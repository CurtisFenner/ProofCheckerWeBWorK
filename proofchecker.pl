# cwfenner@umich.edu
# 6 April 2016
# Based on
# https://github.com/openwebwork/pg/blob/master/macros/parserMultiAnswer.pl

# An answer-checker for proof questions.

=head1 NAME

proofchecker.pl - Check a proof-style answer.

=head1 DESCRIPTION

Lets you ask for a formal proof of something.

$ac = ProofChecker();

=cut

loadMacros("MathObjects.pl"); # ?

###########################################################

package ProofChecker; # define proof checker type

our $answerPrefix = "proofChecker_"; # answer rule prefix
our $counter = 0;

=head1 CONSTRUCTOR
	MultiAnswer();
=cut

# Define a constructor for this class
sub new {
	my $self = shift;
	my $targetStr = shift;
	my $class = ref($self) || $self; # ??
	my ($target, $err) = _parse($targetStr);
	if (!defined($target)) {
		main::TEXT("TARGET ERROR: $err");
	}
	return bless {
		'_blank_num' => 0,
		'num_blanks' => 5,
		'axioms' => {
			'given' => { # a special rule that students can't use
				name => 'Given',
				depends => [],
				test => sub {
					return 0;
				},
			},
		},
		'target' => $target,
		'givens' => [],
	}, $class;
}

# add axiom to proof checker
# an Axiom has a
# name (str)
# test (sub())
sub axiom {
	my $self = shift;
	my $rule = shift;
	$self -> {'axioms'} -> {_normalize_reason($rule -> {'name'})} = $rule;
}

# add a given statement to the proof checker
sub given {
	my $self = shift;
	my $exp = shift;
	my ($statement, $err) = _parse($exp);
	if (!defined($statement)) {
		main::TEXT("GIVEN ERROR: $err");
	}
	my $givens = $self -> {'givens'};
	push @$givens, $statement;
}

################################################################################
# Parses a string into an expression.
sub _parse {
	my $str = shift;
	if (index($str, "'") >= 0 || index($str, "\\") >= 0) {
		return (undef, "cannot contain single quote or backslash");
	}
	my ($obj, $err) = main::PG_restricted_eval("ProofFormula('$str')");
	return ($obj, $err);
}

################################################################################

# Shows an answer blank on the problem page. It returns the ID of that answer
# blank, for use later in checking.
# $id = $pc -> _show_blank($width);
sub _show_blank {
	my $self = shift;
	my $width = shift;
	$name = $answerPrefix . $counter;
	$counter++;
	if ($self -> {'_blank_num'} > 0) {
		# this is not the first blank
		main::TEXT(main::NAMED_ANS_RULE_EXTENSION($name, $width));
	} else {
		# this is the first blank
		main::TEXT(main::NAMED_ANS_RULE($name, $width));
		$self -> {'_primary_blank'} = $name;
	}
	$self->{'_blank_num'}++;
	return $name;
}

# Get the value of a blank created with _show_blank.
# $value = $pc -> _get_blank($id);
# The result is a string (the string entered by the student, maybe with some
# basic santization applied by HTML form)
sub _get_blank {
	my $self = shift;
	my $name = shift;
	my $inputs = $main::inputs_ref;
	return $inputs -> {$name};
}


sub _in_scope {
	my $line = shift;
	my $references = shift;
	# my $proof = shift;
	return $line > $references && $references >= 1;
}

# my ($messages, $correct, $summary) = $pc -> _check($statements, $reasons);
sub _check {
	my $self = shift;
	my $statements = shift;
	my $reasons = shift;
	my $correct = 1;
	#
	my @messages = ();
	for (my $i = 0; $i < $self->{num_blanks}; $i++) {
		my $line = $i + 1;
		#
		if (defined($statements -> [$i])) {
			my $wasCorrect = $correct;
			$correct = 0;
			# Check this statement.
			$axiom = $self -> {'axioms'} -> {$reasons->[$i][0]};
			if (!defined($axiom)) {
				$messages[$i] = "no such rule '" . $reasons->[$i][0] . "'.";
				next;
			}
			my @dep = ();
			my $depNamesr = $axiom -> {'depends'};
			my @depNames = @$depNamesr;
			for (my $j = 1; $j <= scalar @depNames; $j++) {
				my $k = $reasons->[$i]->[$j];
				if (!defined($k) || !$k) {
					$messages[$i] = "'$k' is not a valid statement number (needed for " . $depNames[$j-1] . ")";
				} else {
					if (!_in_scope($line, $k)) {
						$messages[$i] = "statement $k is not in scope";
					} else {
						if (defined($statements -> [$k-1])) {
							push @dep, $statements -> [$k-1];
						} else {
							$messages[$i] = "statement $k is malformed";
						}
					}
				}
			}
			if (!$messages[$i]) {
				$messages[$i] = $axiom -> {'test'}($statements -> [$i], @dep );
			}
			if (!$messages[$i]) {
				$correct = $wasCorrect;
			}
		}
	}
	#
	$summary = "Analyzed:";
	if ($correct) {
		$summary = "All justifications are valid.";
	}
	return (\@messages, $correct, $summary);
}

sub _normalize_reason {
	my $str = shift;
	if (!defined($str)) {
		return "";
	}
	$str =~ s/\s+//g; # remove all whitespace
	return lc($str);
}

sub show {
	my $self = shift;
	# A proof is a sequence of statements and the justifications of those
	# statements.
	main::TEXT("You can use the following axioms/logical rules:" . $main::BR);
	$axioms = $self -> {'axioms'};
	foreach my $key (keys %$axioms) {
		if ($key ne 'given') {
			main::TEXT($axioms -> {$key} -> {'name'} . " ($key)". $main::BR);
		}
	}
	# Show answer blanks:
	# [Show givens]
	my $givens = $self -> {'givens'};
	for (my $i = 0; $i < scalar @$givens; $i++) {
		main::TEXT($i+1 . ".  " );
		main::TEXT( "" . ($givens->[$i]) );
		main::TEXT(" (given)" . $main::BR);
	}
	my $offset = scalar @$givens;
	my @statementBlanks, @reasonBlanks, @dependsBlanks;
	for (my $i = 0; $i < $self->{'num_blanks'}; $i++) {
		main::TEXT($i+1+$offset . ". ");
		push @statementBlanks, $self->_show_blank(20);
		main::TEXT(" by ");
		push @reasonBlanks, $self->_show_blank(20);
		main::TEXT(" on ");
		my $d1 = $self -> _show_blank(1);
		my $d2 = $self -> _show_blank(1);
		my $d3 = $self -> _show_blank(1);
		push @dependsBlanks, [$d1, $d2, $d3];
		main::TEXT($main::BR);
	}
	# Create answer checking subroutine:
	$evaluator = sub {
		my $text = "";
		my $latex = "";
		my @statements = ();
		my %problems = (); # Which statements had problems
		my @reasons = ();
		# Add 'givens' from instructor
		my $i = 0;
		for ($i = 0; $i < scalar @$givens; $i++) {
			push @statements, $givens -> [$i];
			push @reasons, ['given'];
		}
		# Get a list of statements (as MathObjects)
		foreach my $statementBlank (@statementBlanks) {
			my $exp = $self -> _get_blank($statementBlank);
			$statements[$i] = undef;
			if ($exp) {
				$text .= $exp;
				my ($f, $err) = _parse($exp);
				if (!defined($f)) {
					$problems{$i} = "syntax error: $err";
				} else {
					#$f = Value::makeValue($exp, context=> main::Context());
					$statements[$i] = $f;
					$latex .= "\\text{ " . $f . " }"
				}
			} else {
				$problems{$i} = "";
			}
			$text .= "\n";
			$latex .= "\n";
			$i++;
		}
		# Get a list of reasons;
		for (my $i = 0; $i < scalar @reasonBlanks; $i++) {
			$reason = _normalize_reason($self -> _get_blank($reasonBlanks[$i]));
			if ($reason eq 'given') {
				$problems{$i + $offset} = "student cannot use 'given' as justification"
			}
			push @reasons, [
				$reason,
				int($self -> _get_blank($dependsBlanks[$i]->[0]) || 0),
				int($self -> _get_blank($dependsBlanks[$i]->[1]) || 0),
				int($self -> _get_blank($dependsBlanks[$i]->[2]) || 0),
			];
		}
		my ($messages, $correct, $summary) = $self -> _check(\@statements, \@reasons);
		for (my $i = 0; $i < $self -> {num_blanks}; $i++) {
			my $p = $problems{$i + $offset} || $messages -> [$i + $offset];
			if ($p) {
				$summary .= $main::BR . ($i + $offset + 1) . '. ' . $p;
			}
		}
		my $proved = 0;
		for (my $i = 0; $i < $self -> {'num_blanks'}; $i++) {
			if ( $self -> {'target'} -> Same($statements[$i]) ) {
				$proved = 1;
			}
		}
		if (!$proved) {
			$summary .= $main::BR . "You have not yet concluded " . ($self -> {'target'});
		}
		my $x = new AnswerHash;
			#a hash containing the results of checking this answer
		$x -> {'correct_ans'} = ' ';
			# (shown as "Correct Answer" after homework closes)
		$x -> {'student_ans'} = ' ';
			# what the student gave
		$x -> {'original_student_ans'} = ' ';
			# what the student gave, before any cleanup/fiddling
		$x -> {'ans_message'} = $summary;
			# the string the student entered
		$x -> {'preview_text_string'} = $text; # <-- ???
		$x -> {'preview_latex_string'} = $latex;
			# the preview text shown in the table when checking/saving answers
		$x -> {'score'} = $correct && $proved;
			# the score for the problem (0 is 0, 1 is 100%)
		return $x;
	};
	# Record answer checker with WeBWorK:
	main::LABELED_ANS($self -> {'_primary_blank'}, $evaluator); # <-- the checker for the first ans_rule() is $evaluator
}

################################################################################

return 1; # signify that proofchecerk.pl loaded correctly

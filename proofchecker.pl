# cwfenner@umich.edu
# 6 April 2016
# Based on
# https://github.com/openwebwork/pg/blob/master/macros/parserMultiAnswer.pl

# An answer-checker for proof questions.

=head1 NAME

proofchecker.pl - Check a proof-style answer.

=head1 DESCRIPTION

Lets you ask for a formal proof of something.

$ac = ProofChecker('target statement as string');
$ac -> given('given hypothesis as string');

$ac -> show();

=cut

loadMacros("MathObjects.pl"); # ?

###########################################################

package ProofChecker; # define proof checker type

our $answerPrefix = "proofChecker_"; # answer rule prefix
our $counter = 0;

=head1 CONSTRUCTOR
	ProofChecker('target statement as string');
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
				assumption => 1, # this reason is an assumption. affects universal elimination
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

# TODO: make this work with subproofs
sub _in_scope {
	my $line = shift;
	my $references = shift;
	# my $proof = shift;
	return $line > $references && $references >= 1;
}

sub _collect_arguments {
	my $row = shift; # row number (1 indexed -- for human)
	my $reason = shift; # [<reason name>, <line 1>, <line 2>, ..., <line n>]
	my $argumentNames = shift; #[<arg-1 name>, ..., <arg-n name>]
	my $statements = shift;

	my @dep = ();
	for (my $j = 0; $j < scalar @$argumentNames; $j++) {
		my $line = $reason->[$j+1];
		my $name = $argumentNames->[$j];
		if (!defined($line) || !$line) {
			return {problem => $name . " didn't get a valid statement number"};
		}
		my $index = $line - 1;
		if ($index < 0 || $index >= $row - 1) {
			return {problem => $line . " is not in the valid range of statement numbers for row " . $row};
		}
		if (! $statements -> [$index] -> {'inScope'}) {
			return {problem => "line $line is no longer in scope and can't be referenced from row $row"};
		}
		if (! defined($statements -> [$index])) {
			return {problem => "statement $line is invalid; fix it first"};
		}
		push @dep, $statements -> [$index];
	}

	return {arguments => \@dep, problem => 0};
}

# Check the proof for validity. It returns information about what is wrong
# Does NOT check that the proof is for what is needed.
# my ($messages, $correct, $summary) = $pc -> _check($statements, $reasons);
sub _check {
	my $self = shift;
	my $statements = shift;
	my $reasons = shift;
	my $correct = 1;
	#
	my @messages = ();
	for (my $i = 0; $i < $self->{num_blanks}; $i++) {
		# The human-readable line numbering begins at 1 instead of 0
		my $line = $i + 1;

		# Statement on line $line can be checked
		# (it's not defined if there was a syntax # error or some other problem)
		if (defined($statements -> [$i])) {
			# Check this statement.
			$axiom = $self -> {'axioms'} -> {$reasons->[$i][0]};
			if (!defined($axiom)) {
				$correct = 0;
				$messages[$i] = "no such rule '" . $reasons->[$i][0] . "'.";
				next;
			}

			# Collect the required expressions that a justification rule
			# can refer to.
			# This process can produce problem-messages
			# (if the referred to statements are out of scope or malformed)
			my $deps = _collect_arguments($line, $reasons->[$i], $axiom -> {'depends'}, $statements);

			if ($deps -> {'problem'}) {
				# An error was produced while collecting the arguments
				$correct = 0;
				$messages[$i] = $deps -> {'problem'};
			} else {
				# Expressions were collected successfully, so the rule can be tested
				$args = $deps -> {'arguments'};
				$messages[$i] = $axiom -> {'test'}($statements -> [$i], @$args);
			}

			# TODO: make scopes that can be closed
			$statements->[$i]->{'inScope'} = 1;
			$statements->[$i]->{'assumption'} = $axiom -> {'assumption'};
		}
	}
	#
	$summary = "Analyzed:";
	if ($correct) {
		$summary = "All justifications are valid.";
	} else {
		# (@messages are shown after $summary)
	}
	return (\@messages, $correct, $summary);
}

# "Normalize" reasons, which are entered as text, to make them
# tolerant of capitalization and whitespace
sub _normalize_reason {
	my $str = shift;
	if (!defined($str)) {
		return "";
	}
	$str =~ s/\s+//g; # remove all whitespace
	return lc($str);
}

# Render this ProofChecker object as input boxes in a problem
sub show {
	my $self = shift;

	# A proof is a sequence of statements and the justifications of those
	# statements.

	# Declare the usable logical deduction rules to the student
	# (since the current interface requires students type the
	# exact names, this is very necessary)
	main::TEXT("You can use the following axioms/logical rules:" . $main::BR);
	$axioms = $self -> {'axioms'};
	foreach my $key (keys %$axioms) {
		if ($key ne 'given') {
			main::TEXT($axioms -> {$key} -> {'name'} . " ($key)". $main::BR);
		}
	}

	# Show givens lines
	my $givens = $self -> {'givens'};
	for (my $i = 0; $i < scalar @$givens; $i++) {
		main::TEXT($i+1 . ".  " );
		main::TEXT( "" . ($givens->[$i]) );
		main::TEXT(" (given)" . $main::BR);
	}

	# Show answer blanks:
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
					$latex .= "{" . $f->TeX() . "}"
				}
			} else {
				$problems{$i} = "";
			}
			$text .= "\n";
			$latex .= "\n";
			$i++;
		}

		# Validate the names of the justifications
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

		# _check() this proof, and combine any problems/error-messages into the summary
		my ($messages, $correct, $summary) = $self -> _check(\@statements, \@reasons);
		for (my $i = 0; $i < $self -> {num_blanks}; $i++) {
			my $p = $problems{$i + $offset} || $messages -> [$i + $offset];
			if ($p) {
				$summary .= $main::BR . ($i + $offset + 1) . '. ' . $p;
			}
		}

		# Check that the correct thing was proved by the student
		my $proved = 0;
		for (my $i = 0; $i < $self -> {'num_blanks'}; $i++) {
			if ( $self -> {'target'} -> Same($statements[$i]) ) {
				$proved = 1;
			}
		}
		if (!$proved) {
			$summary .= $main::BR . "You have not yet concluded " . ($self -> {'target'});
		}

		# construct a hash containing the results of checking this answer
		# (used internally by WeBWorK)
		my $x = new AnswerHash;

		# (shown as "Correct Answer" after homework closes)
		# TODO: be able to provide this
		$x -> {'correct_ans'} = ' ';

		# what the student gave
		# TODO: figure out what this is used for, and populate this
		$x -> {'student_ans'} = ' ';

		# what the student gave, before any cleanup/fiddling
		$x -> {'original_student_ans'} = ' ';

		# the string the student entered
		$x -> {'ans_message'} = $summary;

		$x -> {'preview_text_string'} = $text; # <-- ???

		# the preview text shown in the table when checking/saving answers
		$x -> {'preview_latex_string'} = $latex;

		# the score for the problem (0 is 0, 1 is 100%)
		$x -> {'score'} = $correct && $proved;
		return $x;
	};
	# Record answer checker with WeBWorK:
	main::LABELED_ANS($self -> {'_primary_blank'}, $evaluator); # <-- the checker for the first ans_rule() is $evaluator
}

################################################################################

return 1; # signify that proofchecerk.pl loaded correctly

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

# computes a similarity (between 0 and 1) of two strings
sub _string_similarity {
	my $a = shift;
	my $b = shift;

	my %M = ();
	for (my $i = 0; $i <= length($a); $i++) {
		for (my $j = 0; $j <= length($b); $j++) {
			my $k = $i . "," . $j;
			if ($i == 0 || $j == 0) {
				$M{$k} = 0;
			} else {
				if (substr($a, $i-1, 1) eq substr($b, $j-1, 1)) {
					$M{$k} = 1 + $M{($i-1) . "," . ($j-1)};
				} else {
					my $u = $M{($i-1) . "," . $j};
					my $v = $M{$i . "," . ($j-1)};
					if ($u < $v) {
						$M{$k} = $v;
					} else {
						$M{$k} = $u;
					}
				}
			}
		}
	}
	return $M{length($a) . "," . length($b)} * 2 / (length($a) + length($b));
}

# Define a constructor for this class
sub new {
	my $self = shift;
	my $targetStr = shift;

	my $numBlanks = shift; #optional
	if (!defined($numBlanks)) {
		$numBlanks = 8;
	}

	my $class = ref($self) || $self; # ??
	my ($target, $err) = _parse($targetStr);
	if (!defined($target)) {
		warn("new ProofChecker: when parsing `$targetStr`, got parse error: $err");
	}
	return bless {
		'_blank_num' => 0,
		'num_blanks' => $numBlanks,
		'axioms' => {
			'given' => { # a special rule that students can't use
				name => 'Given',
				depends => [],
				test => sub {
					return 0;
				},
				assumption => 1, # this reason is an assumption. affects universal elimination
			},
			'conclude' => {
				name => 'Conclude',
				conclusion => 1,
				depends => [],
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

	# Argument validation
	if (ref($rule) ne "HASH") {
		warn("`ProofChecker -> axiom(rule)` expects `rule` to be a hash-reference");
	}
	if (!defined($rule -> {'name'})) {
		warn('rule -> {name} should be a string');
	}
	if (ref($rule -> {'depends'}) ne 'ARRAY') {
		warn('rule -> {depends} should be an array-reference');
	}
	my $hasOpen = ref($rule -> {'open'}) eq 'CODE';
	my $hasClose = ref($rule -> {'close'}) eq 'CODE';
	my $hasTest = ref($rule -> {'test'}) eq 'CODE';
	if ($hasTest && $hasOpen || $hasTest && $hasClose) {
		warn("rule should specify a `test` OR a `open`+`close` subroutine(s), not both");
	} elsif ($hasTest) {
	} elsif ($hasOpen && $hasClose) {
	} else {
		warn("rule " . $rule->{name} . " must specify a `test` or a `open`+`close` subroutine(s)");
	}

	$self -> {'axioms'} -> {_normalize_reason($rule -> {'name'})} = $rule;
}

# add a given statement to the proof checker
sub given {
	my $self = shift;
	my $exp = shift;

	if (ref($exp)) {
		warn("`ProofChecker->given(expr)` expects `expr` to be a string, not a reference");
	}

	my ($statement, $err) = _parse($exp);
	if (!defined($statement)) {
		warn("ProofChecker -> given('$exp') caused parse error: $err");
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

my $ALPHA = "ABCDEFG";

sub _collect_arguments {
	my $row = shift; # row number (1 indexed -- for human)
	my $reason = shift; # [<reason name>, <line 1>, <line 2>, ..., <line n>]
	my $argumentNames = shift; #[<arg-1 name>, ..., <arg-n name>]
	my $statements = shift;

	my @dep = ();
	for (my $j = 0; $j < scalar @$argumentNames; $j++) {
		my $line = $reason->[$j+1];
		my $name = $argumentNames->[$j];

		my @thoseInScope = ();
		for (my $k = 0; $k < scalar @$statements; $k++) {
			if (defined($statements->[$k]) && $statements->[$k] -> {'inScope'}) {
				push @thoseInScope, $k+1;
			}
		}
		my $thoseInScope = "No statements";
		if (scalar @thoseInScope > 1) {
			my $last = pop @thoseInScope;
			$thoseInScope = "Statements " . join(', ', @thoseInScope) . " and $last";
		} elsif (scalar @thoseInScope == 1) {
			$thoseInScope = "Statement " . $thoseInScope[0];
		}

		if (!defined($line) || !$line) {
			return {
				problem =>
				"You left column " . substr($ALPHA, $j, 1) . " blank. "
				. "You need to specify which line number of the " . $name . " that you're referring to. $thoseInScope are in scope at this point."
			};
		}
		my $index = $line - 1;
		if ($index < 0 || $index >= $row - 1) {
			return {problem => $line . " is not in the scope of line " . $row . ". $thoseInScope are in scope at this point."};
		}
		if (! $statements -> [$index] -> {'inScope'}) {
			return {problem => "line $line is no longer in scope and can't be referenced from row $row. $thoseInScope are in scope at this point."};
		}
		if (! defined($statements -> [$index])) {
			return {problem => "statement $line is invalid; fix it before referring to it."};
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
	my @opens = ();
	my @openData = ();
	my @messages = ();
	for (my $i = 0; $i < scalar @{$statements}; $i++) {
		# The human-readable line numbering begins at 1 instead of 0
		my $line = $i + 1;

		# Statement on line $line can be checked
		# (it's not defined if there was a syntax # error or some other problem)
		if (defined($statements -> [$i])) {
			# Check this statement.
			$axiom = $self -> {'axioms'} -> {$reasons->[$i][0]};
			if (!defined($axiom)) {
				$correct = 0;
				if ($reasons->[$i][0]) {
					my $got = $reasons->[$i][0];
					my $best = "";
					foreach my $key (keys(%{$self->{axioms}})) {
						if (_string_similarity($key, $got) > _string_similarity($key, $best)) {
							$best = $key;
						}
					}
					# Output message indicating invalid rule
					$messages[$i] = "There isn't a logical rule called '" . $got  . "' available in this problem.";
					if ($best) {
						$messages[$i] .= " Did you mean '" . $self->{'axioms'}->{$best}->{'name'} . "'?";
					}
				} else {
					$messages[$i] = "The justfication for line $line is blank. Write a justification.";
				}
				next;
			}

			# Collect the required expressions that a justification rule
			# can refer to.
			# This process can produce problem-messages
			# (if the referred to statements are out of scope or malformed)
			my $deps = _collect_arguments($line, $reasons->[$i], $axiom -> {'depends'}, $statements);

			if ($deps -> {'problem'}) {
				# An error was produced while collecting the arguments
				$messages[$i] = $deps -> {'problem'};
			} else {
				# Expressions were collected successfully, so the rule can be tested
				$args = $deps -> {'arguments'};

				my @inScope;
				for (my $j = 0; $j < $i; $j++) {
					if (defined($statements -> [$j]) && $statements -> [$j] -> {'inScope'}) {
						push @inScope, $statements -> [$j];
					}
				}
				# Check using the axiom (conclusion | supposition | normal)
				if ($axiom -> {'conclusion'}) {
					# special: conclusion of sub-proof
					if (scalar @openData == 0) {
						$messages[$i] = "You cannot conclude anything here; no sub-proof is open at line $line";
					} else {
						my $last = pop @openData;
						if ($last == 0) {
							$messages[$i] = "(cannot check conclusion because sub-proof was opened incorrectly)";
						} else {
							$messages[$i] = $last -> {'opener'} -> {'close'}($statements -> [$i], $last, \@inScope);
						}

						# close the open sub-proof
						my $until = pop @opens;
						for (my $j = $until; $j < $i; $j++) {
							if (defined($statements -> [$j])) {
								$statements->[$j]->{'inScope'} = 0;
							}
						}
					}
				} elsif ($axiom -> {'open'}) {
					# sub-proof axiom
					push @opens, $i;
					my $result = $axiom -> {'open'}($statements -> [$i], @$args, \@inScope);
					if (ref($result)) {
						# successful! save result for reference by conclusion
						$messages[$i] = 0;
						$result -> {'opener'} = $axiom;
						push @openData, $result;
					} else {
						# failure (error message)
						$messages[$i] = $result;
						push @openData, 0;
					}
				} else {
					# regular axiom
					$messages[$i] = $axiom -> {'test'}($statements -> [$i], @$args, \@inScope);
				}
			}
			if ($messages[$i]) {
				$correct = 0;
			}

			# TODO: make scopes that can be closed
			$statements->[$i]->{'inScope'} = 1;
			$statements->[$i]->{'assumption'} = $axiom -> {'open'} || $axiom -> {'assumption'};
			$statements->[$i] -> {'indent'} = scalar @opens;
		}
	}
	#
	$summary = "Analyzed:";
	if (scalar @opens) {
		my $lastOpen = $opens[scalar @opens - 1] + 1;
		$summary = "You didn't close the sub-proof that was opened on line " . $lastOpen . ";";
	} elsif ($correct) {
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

	# The number of argument columns to output
	my $cols = 0;

	# A proof is a sequence of statements and the justifications of those
	# statements.

	# Declare the usable logical deduction rules to the student
	# (since the current interface requires students type the
	# exact names, this is very necessary)
	main::TEXT('Using the provided statements and deduction rules, prove that \(' . $self->{'target'}->TeX() . '\).' . $main::BR);
	main::TEXT("You can use the following axioms/logical rules:<ul>");
	$axioms = $self -> {'axioms'};
	foreach my $key (keys %$axioms) {
		if ($key ne 'given') {
			main::TEXT("<li>" . $axioms -> {$key} -> {'name'});
			my @dep = @{$axioms -> {$key} -> {'depends'}};
			if (scalar @dep > $cols) {
				$cols = scalar @dep;
			}
			if (scalar @dep) {
				for (my $i = 0; $i < scalar @dep; $i++) {
					$dep[$i] = substr($ALPHA, $i, 1) . ": " . $dep[$i];
				}
				main::TEXT("(" . join(", ", @dep) . ")");
			}
			main::TEXT("</li>\n");
		}
	}
	main::TEXT("</ul>\n\n");

	# Output the proof table
	main::TEXT("<table>");
	main::TEXT("<tr>");
	main::TEXT("<th>#</th> <th>Statement</th> <th></th> <th>Justification</th><th></th>");
	for (my $c = 0; $c < $cols; $c++) {
		main::TEXT("<th>" . substr($ALPHA, $c, 1) . "</th>");
	}
	main::TEXT("</tr>");

	# Show givens lines
	my $givens = $self -> {'givens'};
	for (my $i = 0; $i < scalar @$givens; $i++) {
		main::TEXT('<tr><th>' . ($i+1) . '.</th>');
		main::TEXT('<td>\(' . $givens->[$i]->TeX() .'\)</td>');
		main::TEXT('<td></td><td>given</td><td></td><td colspan=' . $cols . '></td>');
		main::TEXT('</tr>');
	}

	# Show answer blanks:
	my $offset = scalar @$givens;
	my @statementBlanks, @reasonBlanks, @dependsBlanks;
	for (my $i = 0; $i < $self->{'num_blanks'}; $i++) {
		main::TEXT('<tr><th>' . ($i+1+$offset) . '.</th>');
		main::TEXT('<td>');
		push @statementBlanks, $self->_show_blank(30);
		main::TEXT('</td>');
		main::TEXT('<td>by</td>');
		main::TEXT('<td>');
		push @reasonBlanks, $self->_show_blank(20);
		main::TEXT('</td>');
		main::TEXT('<td>on</td>');
		my @blanks = ();
		for (my $c = 0; $c < $cols; $c++) {
			main::TEXT('<td>');
			my $blank = $self -> _show_blank(1);
			main::TEXT('</td>');
			push @blanks, $blank;
		}
		push @dependsBlanks, \@blanks;
		main::TEXT('</tr>');
	}

	main::TEXT('</table>');

	# Create answer checking subroutine:
	$evaluator = sub {
		my $text = "";
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
				}
			} else {
				$problems{$i} = "";
			}
			$i++;
		}

		# Validate the names of the justifications
		for (my $i = 0; $i < scalar @reasonBlanks; $i++) {
			my $reason = _normalize_reason($self -> _get_blank($reasonBlanks[$i]));
			if ($reason eq 'given') {
				$problems{$i + $offset} = "student cannot use 'given' as justification"
			}
			my @just = ($reason);
			for (my $c = 0; $c < $cols; $c++) {
				push @just, int($self -> _get_blank($dependsBlanks[$i]->[$c]) || 0);
			}
			push @reasons, \@just;
		}

		# _check() this proof, and combine any problems/error-messages into the summary
		my ($messages, $correct, $summary) = $self -> _check(\@statements, \@reasons);
		for (my $i = 0; $i < $self -> {num_blanks}; $i++) {
			my $p = $problems{$i + $offset} || $messages -> [$i + $offset];
			if ($p) {
				$summary .= $main::BR . ($i + $offset + 1) . '. ' . $p;
			}
		}

		# Draw latex proof table
		my $latex = '\begin{array}{r|l}';
		for (my $i = 0; $i < scalar @statements; $i++) {
			my $f = $statements[$i];
			if (defined($f) && defined($f -> {'indent'})) {
				my $depth = $f -> {'indent'};
				my $indent = " " . ("\\qquad" x (2*$depth)) . " ";
				$latex .= ($i+1) . " & " . $indent . " {" . $f->TeX() . "}"
			}
			$text .= "\n";
			$latex .= " \\\\ \n";
			if (defined($f) && defined($f -> {'indent'})) {
				if ($f -> {'assumption'}) {
					$latex .= " \\hline ";
				}
			}
		}
		$latex .= '\end{array}' . "\n";

		# Check that the correct thing was proved by the student
		my $proved = 0;
		for (my $i = 0; $i < $self -> {'num_blanks'}; $i++) {
			if ( $self -> {'target'} -> Same($statements[$i]) ) {
				$proved = 1;
			}
		}
		if (!$proved) {
			$summary .= $main::BR . "You have not yet concluded " . '\(' . ($self -> {'target'})->TeX() . '\)';
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

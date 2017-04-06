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
loadMacros("dropdown.pl");

###########################################################

package ProofChecker; # define proof checker type

our $PROOF_ANSWER_PREFIX = "proofChecker_"; # answer rule prefix
our $UNIQUE_COUNTER = 0;

=head1 CONSTRUCTOR
	ProofChecker('target statement as string');
=cut

# escape user-input to make appear as intended when output in TEXT
sub escapeHTMLSpecial {
	# TODO: replace this with
	# https://github.com/openwebwork/pg/blob/82d00b0f68e33d32b9c5f2bb4216a00be23dd99d/lib/PGcore.pm
	# encode_pg_and_html
	my $arg = shift;
	$arg =~ s/&/&amp;/g;
	$arg =~ s/</&lt;/g;
	$arg =~ s/>/&gt;/g;
	return $arg;
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
	my $instance = bless {
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
		'givensText' => [],
		'hints' => {},
	}, $class;

	# Fix the last line of the proof
	$instance->hint($numBlanks, $target->Tostr());

	return $instance;
}

# set a "hint" for the given line
# line is 1, 2, 3, 4, ... (NOT zero-indexed)
# lines DO NOT include "given" lines. (confusing... sorry... may fix)
# lines MAY skip, leaving space for the student
sub hint {
	my $self = shift;
	my $line = shift;
	my $expression = shift;

	# Check for any instructor mistakes
	if ($line <= 0) {
		return warn("ProofChecker->hint() expects positive line numbers, but $line was passed");
	}
	$line--;
	if (defined($self->{'hints'}->{$line})) {
		warn("a hint has already been given for $line");
	}

	# Record the hint
	my ($f, $err) = _parse($expression);
	if (!defined($f)) {
		return warn("ProofChecker->hint($line, '$expression') got parse error: $err");
	}

	$self->{'hints'}->{$line} = $f;
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
	my $givensText = $self -> {'givensText'};
	push @$givens, $statement;
	push @$givensText, $exp;
}

################################################################################
# Parses a string into an expression.
sub _parse {
	my $str = shift;
	if (index($str, "'") >= 0 || index($str, "\\") >= 0) {
		return (undef, "cannot contain single quote or backslash");
	}
	my ($obj, $err) = ProofFormula::MAKE($str);
	return ($obj, $err);
}

################################################################################

# Shows an answer blank on the problem page. It returns the ID of that answer
# blank, for use later in checking.
# $id = $pc -> _show_blank($width);
sub _show_blank {
	my $self = shift;
	my $width = shift;

	my $name = $PROOF_ANSWER_PREFIX . $UNIQUE_COUNTER;
	$UNIQUE_COUNTER++;

	if ($self -> {'_blank_num'} > 0) {
		# this is not the first blank
		main::TEXT(main::NAMED_ANS_RULE_EXTENSION($name, $width));
	} else {
		# this is the first blank
		main::TEXT(main::NAMED_ANS_RULE($name, $width));
		$self -> {'_primary_blank'} = $name;
	}

	# indicate the "first" blank (the "real" one) has already been made
	$self->{'_blank_num'}++;
	return $name;
}

sub _show_fixed {
	my $self = shift;
	my $col = shift;
	my $value = shift;

	my $name = $PROOF_ANSWER_PREFIX . $UNIQUE_COUNTER;
	$UNIQUE_COUNTER++;

	# INLINED FROM NAMED_ANS_RULE_EXTENSION FROM HERE:
	# https://github.com/openwebwork/pg/blob/47583ef5bd22005916db8a050a4dcaf1c6d3d643/macros/PGbasicmacros.pl

	my $label = main::generate_aria_label($name);

	# Sanitize the value to render as provided *text*
	$value = main::encode_pg_and_html($value);

	# TODO: deal with the fact that this is HTML only
	main::TEXT(qq!<INPUT readonly TYPE=TEXT CLASS="codeshard" SIZE=$col NAME = "$name" id="$name" aria-label="$label" VALUE = "$value">!);

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
	# return the result
	my $out = $inputs -> {$name};
	if (!defined($out)) {
		return "";
	}
	return $out;
}

my @ALPHA = ("&#9398;", "&#9399;", "&#9400;", "&#9401;", "&#9402;", "&#9403;");

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
		my $inScopeMessage = "No statements";
		if (scalar @thoseInScope > 1) {
			my $last = pop @thoseInScope;
			$inScopeMessage = "Statement numbers " . join(', ', @thoseInScope) . " or $last";
		} elsif (scalar @thoseInScope == 1) {
			$inScopeMessage = "Statement number " . $thoseInScope[0];
		}
		$inScopeMessage = "$inScopeMessage might be used to fill the inputs in line $row.";

		if (!defined($line) || !$line) {
			return {
				problem =>
				"You left column " . $ALPHA[$j] . " blank.<br>"
				. "You need to specify in column " . $ALPHA[$j] . " the line number of the $name that you want to refer to.<br>$inScopeMessage"
			};
		}
		my $index = $line - 1;
		if ($index < 0 || $index >= $row - 1) {
			return {problem => $line . " is not in the scope of line $row.<br>$inScopeMessage"};
		}
		if (! $statements -> [$index] -> {'inScope'}) {
			# TODO: update message for "in scope" lines that are just not justified properly
			return {problem => "line $line is not in scope; it can't be referenced from row $row.<br>$inScopeMessage"};
		}
		if (! defined($statements -> [$index])) {
			return {problem => "statement $line is invalid<br>.Fix line $line before referring to it."};
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
					# Output message indicating invalid rule
					$messages[$i] = "There isn't a logical rule called '" . $got  . "' available in this problem.";
				} else {
					$messages[$i] = "The justfication for line $line is blank. Select a justification.";
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
				$statements->[$i]->{'bad_reference'} = 1;
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
						if (!ref($last)) {
							if ($last != 0) {
								warn("the only non-ref that should be returned from successful open is 0");
							}
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

	# Create the final summary
	my $summary = "Problems were found with the following lines:";
	if ($correct) {
		$summary = "All lines so far are justified correctly.";
	}
	if (scalar @opens) {
		my $lastOpen = $opens[scalar @opens - 1] + 1;
		$summary = $summary . "<br><br>You didn't close the sub-proof that was opened on line " . $lastOpen
			. ".<br>Make sure to use 'Conclude sub-proof' to close each sub-proof in order to finish the main proof.";
		$correct = 0;
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
	$axioms = $self -> {'axioms'};
	my @axiomDescriptions = ();
	while (my ($key, $axiom) = each %$axioms) {
		if ($key ne 'given' && $key ne 'conclude') {
			# Update number of columns needed
			my @dep = @{$axiom -> {'depends'}};
			if (scalar @dep > $cols) {
				$cols = scalar @dep;
			}

			# Build the description of the rule
			my $row = "<strong>" . $axiom -> {'name'} . "</strong>";
			if (scalar @dep) {
				for (my $i = 0; $i < scalar @dep; $i++) {
					$dep[$i] = $ALPHA[$i] . ": " . $dep[$i];
				}
				$row .= " (" . join(", ", @dep) . ")";
			}
			if (defined($axiom->{'open'})) {
				$row = "Begin a $row sub-proof";
			}

			push @axiomDescriptions, "<li>$row</li>";
		}
	}
	@axiomDescriptions = main::lex_sort(@axiomDescriptions);

	# Render the description of the available deduction rules
	main::TEXT("<hr>\n");
	main::TEXT("<p><b><a href='http://www-personal.umich.edu/~cwfenner/ProofCheckerWeBWorK/help.html'>"
		. "Click here for an explanation of how to do proof questions on WeBWorK</a></b></p>");
	main::TEXT("<hr>\n");
	main::TEXT('Using the provided statements and deduction rules, prove that \(' . $self->{'target'}->TeX() . '\).' . $main::BR);
	main::TEXT('You do <em>not</em> need to use all of the blanks.' . $main::BR);
	main::TEXT("<details><summary>You can use " . (scalar @axiomDescriptions) . " deduction rules.</summary><ul>");
	main::TEXT(join "", @axiomDescriptions);
	main::TEXT("</ul></details>\n\n");
	main::TEXT("$main::BR $main::BR");

	# Output the proof table
	main::TEXT("<table>");
	main::TEXT("<tr>");
	main::TEXT("<th>#</th> <th>Statement</th> <th></th> <th>Justification</th><th></th>");
	for (my $c = 0; $c < $cols; $c++) {
		main::TEXT("<th>" . $ALPHA[$c] . "</th>");
	}
	main::TEXT("</tr>");

	# Show givens lines
	my $givens = $self -> {'givens'};
	my $givensText = $self -> {'givensText'};
	for (my $i = 0; $i < scalar @$givens; $i++) {
		main::TEXT('<tr><th>' . ($i+1) . '.</th>');

		# Show given statement
		main::TEXT('<td>');
		$self->_show_fixed(30, $givensText->[$i]);
		main::TEXT('</td>');

		# Show given justification
		main::TEXT('<td></td><td>given</td><td></td>');

		# Show blank area for "reference" columns
		main::TEXT('<td colspan=' . $cols . '></td>');
		main::TEXT('</tr>');
	}

	# Show answer blanks:
	my $offset = scalar @$givens;
	my @statementBlanks, @reasonBlanks, @dependsBlanks;
	for (my $i = 0; $i < $self->{'num_blanks'}; $i++) {
		main::TEXT('<tr><th>' . ($i+1+$offset) . '.</th>');
		main::TEXT('<td>');
		if (defined($self->{'hints'}->{$i})) {
			# the statement is a hint from the instructor
			push @statementBlanks, $self->_show_fixed(30, $self->{'hints'}->{$i}->Tostr());
		} else {
			# the statement is blank for the student to use
			push @statementBlanks, $self->_show_blank(30);
		}
		main::TEXT('</td>');
		main::TEXT('<td>by</td>');
		main::TEXT('<td>');

		# Get an alphabetical list of the available deduction rules
		my @axiomNames = ("");
		while (my ($k, $rule) = each %{$self->{'axioms'}}) {
			if ($k ne 'given') {
				push @axiomNames, $rule->{'name'};
			}
		}
		@axiomNames = main::lex_sort(@axiomNames);

		# Create "labels" which are extra-processed
		my @axiomLabels = ("");
		foreach my $name (@axiomNames) {
			while (my ($k, $rule) = each %{$self->{'axioms'}}) {
				if ($rule->{'name'} eq $name) {
					if ($k eq 'conclude') {
						push @axiomLabels, "Conclude sub-proof";
					} elsif (defined($rule->{'open'})) {
						push @axiomLabels, $rule->{'name'} . ' [sub-proof]';
					} else {
						push @axiomLabels, $rule->{'name'};
					}
				}
			}
		}

		# Create and show a dropdown
		my $drop = Dropdown->new(\@axiomLabels, \@axiomNames);
		push @reasonBlanks, $drop->html();

		# End the row with the line-number input boxes
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
	my $evaluator = sub {
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
				# The line was left blank
				# (this is perfectly OK; students can skip lines)
				$problems{$i} = "";
			}
			$i++;
		}

		my $cheating = 0;

		# Validate the names of the justifications
		for (my $i = 0; $i < scalar @reasonBlanks; $i++) {
			my $reason = _normalize_reason($self -> _get_blank($reasonBlanks[$i]));
			if ($reason eq 'given') {
				$problems{$i + $offset} = "You cannot use 'given' as justification!";
				$cheating = 1;
			}
			my @just = ($reason);
			for (my $c = 0; $c < $cols; $c++) {
				my $lineStr = $self -> _get_blank($dependsBlanks[$i]->[$c]);
				$lineStr =~ s/\D+//g;
				push @just, int($lineStr || 0);
			}
			push @reasons, \@just;
		}

		# _check() this proof, and combine any problems/error-messages into the summary
		my ($messages, $correct, $summary) = $self -> _check(\@statements, \@reasons);
		$summary .= "<ol style='text-align:left;'>";
		for (my $i = 0; $i < $self -> {num_blanks}; $i++) {
			my $problem = $problems{$i + $offset} || $messages -> [$i + $offset];
			if ($problem) {
				$summary .= "<li value='" . ($i + $offset + 1) . "'>" . $problem . "</li>";
			}
		}
		$summary .= "</ol>";

		my $BOX_BEGIN = '{\begin{array}{|rl|}\hline' . "\n";
		my $BOX_END = '\hline\end{array}} \\\\ ' . "\n";

		my $previousDepth = 0;
		my $latex = $BOX_BEGIN . "\n";
		for (my $i = 0; $i < scalar @statements; $i++) {
			my $statement = $statements[$i];
			my $underbar = $i+1 == scalar @$givens;

			if (defined($statement) && defined($statement->{'indent'})) {
				if ($statement->{'indent'} > $previousDepth) {
					# This statement begins a subproof
					$previousDepth = $statement->{'indent'};
					# Make a short space above proof box
					$latex .= " \\\\";

					$latex .= ' & ';
					$latex .= $BOX_BEGIN;
					$underbar = 1;
				} elsif ($statement->{'indent'} < $previousDepth) {
					# This statement comes after the end of a subproof
					$previousDepth = $statement->{'indent'};
					$latex .= $BOX_END . " \\\\ \\\\ \n";
				}
				$latex .= ($i+1) . '. & ' . $statement->TeX();

				if ($statement->{'bad_reference'}) {
					$latex .= "{}_{\\textit{ bad ref. }}";
				}
			}
			# Include a blank line
			$latex .= "\\\\\n";
			if ($underbar) {
				$latex .= " \\hline \n";
			}
		}
		while ($previousDepth > 0) {
			$latex .= $BOX_END;
			$previousDepth--;
		}
		$latex .= $BOX_END;

		$latex =~ s/\n+/\n/g;

		# Check that the correct thing was proved by the student
		my $proved = 0;
		for (my $i = 0; $i < scalar @statements; $i++) {
			if ($statements[$i]->{'inScope'} && $self -> {'target'} -> Same($statements[$i])) {
				$proved = 1;
			}
		}
		if (!$proved) {
			$summary .= $main::BR . "You have not yet justified a conclusion of " . '\(' . ($self -> {'target'})->TeX() . '\)';
		}

		#$summary .= "<pre style='text-align:left'> " . main::encode_pg_and_html($latex) . "</pre>";

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
		$x -> {'score'} = $correct && $proved && !$cheating;
		return $x;
	};
	# Record answer checker with WeBWorK:
	main::LABELED_ANS($self -> {'_primary_blank'}, $evaluator); # <-- the checker for the first ans_rule() is $evaluator
}

################################################################################

return 1; # signify that proofchecerk.pl loaded correctly

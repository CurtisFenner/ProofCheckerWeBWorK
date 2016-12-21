

BEGIN_TEXT #between these,
	problem1 \{ ans_rule(); \}

	problem2 \{ ans_rule(); \} # define blanks, in order.
		# (can also be named explicitly with named_ans_rule.)
		# I think ans_rule() uses an internal counter to get unique names.
	# ONLY ONE ans_rule() per pair of \{\}. WHY?
END_TEXT

ANS( checker1 ); # define checker for first blank
ANS( checker2 ); # define checker for first blank
# (somehow a NAMED_ANS also possible to name which blank you care about)

# What type of object is passed to ANS?
	# AnswerEvaluator? AnswerHash?

	$mathv = Compute('9');

	$evaluator = sub {
		$x = new AnswerHash; # <-- a hash containing the results of checking this answer
		$x -> {'correct_ans'} = $mathv; # <-- (shown as "Correct Answer" after homework closes)
		$x -> {'student_ans'} = $mathv; # <-- what the student gave
		$x -> {'original_student_ans'} = $mathv; # <-- what the student gave, before any cleanup/fiddling
		$x -> {'ans_message'} = shift; # <-- the string the student entered
		$x -> {'preview_text_string'} = "preview_text"; # <-- ???
		$x -> {'preview_latex_string'} = "preview_latex"; # <-- the preview text shown in the table when checking/saving answers
		$x -> {'score'} = 0.5; # <-- the score for the problem (0 is 0, 1 is 100%)
		return $x;
	};

	ANS($evaluator); # <-- the checker for the first ans_rule() is $evaluator
# THE ABOVE WORKS AS EXPECTED --------------------------------------------------

# Sources of inspiration:
# draggableproof -- many blanks to one ANS
# FormulaUpToConstant -- patterns for variable names

# format_matrix_HTML
# https://github.com/openwebwork/pg/blob/6f198163908a9d920199d76f9f8b7aa23421977b/lib/Value/AnswerChecker.pm#L461

# ans_matrix (called by public ANS_MATRIX) generates the tables
# https://github.com/openwebwork/pg/blob/6f198163908a9d920199d76f9f8b7aa23421977b/lib/Value/AnswerChecker.pm#L381

#  my $inputs = $self->getPG('$inputs_ref'); has all inputs, Even named ones
# I grab the ones that I'm responsible for, and somehow eat them up so it doesn't whine.

# This is a helpful file to reference:
# https://github.com/openwebwork/pg/blob/master/macros/parserMultiAnswer.pl

# Multiple-blank answer checkers:

	# blanks made. one for each entry. Traditionally, with $obj -> ans_rule()
	# These in turn return main::generate_aria_label($blankid)
	# The first blank is given a more-normal name.
	# NAMED_ANS_RULE(name, col, options) in PGbasicmacros.pl ?
	NAMED_ANS_RULE("proofer" . $i, 40);

	# Multiple blanks...
	# are pulled from $main::inputs_ref -> { ansblankname }

	# This creates a blank without registering it with WebWork:
	NAMED_ANS_RULE_EXTENSION("name", width);
	# This lets me make blanks that won't trigger warnings in multi-part answers

# Create proof checker and Universal Elimination rule:
	$obj = new ProofChecker;

	$obj -> given("(forall, x, (., P, (+, x, 1))   )");

	$obj -> axiom({
		name => 'Universal Elimination',
		depends => ["for all statement"], # the names of statements it depends on
		test => sub {
			my $H = shift; # helpers
			my $line = shift;
			my $forall = shift;
			#
			my $forallPattern = _parse('(forall, @variable, @predicate)');
			my $fam = $H -> Match($forallPattern, $forall);
			if (!$fam) {
				return "not a forall statement";
			}
			my $instancePattern = $H->Substitute($fam -> variable, '@x', $fam -> predicate);
			if (!$H->Match($instancePattern, $line)) {
				return "not a valid instantiation of " . _stringify($forall);
			}
			return 0;
		}
	});

	$obj -> show();

# FormulaUpToConstant replaces the context's Variables parser. The replacement
# adds any variables that have not yet been defined (given that they're
# acceptable constants -- one letter long)

# Look at fraction context for something that tears up the operators


# Important place in source:
# https://github.com/openwebwork/pg/tree/82d00b0f68e33d32b9c5f2bb4216a00be23dd99d/lib/Parser

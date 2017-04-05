package ProofRules;

sub E {
	my $str = shift;
	my ($obj, $err) = main::ProofFormula::MAKE($str);
	if (!defined($obj)) {
		warn("invalid expression '$str' passed to `E` in ProofRules; parse error '$err'");
	}
	return $obj;
}

our %ProofRules = (
########################################################################################################################
	"universal_introduction" => {
		name => 'Create a For-All',
		depends => ["statement about 'free variable'"], # student visible
		test => sub {
			my $line = shift; # ex. line: forall(x, P(x))
			my $freestatement = shift; # ex. freestatement: P(z)
			my $scope_ref = shift;
			my @scope = @$scope_ref;
			#
			my $forallPattern = E('forall(@variable, @predicate)');
			my $fam = $line -> Match($forallPattern);
			if (!$fam) {
				return "this line should be a forall() statement";
			}
			# ex. predicate: P(x). variable: x.
			my $instancePattern = $fam -> {'predicate'} -> Replace( $fam -> {'variable'}, E('@x') );
			my $var = $freestatement -> Match($instancePattern);
			if (!$var) {
				return $freestatement . " cannot be generalized to " . $line;
			}
			# ex. var: z
			# (ii) `var` doesn't appear in the for-all conclusion
			my $cons = $line -> Contains($var->{'x'});
			if ($cons) {
				return $var->{'x'} . " should be eliminated from the generalization " . $line;
			}
			# (i) `var` doesn't occur in an accessible assumption
			foreach my $assumption (@scope) {
				if ($assumption -> {'assumption'}) {
					if ($assumption -> Contains($var->{'x'})) {
						return $var . " is not a free variable since it was introduced in the assumption " . $assumption;
					}
				}
			}
			return 0;
		}
	},
########################################################################################################################
	"existential_elimination" => {
		name => 'Eliminate a There-Exists',
		depends => ["there-exists statement"],
		open => sub {
			# 1) instantiation variable `a` must not appear in any in-scope assumption
			# 2) instantiation variable `a` must not appear in there-exists statement
			my $line = shift; # e.g., P(c)
			my $thereExists = shift; # e.g., exists(x, P(x))
			my $scope_ref = shift;
			my @scope = @$scope_ref;

			my $existsPattern = E('exists(@variable, @predicate)');
			my $em = $thereExists -> Match($existsPattern);
			if (!$em) {
				return "this line should be a there-exists statement";
			}

			my $predicatePattern = $em->{'predicate'} -> Replace($em->{'variable'}, E('@v'));
			my $var = $line -> Match($predicatePattern);
			if (!$var) {
				return $line . " is not an instantiation of " . $thereExists;
			}

			if ($var -> {'v'} -> {'tree'} -> {'type'} ne 'constant') {
				return "you must instantiate to a name, not a complex expression like " . $var -> {'v'} . " with type " . $var->{'v'}->{'tree'}->{'type'};
			}
			if (!($var -> {'v'} -> {'tree'} -> {'value'} =~ /^[a-zA-Z]+$/)) {
				return "you must instantiate to a name, not a number/constant like " . $var -> {'v'};
			}
			if ($thereExists -> Contains($var -> {'v'})) {
				return "the instantiated name " . $var->{'v'} . " must not appear in " . $thereExists;
			}

			foreach my $assumption (@scope) {
				if ($assumption -> {'assumption'}) {
					if ($assumption -> Contains($var->{'v'})) {
						return "You cannot use the name " . $var . " because it is used in assumption " . $assumption;
					}
				}
			}

			# appears OK
			return {
				'var' => $var -> {'v'}
			};
		},
		close => sub {
			# 3) conclusion must not contain instantiation variable `a`
			# (it should have been abstracted into a there-exists)
			my $line = shift; # e.g., exists(s, Q(s))
			my $opening = shift;
			my $scope_ref = shift;
			my @scope = @$scope_ref;

			if ($line -> Contains($opening -> {'var'})) {
				return "The conclusion of an 'eliminate there-exists subproof' must not use the name \$" . $opening->{'var'}->TeX() . "\$ used in the claim.";
			}

			my $top = $scope[(scalar @scope) - 1];
			if (!($top -> Same($line))) {
				return "The conclusion of an 'eliminate there-exists subproof' must have been proven already in the subproof (on the previous line)."
					. "<br>However, \\( " . $line->TeX() . " \\) was not proven in this subproof.";
			}
			return 0;
		},
	},
########################################################################################################################
	"existential_introduction" => {
		name => 'Create a There-Exists',
		depends => ['statement you want to quantify'],
		test => sub {
			my $line = shift; # exists(x, P(x))
			my $stat = shift; # P(c)
			#
			my $existsPattern = E('exists(@variable, @predicate)');
			my $em = $line -> Match($existsPattern);
			if (!$em) {
				return "\\(" . $line->TeX() . "\\) must be a there-exists statement to be deduced from existential-introduction.";
			}
			my $instantiationPattern = $em -> {'predicate'} -> Replace($em -> {'variable'}, E('@v'));
			if (! $stat->Match($instantiationPattern) ) {
				return '\(' . $stat->TeX() . '\) cannot be generalized as \(' . $line->TeX() . '\).<br>'
					. 'To conclude \(' . $line->TeX() . '\), you must use a statement that looks like \(' . $em->{'predicate'}->Replace($em->{'variable'}, E('u'))->TeX() . '\)';
			}
			return 0;
		},
	},
########################################################################################################################
	"universal_elimination" => {
		name => 'Eliminate a For-All',
		depends => ["for-all statement"], # give a student-visible name to the argument of this reason
		test => sub {
			my $line = shift;
			my $forall = shift;
			#
			my $forallPattern = E('forall(@variable, @predicate)');
			my $fam = $forall -> Match($forallPattern);
			if (!$fam) {
				return $forall->Tostr() . " isn't a for-all statement; the 'A' column should indicate a for-all statement";
			}

			my $pattern = $forall;
			my $uniques = "abcdefghijkl";
			while (1) {
				my $hole = E('@' . substr($uniques, 0, 1));
				$uniques = substr($uniques, 1);

				# capture for-all
				my $quantified = $pattern->Match($forallPattern);
				if (!$quantified) {
					# the left side never matched
					return '\(' . $line->TeX() . '\) is not a valid instantiation of \(' . $forall->TeX() . '\)';
				}

				# unwrap one for-all
				$pattern = $quantified->{'predicate'}->Replace($quantified->{'variable'}, $hole);

				my $instanceMatches = $line->Match($pattern);
				if ($instanceMatches) {
					return 0;
				}
			}
			# not reached
		},
	},
########################################################################################################################
	"conjunction_elimination" => {
		name => 'Eliminate an And',
		depends => ["and-statement"],
		test => sub {
			my $line = shift;
			my $and = shift;
			#
			my $andPattern = E('@a & @b');
			my $am = $and -> Match($andPattern);
			if (!$am) {
				return '\(' . $and->TeX() . '\) should be a statement of the form \(a & b\)';
			}
			if ($line -> Same($am -> {'a'}) || $line -> Same($am -> {'b'})) {
				return 0;
			}
			return 'You can only conclude \(' . $am->{'a'}->TeX() . '\) or \(' . $am->{'b'}->TeX() . '\) using conjunction elimination on \(' . $and->TeX() . '\)';
		}
	},
########################################################################################################################
	"conjunction_introduction" => {
		name => 'Create an And',
		depends => ["first statement", "second statement"],
		test => sub {
			my $line = shift;
			my $s1 = shift;
			my $s2 = shift;
			#
			my $andPattern = E('@a & @b');
			my $am = $line -> Match($andPattern);
			if (!$am) {
				return '\(' . $line . '\) should be a statement of the form \(a & b\)';
			}
			if ($s1 -> Same($am -> {'a'}) || $s2 -> Same($am -> {'b'})) {
				return 0;
			}
			if ($s2 -> Same($am -> {'a'}) || $s1 -> Same($am -> {'b'})) {
				return 0;
			}
			return 'You can only conclude the conjunction of \(' . $s1 . '\) and \(' . $s2 . '\) using conjunction introduction.';
		}
	},
########################################################################################################################
	"implication_introduction" => {
		name => 'Suppose to create an Implication',
		depends => [],
		open => sub {
			my $line = shift;

			return $line;
		},
		close => sub {
			my $line = shift;
			my $supposition = shift;
			my $scope_ref = shift;
			my @scope = @$scope_ref;

			my $top = $scope[(scalar @scope) - 1];
			my $pattern = E('@a => @b');
			my $m = $line -> Match($pattern);
			# Validate return
			if (!$m) {
				return 'You can only conclude implications from implication-introduction';
			}
			if (!$m->{'a'}->Same($supposition)) {
				return 'You can only conclude implications of the form \(' . $supposition->TeX() . ' \) => here using implication introduction.';
			}
			if (!$m->{'b'}->Same($top)) {
				return 'Your implication should use the previous statement to condlue \(' . $supposition->TeX() . ' => ' . $top . '\) here.';
			}
			return 0;
		},
	},
########################################################################################################################
	"modus_ponens" => {
		name => 'Modus Ponens',
		depends => ["P => Q statement", "P statement"],
		test => sub {
			my $line = shift;
			my $pimpliesq = shift;
			my $p = shift;
			#
			my $implicationPattern = E('@p => @q');
			my $im = $pimpliesq -> Match($implicationPattern);
			if (!$im) {
				my $output = 'The first argument of modus-ponens should be an implication.<br>However, \(' . $pimpliesq->TeX() . '\) was used.';
				$output .= "<br>HINT: You cannot directly use a for-all or there-exists statement here.";
				$output .= "<br>You should first eliminate the quantifier using Eliminate For-All or Eliminate There-Exists so that a simple implication is left.";
				return $output;
			}
			if (!$im->{'p'}->Same($p)) {
				my $output = '\(' . $p->TeX() . '\) should match the left side of \(' . $pimpliesq->TeX() . '\)';
				$output .= "<br>HINT: You cannot directly use a for-all or there-exists statement here.";
				$output .= "<br>You should first eliminate the quantifier using Eliminate For-All or Eliminate There-Exists so that a simple implication is left.";
				return $output;
			}
			if (!$im->{'q'}->Same($line)) {
				return 'The conclusion \(' . $line->TeX() . '\) should match the right side of \(' . $pimpliesq->TeX() . '\)';
			}
			return 0;
		}
	},
);

return 1;

package ProofRules;

our %ProofRules = (
########################################################################################################################
	"universal_introduction" => {
		name => 'Universal Introduction',
		depends => ["statement about 'free variable'"], # student visible
		test => sub {
			my $line = shift; # ex. line: forall(x, P(x))
			my $freestatement = shift; # ex. freestatement: P(z)
			my $scope_ref = shift;
			my @scope = @$scope_ref;
			#
			my $forallPattern = main::ProofFormula('forall(@variable, @predicate)');
			my $fam = $line -> Match($forallPattern);
			if (!$fam) {
				return "this line should be a forall() statement";
			}
			# ex. predicate: P(x). variable: x.
			my $instancePattern = $fam -> {'predicate'} -> Replace( $fam -> {'variable'}, main::ProofFormula('@x') );
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
		name => 'Existential Elimination',
		depends => ["there-exists statement"],
		open => sub {
			# 1) instantiation variable `a` must not appear in any in-scope assumption
			# 2) instantiation variable `a` must not appear in there-exists statement
			my $line = shift; # e.g., P(c)
			my $thereExists = shift; # e.g., exists(x, P(x))
			my $scope_ref = shift;
			my @scope = @$scope_ref;

			my $existsPattern = main::ProofFormula('exists(@variable, @predicate)');
			my $em = $thereExists -> Match($existsPattern);
			if (!$em) {
				return "this line should be a there-exists statement";
			}

			my $predicatePattern = $em->{'predicate'} -> Replace($em->{'variable'}, main::ProofFormula('@v'));
			my $var = $line -> Match($predicatePattern);
			if (!$var) {
				return $line . " is not an instantiation of " . $thereExists;
			}

			if (!($var -> {'v'} -> {'tree'} -> {'name'})) {
				return "you must instantiate to a name, not a complex expression like " . $var -> {'v'};
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
				return "Conclusion must not use variable " . $opening->{'var'};
			}

			my $top = $scope[(scalar @scope) - 1];
			if (!($top -> Same($line))) {
				return "Conclusion must match previous line";
			}
			return 0;
		},
	},
########################################################################################################################
	"existential_introduction" => {
		name => 'Existential Introduction',
		depends => ['statement'],
		test => sub {
			my $line = shift; # exists(x, P(x))
			my $stat = shift; # P(c)
			#
			my $existsPattern = main::ProofFormula('exists(@variable, @predicate)');
			my $em = $line -> Match($existsPattern);
			if (!$em) {
				return "`" . $line->TeX() . "` must be a there-exists statement to be the conclusion of existential-introduction.";
			}
			my $instantiationPattern = $em -> {'predicate'} -> Replace($em -> {'variable'}, main::ProofFormula('@v'));
			if (! $stat->Match($instantiationPattern) ) {
				return $stat . " cannot be generalized as " . $line;
			}
			return 0;
		},
	},
########################################################################################################################
	"universal_elimination" => {
		name => 'Universal Elimination',
		depends => ["for-all statement"], # give a student-visible name to the argument of this reason
		test => sub {
			my $line = shift;
			my $forall = shift;
			#
			my $forallPattern = main::ProofFormula('forall(@variable, @predicate)');
			my $fam = $forall -> Match($forallPattern);
			if (!$fam) {
				return "not a forall statement";
			}
			my $instancePattern = $fam -> {'predicate'} -> Replace( $fam -> {'variable'}, main::ProofFormula('@x') );
			if (! $line -> Match($instancePattern)) {
				return "not a valid instantiation of " . $forall;
			}
			return 0;
		},
	},
########################################################################################################################
	"conjunction_elimination" => {
		name => 'Conjunction Elimination',
		depends => ["and-statement"],
		test => sub {
			my $line = shift;
			my $and = shift;
			#
			my $andPattern = main::ProofFormula('@a & @b');
			my $am = $and -> Match($andPattern);
			if (!$am) {
				return "`" . $and . "` should be a statement of the form `a & b`";
			}
			if ($line -> Same($am -> {'a'}) || $line -> Same($am -> {'b'})) {
				return 0;
			}
			return "You can only conclude `" . $am->{'a'} . "` or `" . $am->{'b'} . "` using conjunction elimination on `" . $and . "`.";
		}
	},
########################################################################################################################
	"conjunction_introduction" => {
		name => 'Conjunction Introduction',
		depends => ["first statement", "second statement"],
		test => sub {
			my $line = shift;
			my $s1 = shift;
			my $s2 = shift;
			#
			my $andPattern = main::ProofFormula('@a & @b');
			my $am = $line -> Match($andPattern);
			if (!$am) {
				return "`" . $line . "` should be a statement of the form `a & b`";
			}
			if ($s1 -> Same($am -> {'a'}) || $s2 -> Same($am -> {'b'})) {
				return 0;
			}
			if ($s2 -> Same($am -> {'a'}) || $s1 -> Same($am -> {'b'})) {
				return 0;
			}
			return "You can only conclude the conjunction of `" . $s1 . "` and `" . $s2 . "` using conjunction introduction.";
		}
	},
);

return 1;

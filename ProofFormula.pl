# Based on https://raw.githubusercontent.com/openwebwork/pg/master/macros/parserFormulaUpToConstant.pl
# with GPL license:
################################################################################
# WeBWorK Online Homework Delivery System
# Copyright � 2000-2007 The WeBWorK Project, http://openwebwork.sf.net/
# $CVSHeader: pg/macros/parserFormulaUpToConstant.pl,v 1.23 2010/02/08 13:56:09 dpvc Exp $
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of either: (a) the GNU General Public License as published by the
# Free Software Foundation; either version 2, or (at your option) any later
# version, or (b) the "Artistic License" which comes with this package.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.	See either the GNU General Public License or the
# Artistic License for more details.
################################################################################

=head1 NAME
=head1 DESCRIPTION

Formulas, but all (one letter) variables are OK

	$f = ProofFormula("sin(x)+C");

Note that the FormulaUpToConstant object creates its own private
copy of the current Context (so that it can add variables without
affecting the rest of the problem).	You should not notice this
in general, but if you need to access that context, use $f->{context}.
E.g.

	Context($f->{context});

would make the current context the one being used by the
FormulaUpToConstant, while

	$f->{context}->variables->names

would return a list of the variables in the private context.
=cut

loadMacros("MathObjects.pl");

sub _parserProofFormula_init {ProofFormula::Init()}

package ProofFormula;
@ISA = ('Value::Formula');

sub Init {
	main::PG_restricted_eval('sub ProofFormula {ProofFormula->new(@_)}');
}

Init();

sub preprocess {
	my $str = shift;
	if (length($str) <= 1) {
		return $str;
	}
	my $out = substr($str, 0, 1);
	my $prev = $out;
	for (my $i = 1; $i < length($str); $i++) {
		my $c = substr($str, $i, 1);
		if (lc($prev) ne uc($prev)) {
			if ($c eq '(') {
				$out = $out . '$';
			}
		}
		$out = $out . $c;
		if ($c =~ /^\s*$/) {} else {
			$prev = $c;
		}
	}
	return $out;
}

#
#	Create an instance of a ProofFormula.	If no constant
#	is supplied, we add C ourselves.
#
sub new {
	my $self = shift; my $class = ref($self) || $self;
	#
	#	Copy the context (so we can modify it) and
	#	replace the usual Variable object with our own.
	#
	my $context = (Value::isContext($_[0]) ? shift : $self->context)->copy;
	# Suppress most of the error checking done by the built-in context / parser:
	$context->{'parser'}{'Variable'} = 'ProofFormula::Variable';
	# $context->{'parser'}{'Function'} = 'ProofFormula::Function';
	$context -> flags -> set(
		'allowBadOperands' => 1,
		'allowBadFunctionInputs' => 1,
		'reduceConstants' => 0,
		'reduceConstantFunctions' => 0,
	);
	# Allow pattern variables that start with '@'
	my $oldpatterns = $context -> {'_variables'} {'patterns'};
	$context -> {'_variables'}{'patterns'} = {qr/@?[a-zA-Z][a-zA-Z0-9]*/i	=> [5, 'var']};
	# Add function application operator:
	$context ->operators->add(
		'$' => {
			class => 'Parser::BOP::power',
			precedence => 1000,       # very high?
			associativity => 'left',  #  computed left to right
			type => 'bin',            #  binary operator
			string => '$',            #  output string for it
			TeX => '',                #  TeX version
		}
	);
	#
	#	Create a formula from the user's input.
	#
	my @arg = @_;
	$arg[0] = preprocess($arg[0]);
	my $f = main::Formula($context, @arg);
	#
	#	Make a version with adaptive parameters for use in the
	#	comparison later on.	We would like n00*C, but already have $n
	#	copies of C, so remove them.	That way, n00 will be 0 when there
	#	are no C's in the student answer during the adaptive comparison.
	#	(Again, should really check that n00 is not in use already)
	#
	$f->{adapt} = $f;
	return bless $f, $class;
}

################################################################################

sub _same {
	my $self = shift;
	my $other = shift;
	return defined(_match($self, $other, {}));
}

sub _tostr {
	my $self = shift;
	if ($self -> {'name'}) {
		if ($self -> {'hole'}) {
			return '@' . $self->{'name'};
		}
		return $self -> {'name'};
	} elsif ($self -> {'bop'}) {
		return '(' . _tostr($self -> {'lop'}) . ' ' . $self -> {'bop'} . ' ' . _tostr($self -> {'rop'}) . ')';
	} elsif ($self -> {'isConstant'}) {
		return $self -> {'value_string'};
	} elsif ($self -> {'coords'}) {
		my @elements = @{$self -> {'coords'}};
		for (my $i = 0; $i < scalar @elements; $i++) {
			$elements[$i] = _tostr($elements[$i]);
		}
		return "(" . join(", ", @elements) . ")";
	} else {
		main::TEXT( main::pretty_print($self) );
		return undef;
	}
}

sub Tostr {
	my $self = shift;
	return _tostr( $self -> {'tree'} );
}

sub _substitute {
	my $self = shift;
	my $needle = shift;
	my $replacement = shift;
	if (_same($self, $needle)) {
		return $replacement;
	}
	if ($self -> {'name'} || $self -> {'isConstant'}) {
		return $self;
	} elsif ($self -> {'bop'}) {
		return {
			'bop' => $self -> {'bop'},
			'lop' => _substitute($self -> {'lop'}, $needle, $replacement),
			'rop' => _substitute($self -> {'rop'}, $needle, $replacement),
		};
	} else {
		main::TEXT( main::pretty_print($self) );
		return undef;
	}
}

sub _match {
	my $self = shift; # a ProofFormula
	my $pattern = shift; # a ProofFormula
	my $matches = shift;
	#
	#main::TEXT("<hr>");
	#main::TEXT( ($self) . " VERSUS " . ($pattern) );
	#main::TEXT("<hr>");
	#
	if (defined($pattern -> {'hole'})) {
		# match against just a variable
		my $var = $pattern -> {'hole'};
		if ($matches -> {$var}) {
			my $old = $matches -> {$var};
			my $same = _same($self, $old);
			if ($same) {
				return $matches;
			} else {
				return undef; # second time found, did not match
			}
		} else {
			$matches -> {$var} = $self;
			return $matches;
		}
	} elsif (defined($pattern -> {'bop'})) {
		if (!defined($self -> {'bop'})) {
			return undef;
		}
		return _match($self -> {'lop'}, $pattern -> {'lop'}, $matches)
			&& _match($self -> {'rop'}, $pattern -> {'rop'}, $matches);
	} elsif ($pattern -> {'isConstant'}) {
		if ($self -> {'isConstant'} && $self -> {'value'} eq $pattern -> {'value'}) {
			return $matches;
		} else {
			return undef;
		}
	} elsif (defined($pattern -> {'name'})) {
		if (!defined($self -> {'name'})) {
			return undef;
		}
		if ($self -> {'name'} eq $pattern -> {'name'}) {
			return $matches;
		} else {
			return undef;
		}
	} else {
		main::TEXT($main::BR . main::pretty_print($pattern) . $main::BR)
	}
	return undef;
}

# Rule primitives
sub Same {
	my $self = shift;
	my $other = shift;
	return _same($self -> {'tree'}, $other -> {'tree'});
}
sub Match {
	my $self = shift;
	my $pattern = shift;
	return _match($self -> {'tree'}, $pattern -> {'tree'}, {});
}

sub Replace {
	my $self = shift;
	my $pattern = shift;
	my $replacement = shift;
	my $tree = _substitute($self -> {'tree'}, $pattern -> {'tree'}, $replacement -> {'tree'});
	return main::ProofFormula(_tostr($tree));
}

##################################################
#
#	Remember that compare implements the overloaded perl <=> operator,
#	and $a <=> $b is -1 when $a < $b, 0 when $a == $b and 1 when $a > $b.
#	In our case, we only care about equality, so we will return 0 when
#	equal and other numbers to indicate the reason they are not equal
#	(this can be used by the answer checker to print helpful messages)
#
sub compare {
	# TODO: use Formula comparison instead...
	my ($l,$r) = @_;
	my $self = $l;
	my $context = $self->context;
	$r = Value::makeValue($r, context=>$context) unless Value::isValue($r);
	#
	#	Not equal if the student value is constant or has no + C
	#
	return 2 if !Value::isFormula($r);
	#
	#	Compare with adaptive parameters to see if $l + n00 C = $r for some n0.
	#
	my $adapt = $l->adapt;
	my $equal = ($adapt == $r);
	$self->{adapt} = $self->{adapt}->inherit($adapt);						# save the adapted value's flags
	$self->{adapt}{test_values} = $adapt->{test_values};				 #	(these two are removed by inherit)
	$self->{adapt}{test_adapt} = $adapt->{test_adapt};
	$_[1]->{test_values} = $r->{test_values};						# save these in student answer for diagnostics
	return -1 unless $equal;
	#
	#	Check that n00 is non-zero (i.e., there is a multiple of C in the student answer)
	#	(remember: return value of 0 is equal, and non-zero is unequal)
	#
	return (abs($context->variables->get("n00")->{value}) < $context->flag("zeroLevelTol") ? 1 : 0);
}

#
#	Return the {adapt} formula with test points adjusted
#
sub adapt {
	# TODO: wat?
	my $self = shift;
	return $self->adjustInherit($self->{adapt});
}

#
#	Inherit from the main FormulaUpToConstant, but
#	adjust the test points to include the constants
#
sub adjustInherit {
	# TODO: wat?
	my $self = shift;
	my $f = shift->inherit($self);
	delete $f->{adapt}; delete $f->{constant};
	foreach my $id ('test_points','test_at') {
		if (defined $f->{$id}) {
			$f->{$id} = [$f->{$id}->value] if Value::isValue($f->{$id});
			$f->{$id} = [$f->{$id}] unless ref($f->{$id}) eq 'ARRAY';
			$f->{$id} = [map {
	(Value::isValue($_) ? [$_->value] :
				(ref($_) eq 'ARRAY'? $_ : [$_]))
			} @{$f->{$id}}];
			$f->{$id} = $self->addConstants($f->{$id});
		}
	}
	return $f;
}

#
#	Insert dummy values for the constants for the test points
#	(These are supposed to be +C, so the value shouldn't matter?)
#
sub addConstants {
	# TODO: remove this
	my $self = shift; my $points = shift;
	my @names = $self->context->variables->variables;
	my $variables = $self->context->{variables};
	my $Points = [];
	foreach my $p (@{$points}) {
		if (scalar(@{$p}) == scalar(@names)) {
			push (@{$Points},$p);
		} else {
			my @P = (.1) x scalar(@names); my $j = 0;
			foreach my $i (0..scalar(@names)-1) {
				if (!$variables->{$names[$i]}{arbitraryConstant}) {
		$P[$i] = $p->[$j] if defined $p->[$j]; $j++;
	}
			}
			push (@{$Points}, \@P);
		}
	}
	return $Points;
}

##################################################
#
#	Here we override part of the answer comparison
#	routines in order to be able to generate
#	helpful error messages for students when
#	they leave off the + C.
#

#
#	Show hints by default
#
sub cmp_defaults {((shift)->SUPER::cmp_defaults)};

#
#	Provide diagnostics based on the adapted function used to check
#	the student's answer
#
sub cmp_diagnostics {
	my $self = shift;
	my $adapt = $self->inherit($self->{adapt});
	$adapt->{test_values} = $self->{adapt}{test_values};	# these aren't copied by inherit
	$adapt->{test_adapt}	= $self->{adapt}{test_adapt};
	$adapt->SUPER::cmp_diagnostics(@_);
}

#
#	Make it possible to graph single-variable formulas by setting
#	the arbitrary constants to 0 first.
#
sub cmp_graph {
	my $self = shift; my $diagnostics = shift;
	my $F1 = shift; my $F2; ($F1,$F2) = @{$F1} if (ref($F1) eq 'ARRAY');
	my %subs; my $context = $self->context;
	foreach my $v ($context->variables->variables)
		{$subs{$v} = 0 if ($context->variables->get($v)->{arbitraryConstant})}
	$F1 = $F1->inherit($F1->{adapt})->substitute(%subs)->reduce;
	$F2 = $F2->inherit($F2->{adapt})->substitute(%subs)->reduce;
	$self->SUPER::cmp_graph($diagnostics,[$F1,$F2]);
}

#
#	Add useful messages, if the author requested them
#
sub cmp_postprocess {
	my $self = shift; my $ans = shift;
	$self->SUPER::cmp_postprocess($ans,@_);
	return unless $ans->{score} == 0 && !$ans->{isPreview};
	return if $ans->{ans_message} || !$self->getFlag("showHints");
	my $student = $ans->{student_value};
	my $result = Parser::Eval(sub {return $ans->{correct_value} <=> $student}) || 0; # compare encodes the reason in the result
	$self->cmp_Error($ans,"Note: there is always more than one possibility") if $result == 2 || $result == 3;
	if ($result == 3) {
		my $context = $self->context;
		$context->flags->set(no_parameters=>0);
		$context->variables->add(x00=>'Real');
		my $correct = $self->removeConstant+"n01+n00x00";		# must use both parameters
		$result = 1 if $correct->cmp_compare($student+"x00",{});
		$context->variables->remove('x00');
		$context->flags->set(no_parameters=>1);
	}
	$self->cmp_Error($ans,"Your answer is not the most general solution") if $result == 1;
	$self->cmp_Error($ans,"Your formula should be linear in the constant '$student->{constant}'")
		if $result == -1 && $self->getFlag("showLinearityHints") && !$student->D($student->{constant})->isConstant;
}

######################################################################
#
#	This class replaces the Parser::Variable class, and its job
#	is to look for new constants that aren't in the context,
#	and add them in.	This allows students to use ANY constant
#	they want, and a different one from the professor.	We check
#	that the student only used ONE arbitrary constant, however.
#
package ProofFormula::Variable;
our @ISA = ('Parser::Variable');

sub new {
	my $self = shift;
	my $equation = shift;
	#my $class = ref($self) || $self;
	my $variables = $equation->{context}{variables};
	my ($name, $ref) = @_;
	my $pattern = substr($name, 0, 1) eq '@';
	if ($pattern) {
		$name = substr($name, 1);
	}
	my $def = $variables->{$name};

	#
	#	If the variable is not already in the context, add it
	#		and mark it as an arbitrary constant (for later reference)
	#
	if (!defined($def)) {
		$equation->{context}->variables->add($name => 'Real');
		$equation->{context}->variables->set($name => {arbitraryConstant => 1});
		$def = $variables->{$name};
	}
	#
	#	Do the usual Variable stuff.
	#
	my $v = $self->SUPER::new($equation, $name, $ref);
	if ($pattern) {
		$v -> {'hole'} = $name;
	}
	return $v;
}

package ProofFormula::Function;
our @ISA = ('Parser::Function');
# TODO...

1;
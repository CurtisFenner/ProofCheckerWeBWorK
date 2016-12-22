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
loadMacros("FunctionApplicationBOP.pl");

sub _parserProofFormula_init {ProofFormula::Init()}

package ProofFormula;
@ISA = ('Value::Formula');

sub Init {
	main::PG_restricted_eval('sub ProofFormula {ProofFormula->new(@_)}');
}

Init();

# Modify the text to insert implicit operators
# (`$` as high-precedence function application)
# This is necessary because of webwork's default choice
# for juxtaposition is multiplication, not function application;
# adding new functions prevents those functions' names being used
# in non-function application ways.
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
	);
	$context -> reduction -> clear();
	$context -> constants -> clear();
	# Allow pattern variables that start with '@'
	my $oldpatterns = $context -> {'_variables'} {'patterns'};
	$context -> {'_variables'}{'patterns'} = {qr/@?[a-zA-Z][a-zA-Z0-9]*/i	=> [5, 'var']};

	# Remove all functions from this context (they interfere with parsing; use preprocess to insert $)
	$fs = $context->functions;
	$tokens = $fs->{'tokens'};
	foreach $f (keys %$tokens) {
		$context->functions->remove($f);
	}
	# Add function application operator:
	$context -> operators -> add(
		'$' => {
			class => 'foo::BOP::FunctionApplication',
			precedence => 1000,        # very high?
			associativity => 'left',   #  computed left to right
			type => 'bin',             #  binary operator
			string => '$',             #  output string for it
			TeX => 'not defined here', #  (overriden by class)
		}
	);
	$context -> operators -> remove(' ');
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

sub _form {
	my $tree = shift;
	return main::ProofFormula(_tostr($tree));
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
	} elsif (defined($self -> {'coords'})) {
		my @elements = @{$self -> {'coords'}};
		for (my $i = 0; $i < scalar @elements; $i++) {
			$elements[$i] = _tostr($elements[$i]);
		}
		return "(" . join(", ", @elements) . ")";
	} else {
		main::TEXT( "_tostr couldn't handle:" . main::pretty_print($self) );
		return "UNKNOWN";
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
	} elsif (defined($self -> {'coords'})) {
		my @elements = @{$self -> {'coords'}};
		for (my $i = 0; $i < scalar @elements; $i++) {
			$elements[$i] = _substitute($elements[$i], $needle, $replacement);
		}
		return {
			'coords' => \@elements,
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
	} elsif (defined($pattern -> {'coords'})) {
		my @selfs;
		if (defined($self -> {'coords'})) {
			@selfs = @{$self -> {'coords'}};
		} elsif (ref($self->{'value'}) eq "HASH" && ref($self->{'value'}->{'data'}) eq "ARRAY") {
			@selfs = @{$self -> {'value'} -> {'data'}};
		} else {
			return undef;
		}
		my @patterns = @{$pattern -> {'coords'}};
		if (scalar @patterns != scalar @selfs) {
			return undef;
		}
		for (my $i = 0; $i < scalar @selfs; $i++) {
			$matches = $matches && _match($selfs[$i], $patterns[$i], $matches);
		}
		return $matches;
	} elsif (defined($pattern -> {'bop'})) {
		if (!defined($self -> {'bop'})) {
			return undef;
		}
		if ($self -> {'bop'} ne $pattern -> {'bop'}) {
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

sub Contains {
	my $self = shift;
	my $needle = shift;

	my $without = $self -> Replace($needle, main::ProofFormula('@Q'));

	if ($without -> Same($self)) {
		return 0;
	}
	return "replace-and-got::" . $without->Tostr();
}

sub Match {
	my $self = shift;
	my $pattern = shift;
	my $matches = _match($self -> {'tree'}, $pattern -> {'tree'}, {});
	if (defined($matches)) {
		foreach my $key (keys %{$matches}) {
			$matches -> {$key} = _form( $matches -> {$key} );
		}
		return $matches;
	} else {
		return undef;
	}
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
#	Here we override part of the answer comparison
#	routines in order to be able to generate
#	helpful error messages for students when
#	they leave off the + C.
#

#
#	Show hints by default
#
sub cmp_defaults {((shift)->SUPER::cmp_defaults)};

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
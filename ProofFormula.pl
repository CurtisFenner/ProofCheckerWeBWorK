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
loadMacros("shunting.pl");

sub _parserProofFormula_init {ProofFormula::Init()}

package ProofFormula;

sub Init {
}

Init();

sub TeX {
	# TODO
	return "foo";
}

# Create an instance of a ProofFormula.
sub MAKE {
	# TODO:
	# Allow pattern variables that start with '@'
	# Add implication operator
	# Add `=` operator
	# Add `and` and `or` operators

	#	Create a formula from the user's input.
	my $str = shift;
	my ($e, $err) = proofparsing::parse($str);

	if (!defined($e)) {
		return undef, $err;
	}

	return (bless {'tree' => $e}, 'ProofFormula'), undef;
}

################################################################################

# returns whether or not two expression trees are equivalent
sub _same {
	my $tree = shift;
	my $other = shift;
	defined(_match($tree, $other, {}));
}

# makes a proof formula equivalent to this
sub _form {
	my $tree = shift;
	return main::ProofFormula(_tostr($tree));
}

# makes a string from an expression tree
sub _tostr {
	my $tree = shift;
	my $type = $tree->{'type'};

	if ($type eq 'pattern') {
		return '@' . $tree->{'name'};
	} elsif ($type eq 'constant') {
		return $tree->{'value'};
	} elsif ($type eq 'binary') {
		return '(' . _tostr($tree->{'left'}) . ' ' . $tree->{'op'} . ' ' . _tostr($tree->{'right'}) . ')';
	} elsif ($type eq 'unary') {
		return '(' . $tree->{'op'} . ' ' . _tostr($tree->{'argument'}) . ')';
	} elsif ($type eq 'tuple') {
		my $out = '(';
		for (my $i = 0; $i < $tree->{'count'}; $i++) {
			if ($i > 0) {
				$out .= ', ';
			}
			$out .= _tostr($tree->{$i});
		}
		return $out . ')';
	} elsif ($type eq 'function') {
		# Careful: I assume the {function} is unparenthesized,
		# because that's currently an assumption of the parser
		return _tostr($tree->{'function'}) . '(' . _tostr($tree->{'arguments'}) . ')';
	}

	warn("unrecognized expression type '$type'");
	return "";
}

sub Tostr {
	my $self = shift;
	return _tostr( $self -> {'tree'} );
}

sub _substitute {
	my $tree = shift;
	my $needle = shift;
	my $replacement = shift;
	if (_same($tree, $needle)) {
		return $replacement;
	}

	my $type = $tree->{'type'};

	if ($type eq 'pattern' || $type eq 'constant') {
		return $tree;
	} elsif ($type eq 'binary') {
		return {
			'type' => 'binary',
			'op' => $tree->{'op'},
			'left' => _substitute($tree->{'left'}, $needle, $replacement),
			'right' => _substitute($tree->{'right'}, $needle, $replacement),
		};
	} elsif ($type eq 'unary') {
		return {
			'type' => 'unary',
			'op' => $tree->{'op'},
			'argument' => _substitute($tree->{'argument'}, $needle, $replacement),
		};
	} elsif ($type eq 'tuple') {
		my %elements = ('type'=>'tuple', 'count' => $tree->{'count'});
		for (my $i = 0; $i < $tree->{'count'}; $i++) {
		 	$elements[$i] = _substitute($tree->{'coords'}->{$i}, $needle, $replacement);
		}
		return \%elements;
	} elsif ($type eq 'function') {
		return {
			'type' => 'function',
			'function' => _substitute($tree->{'function'}, $needle, $replacement),
			'arguments' => _substitute($tree->{'arguments'}, $needle, $replacement),
		};
	}

	warn("unrecognized expression type $type");
	return undef;
}

sub _match {
	my $self = shift; # a ProofFormula tree
	my $pattern = shift; # a ProofFormula tree
	my $matches = shift;
	#
	if (ref($pattern) ne 'HASH') {
		warn("pattern $pattern is not a hash / ref(pattern) is `" . ref($pattern) . "`");
		return undef;
	}
	if (!exists($self->{'type'})) {
		warn("self `$self` doesn't have a 'type'");
		return undef;
	}
	if (!exists($pattern->{'type'})) {
		warn("pattern `$pattern` doesn't have a 'type'");
		return undef;
	}

	if ($pattern->{'type'} eq 'pattern') {
		# match against just a pattern-matching-variable
		my $var = $pattern->{'name'};
		if (defined($matches->{$var})) {
			# verify that this object is the same as previous matches
			my $old = $matches->{$var};
			if (_same($self, $old)) {
				return $matches;
			} else {
				return undef;
			}
		} else {
			# new way to match
			$matches->{$var} = $self;
			return $matches;
		}
	} elsif ($pattern->{'type'} eq 'tuple') {
		if ($self->{'type'} ne 'tuple') {
			# pattern is a tuple but this expression is not
			return undef;
		}
		if ($self->{'count'} != $pattern->{'count'}) {
			# patter and this have different sizes
			return undef;
		}
		for (my $i = 0; $i < $self->{'count'}; $i++) {
			$matches = $matches && _match($self->{$i}, $pattern->{$i}, $matches);
		}
		return $matches;
	} elsif ($pattern->{'type'} eq 'binary') {
		if ($self->{'type'} ne 'binary') {
			return undef;
		}
		if ($self->{'op'} ne $pattern->{'op'}) {
			return undef;
		}
		return _match($self->{'left'}, $pattern->{'left'}, $matches)
			&& _match($self->{'right'}, $pattern->{'right'}, $matches);
	} elsif ($pattern->{'type'} eq 'constant') {
		if (_same($self, $pattern)) {
			return $matches;
		}
		return undef;
	}

	main::TEXT(main::pretty_print($pattern));
	return undef;
}

# Rule primitives
sub Same {
	my $self = shift;
	my $other = shift;
	if (ref($other) ne 'ProofFormula') {
		return warn("Same($other) is called with non-ProofFormula parameter;"
			. " instead was passed " . ref($other));
	}

	my $result = _same($self -> {'tree'}, $other -> {'tree'});

	return $result;
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
	if (!defined($self->{'tree'})) {
		return warn("->Match called on a ProofFormula without a {tree}");
	} elsif (!defined($pattern->{'tree'})) {
		return warn("->Match($pattern) called, but pattern doesn't have a {tree}");
	}
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

1;
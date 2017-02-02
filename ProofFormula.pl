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

sub _tex {
	my $tree = shift;
	my $conP = shift;

	my $type = $tree->{'type'};
	if ($type eq 'pattern') {
		return '\fbox{' . $tree->{'name'} . '}';
	} elsif ($type eq 'constant') {
		if (length($tree->{'value'}) > 1) {
			return '\\textrm{' . $tree->{'value'} . '}';
		}
		return $tree->{'value'};
	} elsif ($type eq 'binary') {
		my $myP = proofparsing::Precedence($tree->{'op'});
		my $op = $tree->{'op'};
		if ($op eq '=>') {
			$op = ' \implies ';
		}
		if ($op eq '&') {
			$op = ' \wedge ';
		}
		my $out = _tex($tree->{'left'}, $myP) . ' ' . $op . ' ' . _tex($tree->{'right'}, $myP);
		if ($conP > $myP) {
			return '(' . $out . ')';
		}
		return $out;
	} elsif ($type eq 'unary') {
		my $myP = proofparsing::Precedence('u' . $tree->{'op'});
		my $out = $op . ' ' . _tex($tree->{'argument'}, $myP);
		if ($conP > $myP) {
			return '(' . $out . ')';
		}
		return $out;
	} elsif ($type eq 'tuple') {
		my $out = '(';
		for (my $i = 0; $i < $tree->{'count'}; $i++) {
			if ($i > 0) {
				$out .= ', ';
			}
			$out .= _tex($tree->{$i}, -10000);
		}
		return $out . ')';
	} elsif ($type eq 'function') {
		my $base = _tex($tree->{'function'}, 10000);
		my $arg = _tex($tree->{'arguments'}, 10000);
		if (substr($arg, 0, 1) ne '(') {
			$arg = '(' . $arg . ')';
		}
		return $base . ' ' . $arg;
	}
	warn("unknown type $type for TeX");
}

sub TeX {
	my $self = shift;

	# TODO: do this properly
	return _tex($self->{'tree'}, -10000);
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
	if (!defined($tree->{'type'})) {
		warn("in _form(tree), tree $tree has no type; keys are (" . join(", ", keys %$tree) . ")");
		return undef;
	}

	my $str = _tostr($tree, "_form");
	my ($obj, $err) = ProofFormula::MAKE($str);

	if (!defined($obj)) {
		warn("something went wrong with _form; got '$str' as string, but when that was parsed I got parse error '$err'");
	}
	return $obj;
}

# makes a string from an expression tree
sub _tostr {
	my $tree = shift;
	my $type = $tree->{'type'};
	my $cause = shift || "";

	if (!defined($type)) {
		warn("in _tostr(tree), tree $tree has no type; keys are (" . join(", ", keys %$tree) . "). cause is listed as `$cause`");
		return "UNDEFINED-TYPE";
	}

	if ($type eq 'pattern') {
		return '@' . $tree->{'name'};
	} elsif ($type eq 'constant') {
		return $tree->{'value'};
	} elsif ($type eq 'binary') {
		return '(' . _tostr($tree->{'left'}, "$cause {left}") . ' ' . $tree->{'op'} . ' ' . _tostr($tree->{'right'}, "$cause {right}") . ')';
	} elsif ($type eq 'unary') {
		return '(' . $tree->{'op'} . ' ' . _tostr($tree->{'argument'}, "$cause {argument}") . ')';
	} elsif ($type eq 'tuple') {
		my $out = '(';
		main::pretty_print($tree);
		for (my $i = 0; $i < $tree->{'count'}; $i++) {
			if ($i > 0) {
				$out .= ', ';
			}
			$out .= _tostr($tree->{$i}, "$cause {$i of " . $tree->{'count'} . "}");
		}
		return $out . ')';
	} elsif ($type eq 'function') {
		# Careful: I assume the {function} is unparenthesized,
		# because that's currently an assumption of the parser
		return _tostr($tree->{'function'}) . '(' . _tostr($tree->{'arguments'}, "$cause {arguments}") . ')';
	}

	warn("unrecognized expression type '$type'");
	return "";
}

sub Tostr {
	my $self = shift;
	return _tostr($self -> {'tree'}, "Tostr");
}

sub _substitute {
	my $tree = shift;
	my $needle = shift;
	my $replacement = shift;

	if (!defined($tree->{'type'})) {
		return warn("tree $tree has undefined 'type' in _substitute");
	}
	if (!defined($needle->{'type'})) {
		return warn("needle $needle has undefined 'type' in _substitute");
	}
	if (!defined($replacement->{'type'})) {
		return warn("replacement $replacement has undefined 'type' in _substitute");
	}

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
		 	$elements{$i} = _substitute($tree->{$i}, $needle, $replacement);
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
		return warn("pattern $pattern is not a hash / ref(pattern) is `" . ref($pattern) . "`");
	} elsif (!defined($self->{'type'})) {
		return warn("self `$self` doesn't have a 'type'");
	} elsif (!defined($pattern->{'type'})) {
		return warn("pattern `$pattern` doesn't have a 'type'");
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
		if ($self->{'type'} eq 'constant' && $self->{'value'} eq $pattern->{'value'}) {
			return $matches;
		}
		return undef;
	} elsif ($pattern->{'type'} eq 'function') {
		if ($self->{'type'} ne 'function') {
			return undef;
		}
		return _match($self->{'function'}, $pattern->{'function'}, $matches)
			&& _match($self->{'arguments'}, $pattern->{'arguments'}, $matches);
	}

	return warn("unhandled type ~" . $pattern->{'type'} . "~");
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

	my ($o, $e) = ProofFormula::MAKE('@Q');
	if (!defined($o)) {
		warn("something went wrong: $e");
	}

	my $without = $self -> Replace($needle, $o);

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
	return _form($tree);
}

1;
{
	package foo::BOP::And;
	our @ISA = ('Parser::BOP');

	# unused by proof
	sub _check {return 0;}
	sub _eval {return 0;}
	sub perl {return "<<<unused>>>";}
}

{
	package foo::BOP::Eq;
	our @ISA = ('Parser::BOP');

	# unused by proof
	sub _check {return 0;}
	sub _eval {return 0;}
	sub perl {return "<<<unused>>>";}
}

{
	package foo::BOP::Implies;
	our @ISA = ('Parser::BOP');

	# unused by proof
	sub _check {return 0;}
	sub _eval {return 0;}
	sub perl {return "<<<unused>>>";}
}

#
#  A package for representing function application syntactically
#
package foo::BOP::FunctionApplication;
our @ISA = ('Parser::BOP');            # subclass of Binary OPerator

#  Check operands (not necessary).
sub _check {
	my $self = shift;
	return 0;
}

# evaluation (not defined here)
sub _eval {
	my $self = shift;
	# FunctionApplication is only syntactic and shouldn't be evaluated
	# However, BOP, upon construction, evaluates this and saves it. We don't care about the result, so I just return 0
	return 0;
}

#  Non-standard TeX output.
# TODO: correctly render (1 + 2)$(3 + 4)
# TODO: fix that ->TeX() collapses constants
sub TeX {
	my $self = shift;
	my $right = $self->{rop}->TeX;
	$right =~ s/\\\\//g;
	$right =~ s/\\left//g;
	$right =~ s/\\right//g;

	# if the right side has balanced parenthesis, don't add more

	my $first = substr($right, 0, 1);
	my $last = substr($right, -1);
	my $middle = substr($right, 1, -1);

	my $omit = 1;

	my $level = 0;
	for my $c (split //, $middle) {
		if ($c eq '(') {
			$level++;
		} elsif ($c eq ')') {
			$level--;
			if ($level < 0) {
				$omit = 0;
			}
		}
	}
	if ($level != 0) {
		$omit = 0;
	}
	if (($first ne '(') || ($last ne ')')) {
		$omit = 0;
	}

	if ($omit) {
		return '{\operatorname{ '.$self->{lop}->TeX.' } { ' . $right . ' } }';
	}

	return '{\operatorname{ '.$self->{lop}->TeX.' } \left({ ' . $right . ' }\right) }';
}

#
#  Non-standard perl output
#
sub perl {
	my $self = shift;
	return '<< perl() not defined for FunctionApplication -- used for capturing syntax only >>';
}

package main;

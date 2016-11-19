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
	return '{\operatorname{ '.$self->{lop}->TeX.' } \left({ '.$self->{rop}->TeX.' }\right) }';
}

#
#  Non-standard perl output
#
sub perl {
	my $self = shift;
	return '<< perl() not defined for FunctionApplication -- used for capturing syntax only >>';
}

package main;

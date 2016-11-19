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
# TODO: make f $ 5 be rendered as f(5).
sub TeX {
	my $self = shift;
	return '{'.$self->{lop}->TeX.' \choose '.$self->{rop}->TeX.'}';
}

#
#  Non-standard perl output
#
sub perl {
	my $self = shift;
	return '<< perl() not defined for FunctionApplication -- used for capturing syntax only >>';
}

package main;

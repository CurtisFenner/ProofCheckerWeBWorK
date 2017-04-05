package proofparsing;

# RETURNS a reference to an array of strings
# RETURNS undef, string error message upon failure
sub _tokenize {
	my $str = shift;

	my @tokens = ();
	while (length($str) > 0) {
		my $token = "";
		my $ignore = 0;
		if ($str =~ /^([ \t\r\n]+)/) {
			$token = $1;
			$ignore = 1;
		}
		if ($str =~ /^(@?[0-9a-zA-Z.]+)/) {
			$token = $1;
		}
		if ($str =~ /^([\-\+\*\/=><&|^~]+)/) {
			$token = $1;
		}
		if ($str =~ /^([\[\]\{\}\(\),:;])/) {
			$token = $1;
		}

		if ($token eq "") {
			return undef, "unrecognized character `" . substr($str, 0, 1) . "`";
		}
		if (!$ignore) {
			push @tokens, $token;
		}
		$str = substr($str, length($token), );
	}

	return \@tokens, undef;
}

# all keywords MUST be lowercase
my %aliases = (
	'and' => '&',
	'^' => '&',
	#
	'implies' => '=>',

	'all' => 'forall',
	'exist' => 'exists',

	'forall' => 'forall',
	'exists' => 'exists',

	'is' => 'is',
);

# RETURNS whether or not (as a LaTeX string)
# the argument is a quantifier function base.
sub Quantifier {
	my $arg = shift;
	if ($arg eq 'forall') {
		return "\\forall";
	} elsif ($arg eq 'exists') {
		return "\\exists";
	}
	return undef;
}

my %precedence = (
	'$' => 9999999999,
	'u-' => 100,
	'^' => 5,
	'*' => 4,
	'/' => 4,
	'+' => 2,
	'-' => 2,

	'=' => 0.1,

	'is' => -0.5,

	'&' => -1,
	'=>' => -2,
);

# RETURNS whether or not the argument is the name of a 'fixed constant'
# such as 3.7, pi, -15.
sub IsFixedConstant {
	my $name = shift;
	my $without = $name . '';
	$without =~ s/^\-?\.?[0-9]+//;
	if ($name ne $without) {
		# Numbers are fixed constants
		return 1;
	}

	if ($name eq 'pi' || $name eq 'PI' || $name eq 'Pi') {
		# Significant constants
		return 1;
	}

	if ($name eq 'zero') {
		# vector zero...
		return 1;
	}

	# Everything else is a normal name
	return 0;
}

sub Precedence {
	my $op = shift;
	if (!defined($precedence{$op})) {
		warn("unknown operator ~$op~ passed to Precedence");
	}
	return $precedence{$op};
};

sub shunting {
	my $str = shift;

	# Lex string into tokens
	my ($rawtokens, $err) = _tokenize($str);
	if (!defined($rawtokens)) {
		return undef, $err;
	}

	# Normalize tokens
	for (my $i = 0; $i < scalar @$rawtokens; $i++) {
		my $normalized = $aliases{lc($rawtokens->[$i])};
		if (defined($normalized)) {
			$rawtokens->[$i] = $normalized;
		}
	}

	my %right = (
		'u-' => 1,
		'^' => 1,
	);

	# Annotate unary operators
	my @tokens = ();
	my $previous = "(";
	foreach my $token (@$rawtokens) {
		if ($token eq '(' && !exists($precedence{$previous}) && $previous ne '(' && $previous ne ',') {
			push @tokens, '$';
			push @tokens, '(';
		} elsif (exists($precedence{'u' . $token}) && ( $previous eq "(" || exists($precedence{$previous}))) {
			push @tokens, 'u' . $token;
		} else {
			push @tokens, $token;
		}
		$previous = $token;
	}

	# Do shunting-yard parsing
	my @stack = ();
	my @outQueue = ();
	foreach my $token (@tokens) {
		if ($token eq '(') {
			push @stack, '(1';
			next;
		}

		if ($token eq ')') {
			# Pop everything into queue until open-paren
			while (scalar @stack > 0) {
				my $top = pop @stack;
				if (substr($top, 0, 1) eq '(') {
					push @stack, $top;
					last;
				} else {
					push @outQueue, $top;
				}
			}
			if (scalar @stack == 0) {
				return undef, "there is a `)` with no matching `(`";
			}
			my $open = pop @stack;
			push @outQueue, '$' . substr($open, 1);
			next;
		}

		if ($token eq ',') {
			# The token is an argument-separator;
			# Pop from stack into queue until reach open-paren
			while (scalar @stack > 0) {
				my $top = pop @stack;
				if (substr($top, 0, 1) eq '(') {
					push @stack, '(' . (substr($top, 1) + 1);
					last;
				} else {
					push @outQueue, $top;
				}
			}
			if (scalar @stack == 0) {
				return undef, "a comma or parenthesis is misplaced";
			}
			next;
		}

		if ($precedence{$token}) {
			# The token is an operator;
			while (scalar @stack > 0) {
				my $top = pop @stack;
				if (!defined($precedence{$top})) {
					# parenthesis
					push @stack, $top;
					last;
				} else {
					# other operator
					if ($right{$token}) {
						# $token is right associative
						if ($precedence{$token} < $precedence{$top}) {
							push @outQueue, $top;
						} else {
							push @stack, $top;
							last;
						}
					} else {
						if ($precedence{$token} <= $precedence{$top}) {
							push @outQueue, $top;
						} else {
							push @stack, $top;
							last;
						}
					}
				}
			}
			push @stack, $token;
			next;
		}

		# Output numbers and words
		if ($token =~ /^[\@a-zA-Z0-9.]+$/) {
			push @outQueue, $token;
			next;
		}

		return undef, "uncategorized token `$token`";
	}

	while (scalar @stack > 0) {
		# pop any remaining operators off the stack
		my $top = pop @stack;
		if (substr($top, 0, 1) eq '(') {
			return undef, "there is a `(` with no matching `)`";
		}
		push @outQueue, $top;
	}

	return \@outQueue, undef;
}

sub parseRPN {
	my $actions_ref = shift;
	my @actions = @$actions_ref;

	if (scalar @actions < 1) {
		return undef, "nothing was provided";
	}

	my @stack = ();
	foreach $action (@actions) {
		if ($action eq '$1') {
			# parenthesis around an expression; ignore
		} elsif (substr($action, 0, 1) eq '$') {
			if ($action eq '$') {
				# Function call
				if (scalar @stack < 2) {
					return undef, "misplaced function";
				}
				my $arg = pop @stack;
				my $fun = pop @stack;
				push @stack, {'type' => 'function', 'function' => $fun, 'arguments' => $arg};
			} else {
				# Tuple
				my $count = substr($action, 1);
				if (scalar @stack < $count) {
					return undef, "misplaced tuple/comma";
				}

				my %args = ('type' => 'tuple', 'count' => $count);
				for (my $i = 0; $i < $count; $i++) {
					$args{$count-1-$i} = pop @stack;
				}
				push @stack, \%args;
			}
		} elsif (exists($precedence{$action})) {
			if (substr($action, 0, 1) eq 'u') {
				# Unary operator
				if (scalar @stack < 1) {
					return undef, "misplaced unary operator '" . substr($action, 1) . "'";
				}
				my $arg = pop @stack;
				push @stack, {'type' => 'unary', 'argument' => $arg, 'op' => substr($action, 1)};
			} else {
				# Binary operator
				if (scalar @stack < 2) {
					return undef, "misplaced binary operator '$action'";
				}
				my $right = pop @stack;
				my $left = pop @stack;
				push @stack, {'type' => 'binary', 'left' => $left, 'right' => $right, 'op' => $action};
			}
		} else {
			# Atom (constant / variable / hole)
			if (substr($action, 0, 1) eq '@') {
				# Pattern variable
				push @stack, {'type' => 'pattern', 'name' => substr($action, 1)};
			} else {
				push @stack, {'type' => 'constant', 'value' => $action};
			}
		}
	}
	if (scalar @stack == 0) {
		return undef, "no expression was entered";
	}

	if (scalar @stack > 1) {
		my $problem = " '" . $stack[1] . "'";
		if (ref($stack[1]) ne '') {
			$problem = "";
		}
		return undef, "unexpected value" . $problem . "; did you forget a comma or operator?";
	}
	return $stack[0], undef;
}

# for debugging
# $e: a reference or scalar
# RETURNS: a string representation of $e
sub explain {
	my $e = shift;
	if (!ref($e)) {
		return "'$e'";
	} elsif (ref($e) eq 'HASH') {
		my $out = '{';
		while (my ($k, $v) = each %$e) {
			$out .= explain($k) . ' => ' . explain($v) . ',';
		}
		return $out . '}';
	}
	return "[" . ref($e) . "]";
}

# "fixes" an expression, reported errors with certain invalid constructs
# RETURNS (expression, error message)
sub fixExpression {
	my $e = shift;

	my $type = $e->{'type'};
	if (!defined($type)) {
		main::TEXT("<h1>" . explain($e) . "</h1>");
	}

	if ($type eq 'binary') {
		my $op = $e->{'op'};

		if ($op eq 'is') {
			return fixExpression({
				'type' => 'function',
				'arguments' => $e->{'left'},
				'function' => $e->{'right'},
			});
		}

		my ($newLeft, $err) = fixExpression($e->{'left'});
		if (!defined($newLeft)) {
			return undef, $err;
		}

		my ($newRight, $err) = fixExpression($e->{'right'});
		if (!defined($newRight)) {
			return undef, $err;
		}

		return {
			'type' => 'binary',
			'op' => $op,
			'left' => $newLeft,
			'right' => $newRight,
		}, undef;
	} elsif ($type eq 'function') {
		my $base = $e->{'function'};

		# Verify that the function/predicate is a name and not something else
		if ($base->{'type'} ne 'constant' && $base->{'type'} ne 'pattern') {
			warn("<h1>base: " . explain($base) . "</h1>");
			return undef, 'Functions and predicates must be names, not ' . $base->{'type'} . ' expressions.';
		}

		# Verify the function base is not a fixed constant (like a number)
		if ($base->{'type'} eq 'constant' && IsFixedConstant($base->{'value'})) {
			return undef, "A constant like '" . $base->{'value'} . "' cannot be used as a function/predicate.";
		}

		# Verify the variable of a quantifier is a constant
		if (Quantifier($base->{'value'})) {
			if ($e->{'arguments'}->{'type'} ne 'tuple') {
				return undef, "The quantifier " . $base->{'value'} . " requires at least two things: the variable, and the statement about the variable.";
			}
			my $variable = $e->{'arguments'}->{'0'};
			if ($variable->{'type'} ne 'constant' && $variable->{'type'} ne 'pattern') {
				return undef, "The quantifier " . $base->{'value'} . " requires the variable be a simple name like 'x', not a " . $variable->{'type'} . " expression.";
			}
			if ($variable->{'type'} eq 'constant' && IsFixedConstant($variable->{'value'})) {
				return undef, "The quantifier " . $base->{'value'} . " requires a variable name, and not a fixed constant like " . $variable->{'value'} . ".";
			}
		}

		# TODO: validate quantifier variables
		# 3) not in scope: `x and forall(x, P(x))`

		# Recursively check expression
		my ($newFunction, $err) = fixExpression($base);
		if (!defined($newFunction)) {
			return undef, $err;
		}
		my ($newArgs, $err) = fixExpression($e -> {'arguments'});
		if (!defined($newArgs)) {
			return undef, $err;
		}
		return {
			'type' => 'function',
			'function' => $newFunction,
			'arguments' => $newArgs,
		}, undef;
	} elsif ($type eq 'constant' || $type eq 'pattern') {
		# a constant cannot be invalid (I think?)
		return $e, undef;
	} elsif ($type eq 'tuple') {
		my $out = {
			'type' => 'tuple',
			'count' => $e->{'count'},
		};
		for (my $i = 0; $i < $e->{'count'}; $i++) {
			my ($f, $err) = fixExpression($e->{$i});
			if (!defined($f)) {
				return undef, $err;
			}
			$out->{$i} = $f;
		}
		return $out, undef;
	} elsif ($type eq 'unary') {
		my ($newArg, $err) = fixExpression($e->{'argument'});
		if (!defined($newArg)) {
			return undef, $err;
		}

		return {
			'type' => 'unary',
			'op' => $e->{'op'},
			'argument' => $newArg,
		}, undef;
	}

	warn("unhandled expression of type $type in shunting.pl::fixExpression");
	return $e, undef;
}

# An Expression has a {type}
#     type => pattern: has a {name} which is a string
#     type => constant: has a {value} which is a string
#     type => binary: has a {left} and {right} which are expression refs.
#                     has a {op} which is a string
#     type => unary: has a {argument} which is an expression ref.
#                    has a {op} which is a string
#     type => tuple: has a {count} which is an integer 2 or greater.
#                   has a {0}, {1}, ..., {count-1} which are expression refs.
#     type => function: has a {function} which is an expression ref
#                           (probably a pattern or constant).
#                       has a {arguments} which is an expression ref
#                           (a tuple for multi-argument functions)
# Takes a string as an argument
# RETURNS <expression ref>, <error string>
sub parse {
	my $str = shift;
	if (!defined($str)) {
		warn("proofparsing::parse should be passed a string, not undef");
		return undef, "INSTRUCTOR MISUSE";
	}

	my ($tokens, $err) = shunting($str);
	if (!defined($tokens)) {
		return undef, $err;
	}
	my ($f, $err) = parseRPN($tokens);
	if (!defined($f)) {
		return undef, $err;
	}
	return fixExpression($f);
}

# use Data::Dumper;

# print( Dumper( parse("-x") ) );
# print( Dumper(parse('exists(x, L(x, x) & H(x,x))') ) );

#return 1;
1;
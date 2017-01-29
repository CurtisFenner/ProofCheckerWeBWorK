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

my %precedence = (
	'$' => 9999999999,
	'-u' => 100,
	'^' => 5,
	'*' => 4,
	'/' => 4,
	'+' => 2,
	'-' => 2,

	'=' => 0,
	'&' => -1,
);

sub Precedence {
	my $op = shift;
	if (!defined($precedence{$op})) {
		warn("unknown operator ~$op~ passed to Precedence");
	}
	return $precedence{$op};
};

sub shunting {
	my $str = shift;

	my ($rawtokens, $err) = _tokenize($str);
	if (!defined($rawtokens)) {
		return undef, $err;
	}

	my %right = (
		'-u' => 1,
		'^' => 1,
	);

	# Annotate unary operators
	my @tokens = ();
	my $previous = "(";
	foreach my $token (@$rawtokens) {
		if ($token eq '(' && !exists($precedence{$previous}) && $previous ne '(') {
			push @tokens, '$';
			push @tokens, '(';
		} elsif (exists($precedence{$token . 'u'}) && ($i == 0 || $previous eq "(" || exists($precedence{$previous}))) {
			push @tokens, $token . 'u';
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
					return undef, "misplaced operator '" . substr($action, 1) . "'";
				}
				my $arg = pop @stack;
				push @stack, {'type' => 'unary', 'argument' => $arg, 'op' => substr($action, 1)};
			} else {
				# Binary operator
				if (scalar @stack < 2) {
					return undef, "misplaced operator '$action'";
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
		return undef, "unexpected value '" . $stack[1] . "'";
	}
	return $stack[0], undef;
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
	return parseRPN($tokens);
}

# use Data::Dumper;
# print( Dumper(parse('exists(x, L(x, x) & H(x,x))') ) );

return 1;

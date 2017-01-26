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
		if ($str =~ /^([\@0-9a-zA-Z.]+)/) {
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

	print("tokenization: [" . join(", ", @tokens) . "]\n");
	return \@tokens, undef;
}

sub shunting {
	my $str = shift;

	my ($rawtokens, $err) = _tokenize($str);
	if (!defined($rawtokens)) {
		return undef, $err;
	}

	my %precedence = (
		'$' => 9999999999,
		'-u' => 100,
		'^' => 5,
		'*' => 4,
		'/' => 4,
		'+' => 2,
		'-' => 2,
	);
	my %right = (
		'-u' => 1,
		'^' => 1,
	);

	# Annotate unary operators
	my @tokens = ();
	my $previous = "(";
	foreach my $token (@$rawtokens) {
		print("preprocessing $token\n");
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

	print("annotated tokens: [" . join(", ", @tokens) . "]\n");

	# Do shunting-yard parsing
	my @stack = ();
	my @outQueue = ();
	foreach my $token (@tokens) {
		print("processing `$token`\n");

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

		warn "uncategorized token `$token`";
	}

	while (scalar @stack > 0) {
		# pop any remaining operators off the stack
		my $top = pop @stack;
		if (substr($top, 0, 1) eq '(') {
			return undef, "there is a `(` with no matching `)`";
		}
		push @outQueue, $top;
	}

	print("\noutQueue size is " . scalar @outQueue . "\n");
	return \@outQueue, undef;
}

my ($out, $err) = shunting("cos  (1 + 2)");
print("output: " . join ",", @$out);

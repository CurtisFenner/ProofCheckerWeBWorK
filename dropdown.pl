# A class that generates HTML for dropdowns
# Based on https://github.com/openwebwork/pg/blob/master/macros/parserPopUp.pl

package Dropdown;

our $_index = 0;
our $_UNIQUE_PREFIX = "dropdownprefix";

sub new {
	my $class = shift;
	my $options = shift;
	if (ref($options) ne 'ARRAY') {
		warn("Dropdown expects an array-reference. You can use [] to create one");
	}
	$_index++;
	my $obj = {'options' => $options, 'id' => $_UNIQUE_PREFIX . $_index};
	return bless $obj, $class;
}

# RETURNS a string, the blank ID
sub html {
	my $self = shift;
	my $name = $self->{'id'};
	my $label = main::generate_aria_label($name);

	# Get submitted value
	my $value = $main::inputs_ref->{$name} || "";

	# Output drop down
	main::TEXT("<select class='pg-select' name='$name' id='$name' aria-label='$label' size='1' value='$value'>\n");
	foreach my $option (@{$self->{'options'}}) {
		my $selected = '';
		if ($option eq $value) {
			$selected = 'selected';
		}
		main::TEXT("<option value='$option' class='tex2jax_ignore' $selected>$option</option>\n");
	}
	main::TEXT("</select>\n");

	# Return unique input ID
	return $name;
}

return 1;

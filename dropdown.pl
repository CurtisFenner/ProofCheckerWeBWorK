# A class that generates HTML for dropdowns
# Based on https://github.com/openwebwork/pg/blob/master/macros/parserPopUp.pl

package Dropdown;

our $_index = 0;
our $_UNIQUE_PREFIX = "dropdownprefix";

sub new {
	my $class = shift;
	my $options = shift;
	my $values = shift || $options;
	if (ref($options) ne 'ARRAY') {
		warn("Dropdown expects an array-reference. You can use [] to create one");
	}
	if (ref($values) ne 'ARRAY') {
		warn("Dropdown expects an array-reference. You can use [] to create one");
	}
	if (scalar @$options != scalar @$values) {
		warn("Dropdown options and values arrays must be the same length");
	}
	$_index++;
	my $obj = {'options' => $options, 'values' => $values, 'id' => $_UNIQUE_PREFIX . $_index};
	return bless $obj, $class;
}

# RETURNS a string, the blank ID
sub html {
	my $self = shift;
	my $name = $self->{'id'};
	my $label = main::generate_aria_label($name);

	# Get submitted value
	my $submitted = $main::inputs_ref->{$name} || "";

	# Output drop down
	main::TEXT("<select class='pg-select' name='$name' id='$name' aria-label='$label' size='1' value='$submitted'>\n");
	for (my $i = 0; $i < scalar @{$self->{'options'}}; $i++) {
		my $option = $self->{'options'}->[$i];
		my $value = $self->{'values'}->[$i];

		my $selected = '';
		if ($value eq $submitted) {
			$selected = 'selected';
		}
		main::TEXT("<option value='$value' class='tex2jax_ignore' $selected>$option</option>\n");
	}
	main::TEXT("</select>\n");

	# Return unique input ID
	return $name;
}

return 1;

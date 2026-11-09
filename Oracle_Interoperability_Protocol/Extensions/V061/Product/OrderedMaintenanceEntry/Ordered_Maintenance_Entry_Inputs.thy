theory Ordered_Maintenance_Entry_Inputs
  imports "OIP_Ordered_Maintenance_G0_Core.Ordered_Maintenance_Source_Input"
begin

type_synonym maintenance_entry_input = "bool \<times> bool \<times> product_principal option"

definition maintenance_entry_inputs :: "maintenance_entry_input list" where
  "maintenance_entry_inputs =
    [(False, False, Some maintenance_input_principal),
     (True, False, Some maintenance_input_principal),
     (False, True, Some maintenance_input_principal),
     (True, True, Some maintenance_input_principal),
     (False, False, None)]"

end

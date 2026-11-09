theory Ordered_Maintenance_Source_Input
  imports "OIP_Product.Recovery_Anchor" "OIP_Product.Wire_Product_Execution"
begin

definition maintenance_input_profile :: recovery_profile where
  "maintenance_input_profile = \<lparr>recovery_deployment = 7, recovery_format = 1,
    recovery_authority_profile = 99\<rparr>"

definition maintenance_input_principal :: product_principal where
  "maintenance_input_principal = 7"

definition maintenance_input_product_cut :: product_cut where
  "maintenance_input_product_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 2\<rparr>"

definition maintenance_input_selection :: wire_bytes where
  "maintenance_input_selection = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]"

definition maintenance_input_observe_time :: "product_session_id \<times> nat" where
  "maintenance_input_observe_time = (2, 105)"

end

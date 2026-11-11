theory Reserve_Debit_Seed
  imports "OIP_Reserve_Debit_Finite_Base.Wire_Code_Finite_Source_Slice" Wire_Code_Fixture_Input_Data
begin

definition code_fixture_initial_slice :: "code_finite_source_slice" where
  "code_fixture_initial_slice = \<lparr>slice_financial = code_fixture_initial_machine,slice_source_bindings = [],
    slice_holder_balances = code_fixture_source_account_rows,slice_revision = 0,slice_binding_epoch = 9,slice_separator = 0\<rparr>"


end

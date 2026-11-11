theory Historical_Read_Export
  imports "OIP_Historical_Read_G0.Historical_Read_G0" "HOL-Library.Code_Target_Nat"
begin

fun historical_export_reply :: "product_read_reply \<Rightarrow> nat list" where
  "historical_export_reply (Current_Cut_Value selected_cut (Units_Value units_input)) =
    [1,1,1,cut_authority_epoch selected_cut,cut_revision selected_cut,1,units_input]"
| "historical_export_reply (Historical_Prefix_Value named_index (Units_Value units_input)) =
    [2,1,0,0,named_index,1,units_input]"
| "historical_export_reply Product_Read_Busy = [3,0,0,0,0,0,0]"
| "historical_export_reply Product_Read_Unavailable = [4,0,0,0,0,0,0]"
| "historical_export_reply Product_Read_Rejected = [5,0,0,0,0,0,0]"
| "historical_export_reply _ = [6,0,0,0,0,0,0]"

definition historical_export_prefixes :: "integer \<Rightarrow> integer \<Rightarrow> integer list list" where
  "historical_export_prefixes initial_input written_input =
    (let prefixes = historical_fixture_prefixes (nat_of_integer initial_input) (nat_of_integer written_input)
     in map (\<lambda>index. let projection = prefixes ! index in map integer_of_nat
       [index,historical_units projection,(if historical_locked projection then 1 else 0),
        (if historical_unpublished_touch projection then 1 else 0),
        (if historical_registered projection then 1 else 0)]) [0..<length prefixes])"

fun historical_export_observe_nat :: "nat list \<Rightarrow> nat list option" where
  "historical_export_observe_nat [row_id,read_kind,requested_index,epoch_input,initial_input,written_input,
      access_input,available_input] =
    (if read_kind > 1 \<or> access_input > 1 \<or> available_input > 1 then None
     else let prefixes = historical_fixture_prefixes initial_input written_input;
       history = historical_fixture_history epoch_input initial_input written_input;
       selected_cut = reference_observed_cut history;
       original = (if read_kind = 0 then historical_native_read False (access_input = 1)
          (available_input = 1) requested_index prefixes
         else historical_native_current (access_input = 1) (available_input = 1)
           \<lparr>cut_authority_epoch = epoch_input,cut_revision = requested_index\<rparr>
           epoch_input (cut_revision selected_cut) prefixes);
       altered = (if read_kind = 0 then historical_native_read True (access_input = 1)
          (available_input = 1) requested_index prefixes else original)
     in Some ([row_id,read_kind,requested_index,cut_authority_epoch selected_cut,
        cut_revision selected_cut,length prefixes] @ historical_export_reply original @ historical_export_reply altered))"
| "historical_export_observe_nat _ = None"

definition historical_export_observe :: "integer list \<Rightarrow> integer list option" where
  "historical_export_observe inputs =
    (if list_all (\<lambda>n. 0 \<le> n) inputs then
       map_option (map integer_of_nat) (historical_export_observe_nat (map nat_of_integer inputs))
     else None)"

lemma historical_export_does_not_label_a_historical_value_current:
  "historical_export_reply (Historical_Prefix_Value index (Units_Value units_input)) \<noteq>
    historical_export_reply (Current_Cut_Value selected_cut (Units_Value units_input))"
  by simp

export_code historical_export_prefixes historical_export_observe
  in SML module_name OIP_Historical_Read file_prefix "oip_historical_read"

thm_oracles historical_export_does_not_label_a_historical_value_current

end

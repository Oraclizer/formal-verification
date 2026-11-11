theory Retained_Transition_Source_Link
  imports "OIP_Record_Reopening_Prefix_G0.Record_Reopening_Prefix_G0"
begin

definition rti_source_link :: "nat list list \<Rightarrow> nat list option" where
  "rti_source_link rti_heads =
    (case rti_heads of [rti_old,rti_old_hash,rti_next,rti_next_hash,rti_parent,rti_parent_hash] \<Rightarrow>
       (case (rr_make_address rti_old rti_old_hash,rr_make_address rti_next rti_next_hash,
              rr_make_address rti_parent rti_parent_hash) of
          (Some rti_previous,Some rti_selected,Some rti_recorded) \<Rightarrow>
            Some [if rti_recorded = rti_previous then 1 else 0,
                  if rr_parent_ok rti_selected (Some rti_recorded) then 1 else 0]
        | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition rti_u64 :: "integer \<Rightarrow> bool" where
  "rti_u64 rti_word \<longleftrightarrow> 0 \<le> rti_word \<and> rti_word < 18446744073709551616"

definition rti_source_link_integer_abi :: "integer list list \<Rightarrow> integer list option" where
  "rti_source_link_integer_abi rti_heads =
    (if list_all (list_all rti_u64) rti_heads
     then map_option (map integer_of_nat) (rti_source_link (map (map nat_of_integer) rti_heads))
     else None)"

thm_oracles rr_read_success_exposes_computed_guards

export_code rti_source_link_integer_abi in SML
  module_name OIP_Retained_Transition_Source_ABI file_prefix "oip_retained_transition_source_abi"

end

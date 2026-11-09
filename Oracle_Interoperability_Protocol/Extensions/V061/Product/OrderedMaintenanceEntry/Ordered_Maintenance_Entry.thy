theory Ordered_Maintenance_Entry
  imports "OIP_Ordered_Maintenance_G0_Core.Ordered_Maintenance_G0" Ordered_Maintenance_Entry_Inputs
begin

definition consume_open_generic_maintenance ::
  "product_principal option \<Rightarrow> (product_principal \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> 'reply option) \<Rightarrow>
    retained_product \<Rightarrow> retained_product \<times> 'reply option" where
  "consume_open_generic_maintenance opened legacy records =
    (case opened of None \<Rightarrow> (records, None) | Some actor \<Rightarrow> legacy actor records)"

definition guard_generic_maintenance where
  "guard_generic_maintenance attached_ordered configured_ordered local_actor legacy records =
    consume_open_generic_maintenance (open_generic_maintenance attached_ordered configured_ordered local_actor) legacy records"

theorem ordered_generic_maintenance_is_rejected_before_the_legacy_effect:
  assumes "attached_ordered \<or> configured_ordered"
  shows "open_generic_maintenance attached_ordered configured_ordered local_actor = None"
    "guard_generic_maintenance attached_ordered configured_ordered local_actor legacy records = (records, None)"
  using assms by (simp_all add: guard_generic_maintenance_def consume_open_generic_maintenance_def open_generic_maintenance_def)

theorem a_generic_open_requires_standalone_and_the_exact_local_actor:
  "open_generic_maintenance attached_ordered configured_ordered local_actor = Some actor \<longleftrightarrow>
    \<not> attached_ordered \<and> \<not> configured_ordered \<and> local_actor = Some actor"
  by (auto simp: open_generic_maintenance_def)

theorem standalone_generic_maintenance_consumes_the_existing_local_result:
  "guard_generic_maintenance False False (Some actor) legacy records = legacy actor records"
  "guard_generic_maintenance False False None legacy records = (records, None)"
  by (simp_all add: guard_generic_maintenance_def consume_open_generic_maintenance_def generic_maintenance_route_controls)

lemma guarded_dispatch_is_the_existing_dispatch_consumer:
  "guard_generic_maintenance attached_ordered configured_ordered local_actor
     (\<lambda>actor. consume_generic_dispatch False False (Some actor) verified request) records =
   consume_generic_dispatch attached_ordered configured_ordered local_actor verified request records"
  by (cases "open_generic_maintenance attached_ordered configured_ordered local_actor")
     (simp_all add: guard_generic_maintenance_def consume_open_generic_maintenance_def
       consume_generic_dispatch_def generic_maintenance_route_controls)

section \<open>Single-condition removal inside the model\<close>

definition canary_without_ordered_attachment where
  "canary_without_ordered_attachment (attached_ordered :: bool) configured_ordered local_actor legacy records =
    consume_open_generic_maintenance (open_generic_maintenance False configured_ordered local_actor) legacy records"

definition canary_without_ordered_configuration where
  "canary_without_ordered_configuration attached_ordered (configured_ordered :: bool) local_actor legacy records =
    consume_open_generic_maintenance (open_generic_maintenance attached_ordered False local_actor) legacy records"

abbreviation entry_legacy_dispatch where
  "entry_legacy_dispatch actor \<equiv> consume_generic_dispatch False False (Some actor) (\<lambda>_. False) dispatch_request"

lemma each_ordered_condition_independently_stops_the_existing_dispatch:
  "guard_generic_maintenance True False dispatch_actor entry_legacy_dispatch
    (ordered_maintenance_records dispatch_witness) = (ordered_maintenance_records dispatch_witness, None)"
  "canary_without_ordered_attachment True False dispatch_actor entry_legacy_dispatch
    (ordered_maintenance_records dispatch_witness) = (dispatch_after, Some (Settlement_Dispatched (Some dispatched_job)))"
  "guard_generic_maintenance False True dispatch_actor entry_legacy_dispatch
    (ordered_maintenance_records dispatch_witness) = (ordered_maintenance_records dispatch_witness, None)"
  "canary_without_ordered_configuration False True dispatch_actor entry_legacy_dispatch
    (ordered_maintenance_records dispatch_witness) = (dispatch_after, Some (Settlement_Dispatched (Some dispatched_job)))"
  by (simp_all add: guard_generic_maintenance_def
    canary_without_ordered_attachment_def canary_without_ordered_configuration_def consume_open_generic_maintenance_def
    generic_maintenance_route_controls generic_dispatch_uses_the_standalone_authority_and_stops_on_ordered_authority)

section \<open>Consumer observations generated from the original guard\<close>

fun observe_maintenance_entry where
  "observe_maintenance_entry (attached_ordered, configured_ordered, local_actor) =
    open_generic_maintenance attached_ordered configured_ordered local_actor"

definition maintenance_entry_table where
  "maintenance_entry_table = map (\<lambda>input. (input, observe_maintenance_entry input)) maintenance_entry_inputs"

value [code] "maintenance_entry_table"

export_code open_generic_maintenance maintenance_entry_table
  in SML module_name OIP_Maintenance_Entry file_prefix "oip_maintenance_entry"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordered_generic_maintenance_is_rejected_before_the_legacy_effect
      a_generic_open_requires_standalone_and_the_exact_local_actor
      standalone_generic_maintenance_consumes_the_existing_local_result
      guarded_dispatch_is_the_existing_dispatch_consumer each_ordered_condition_independently_stops_the_existing_dispatch})
  then () else error "Unexpected oracle in generic maintenance entry"
\<close>

end

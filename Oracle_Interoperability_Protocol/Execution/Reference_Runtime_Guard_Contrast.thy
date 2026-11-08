theory Reference_Runtime_Guard_Contrast
  imports Reference_Runtime_Vectors
begin

definition debit_without_signed_generation where
  "debit_without_signed_generation registered verified entry actor credential binding generation versions code =
     (let slot = rust_lock_slots code (binding_key binding);
          current = (case slot of None \<Rightarrow> generation | Some value \<Rightarrow> rust_slot_generation value)
      in rust_submit_debit registered verified entry actor credential binding current versions code)"

lemma the_signed_generation_case_changes_only_when_the_command_generation_is_ignored:
  defines "binding \<equiv> \<lparr>binding_key = (0,17), binding_asset = 17, binding_amount = 5,
     binding_destination = 2, binding_recipient = 3, binding_source_epoch = 9,
     binding_operation = Destination_Credit, binding_separator = 0\<rparr>"
    and "credential \<equiv> \<lparr>credential_token = \<lparr>token_asset = 17, token_owner = 7, token_generation = 0\<rparr>,
     credential_epoch = 9, credential_origin = (0,17)\<rparr>"
  shows "rust_submit_debit True True Normal_Lock_Entry 7 credential binding 1 (\<lambda>_. 0) lease_stale =
       (lease_stale, Request_Rejected)"
    "let (after, reply) = debit_without_signed_generation True True Normal_Lock_Entry 7 credential binding 1
       (\<lambda>_. 0) lease_stale in (map_option rust_slot_phase (rust_lock_slots after (0,17)), rust_lock_balance after, reply) =
       (Some Source_Pending, 5, Source_Debited)"
  by (simp_all add: binding_def credential_def debit_without_signed_generation_def rust_submit_debit_def
      rust_bound_debit_def lease_stale_def Let_def)

definition receive_without_exact_replay_compare where
  "receive_without_exact_replay_compare verify attest body_allowed authority bytes cache =
    (case wire_gate verify attest body_allowed authority bytes of
       Gate_Refused reason \<Rightarrow> (cache, Wire_Rejected reason)
     | Gate_Admitted packet \<Rightarrow>
         let core = packet_core packet; key = authenticated_wire_message_id core in
           case cache key of None \<Rightarrow> (cache(key := Some (encode_wire_core core)), Wire_First packet)
           | Some _ \<Rightarrow> (cache, Wire_Identical packet))"

lemma deleting_only_the_exact_core_comparison_misclassifies_the_same_admitted_bytes:
  assumes admitted: "wire_gate verify attest body_allowed authority bytes = Gate_Admitted packet"
    and cached: "cache (authenticated_wire_message_id (packet_core packet)) = Some prior"
    and changed: "prior \<noteq> encode_wire_core (packet_core packet)"
  shows "receive_canonical_wire verify attest body_allowed authority bytes cache = (cache, Wire_Rejected Conflicting_Wire_Replay)"
    "receive_without_exact_replay_compare verify attest body_allowed authority bytes cache = (cache, Wire_Identical packet)"
  using assms by (simp_all add: receive_canonical_wire_def receive_without_exact_replay_compare_def Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_signed_generation_case_changes_only_when_the_command_generation_is_ignored
     deleting_only_the_exact_core_comparison_misclassifies_the_same_admitted_bytes})
  then () else error "Unexpected oracle in model guard contrasts"
\<close>

end

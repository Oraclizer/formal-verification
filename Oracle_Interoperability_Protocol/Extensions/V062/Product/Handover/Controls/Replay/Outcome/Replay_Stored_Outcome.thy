theory Replay_Stored_Outcome
  imports "OIP_V062_P13_Replay_Epoch_Base.Replay_Epoch_Base"
    "OIP_Reference_Profile.Reference_Authority_Grants"
begin

text \<open>The stored payload/outcome is produced by the actual authoritative
submit, then the ordinary completion step used by fresh execution. The
input assertion receipt_exists is never used to manufacture an entry.\<close>

definition pro_permissions :: "reference_permission list" where
  "pro_permissions = [Ref_Reserve,Ref_Dispatch,Ref_Debit,Ref_Cancel,Ref_Refund,Ref_Attest,Ref_Observe_Time,Ref_Publish_Primary]"

definition pro_inputs :: "nat \<Rightarrow> reference_authority_inputs" where
  "pro_inputs m_epoch = \<lparr>reference_epoch = m_epoch,
    reference_grants = (\<lambda>m_endpoint. if m_endpoint \<in> {0,2}
      then set (concat (map (\<lambda>m_actor. map (\<lambda>m_permission. (m_actor,Normal_Lock_Entry,m_permission)) pro_permissions) [7,8]))
      else {})\<rparr>"

definition pro_verified :: "product_principal \<Rightarrow> client_call_id \<Rightarrow> product_call_payload \<Rightarrow> bool" where
  "pro_verified = (\<lambda>_ _ _. True)"

definition pro_initial :: outcome_world where
  "pro_initial = initial_outcome_world hf_initial"

definition pro_original_outcome :: product_outcome where
  "pro_original_outcome = normalized_authority_reply (snd (sample.execute_finality_client hf_reserve finality_sample_initial))"

definition pro_original_entry :: product_result_entry where
  "pro_original_entry = \<lparr>result_payload = prp_original_payload, result_outcome = pro_original_outcome\<rparr>"

definition pro_submitted :: outcome_world where
  "pro_submitted = sample.submit_authoritative_call (reference_permitted_at (pro_inputs 9)) pro_verified
    ({7}::nat set) {0,2} Normal_Lock_Entry 7 ((7,1)::client_call_id) prp_original_payload pro_initial"

definition pro_completed :: outcome_world where
  "pro_completed = fst (complete_authoritative_result pro_verified 7 ((7,1)::client_call_id) prp_original_payload pro_submitted)"

lemma pro_original_reserve_has_no_lock_token:
  "payload_credential prp_original_payload = None"
  by (simp add: prp_original_payload_def)

lemma pro_reserve_uses_the_actual_reference_grant:
  "reference_permitted_at (pro_inputs 9) Normal_Lock_Entry 7
    (envelope_command (payload_envelope prp_original_payload))"
  by (simp add: reference_permitted_at_def pro_inputs_def pro_permissions_def
      prp_original_payload_def hf_envelope_def hf_reserve_def)

lemma pro_reserve_is_registered_and_admitted_without_a_lock_token:
  "registered_lock_envelope {0,2} (payload_envelope prp_original_payload)"
  "lock_envelope_admitted 7 (payload_envelope prp_original_payload) (None::product_lock_credential option) hf_initial"
  by (simp_all add: registered_lock_envelope_def lock_envelope_admitted_def prp_original_payload_def hf_envelope_def hf_reserve_def
      envelope_matches_request_def envelope_matches_binding_def sample_request_def sample_binding_def example_binding_def
      prp_initial_reserved_dispatched_metadata)

lemma pro_reserve_identity_is_bound_before_and_after_submission:
  "product_identity_bound 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) hf_initial"
  "product_identity_bound 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) hf_reserved"
  by (simp_all add: product_identity_bound_def prp_original_payload_def hf_envelope_def hf_reserve_def
      sample_request_def prp_initial_reserved_dispatched_metadata hf_sessions_def)

lemma pro_actual_lock_entry_is_the_checked_reserve:
  "sample.lock_product_step (reference_permitted_at (pro_inputs 9)) (\<lambda>_ _ _ _. True)
    ({7}::nat set) {0,2}
    (Lock_Submit Normal_Lock_Entry 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) None) hf_initial = hf_reserved"
proof -
  have entry: "sample.submit_lock_entry (reference_permitted_at (pro_inputs 9)) (\<lambda>_ _ _ _. True)
    Normal_Lock_Entry 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) (None::product_lock_credential option) hf_initial =
    sample.product_submit (\<lambda>_ _ _. True) 7 (7,1) (payload_envelope prp_original_payload) hf_initial"
    by (rule sample.authorized_current_entry_uses_actual_submission)
      (rule pro_reserve_uses_the_actual_reference_grant, rule TrueI,
       rule pro_reserve_is_registered_and_admitted_without_a_lock_token(2))
  have registered_entry: "sample.lock_product_step (reference_permitted_at (pro_inputs 9)) (\<lambda>_ _ _ _. True)
      ({7}::nat set) {0,2}
      (Lock_Submit Normal_Lock_Entry 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) None) hf_initial =
      sample.submit_lock_entry (reference_permitted_at (pro_inputs 9)) (\<lambda>_ _ _ _. True)
        Normal_Lock_Entry 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) (None::product_lock_credential option) hf_initial"
    by (simp only: sample.lock_product_step.simps
        pro_reserve_is_registered_and_admitted_without_a_lock_token(1) if_True; rule refl)
  have produced: "sample.lock_product_step (reference_permitted_at (pro_inputs 9)) (\<lambda>_ _ _ _. True)
      ({7}::nat set) {0,2}
      (Lock_Submit Normal_Lock_Entry 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) None) hf_initial =
      sample.product_submit (\<lambda>_ _ _. True) 7 (7,1) (payload_envelope prp_original_payload) hf_initial"
    by (rule trans[OF registered_entry entry])
  have folded: "sample.product_submit (\<lambda>_ _ _. True) 7 (7,1)
      (payload_envelope prp_original_payload) hf_initial = hf_reserved"
    by (simp only: hf_reserved_def hf_submit_def prp_original_payload_def product_call_payload.select_convs; rule refl)
  show ?thesis by (rule trans[OF produced folded])
qed

lemma pro_submit_constructs_the_entry_from_the_actual_reserve_reply:
  "pro_submitted = store_product_result (7,1) prp_original_payload pro_original_outcome hf_reserved pro_initial"
proof -
  let ?call_id = "((7,1)::client_call_id)"
  let ?permitted = "reference_permitted_at (pro_inputs 9)"
  let ?before = "outcome_source pro_initial"
  let ?calls = "product_calls ?before"
  have source: "?before = hf_initial"
    by (simp add: pro_initial_def initial_outcome_world_def)
  have empty: "outcome_entries pro_initial ?call_id = None"
    by (simp add: pro_initial_def initial_outcome_world_def)
  have access: "result_access_bound pro_verified 7 ?call_id prp_original_payload pro_initial"
    unfolding result_access_bound_def
  proof (rule conjI)
    show "pro_verified 7 ?call_id prp_original_payload"
      unfolding pro_verified_def by (rule TrueI)
    show "product_identity_bound 7 ?call_id (payload_envelope prp_original_payload) ?before"
      unfolding source
      by (rule pro_reserve_identity_is_bound_before_and_after_submission(1))
  qed
  have submit:
    "pro_submitted = sample.submit_new_authoritative_call ?permitted ({7}::nat set) {0,2}
      Normal_Lock_Entry 7 ?call_id prp_original_payload pro_initial"
    unfolding pro_submitted_def sample.submit_authoritative_call_def
    by (rule if_P) (rule conjI[OF access empty])
  have fresh: "(call_invocations ?calls ?call_id \<noteq> None \<or>
      call_authority_results ?calls ?call_id \<noteq> None \<or>
      call_local_status ?calls \<noteq> Endpoint_Up) = False"
    by (simp add: source hf_initial_call_machine initial_call_machine_def)
  have connected: "(call_connection ?calls \<noteq> Authority_Connected) = False"
    by (simp add: source hf_initial_call_machine initial_call_machine_def)
  have source_step:
    "sample.lock_product_step ?permitted (\<lambda>_ _ _ _. True) ({7}::nat set) {0,2}
      (Lock_Submit Normal_Lock_Entry 7 ?call_id (payload_envelope prp_original_payload)
        (payload_credential prp_original_payload)) ?before = hf_reserved"
    unfolding source pro_original_reserve_has_no_lock_token by (rule pro_actual_lock_entry_is_the_checked_reserve)
  show ?thesis
    unfolding submit sample.submit_new_authoritative_call_def Let_def
    by (simp only: fresh connected if_False source_step prp_original_cache_entry_is_computed_by_reserve
        option.case case_prod_conv pro_original_outcome_def)
qed

lemma pro_submitted_source_and_entry_are_actual:
  "outcome_source pro_submitted = hf_reserved"
  "outcome_entries pro_submitted (7,1) = Some pro_original_entry"
  "outcome_completed pro_submitted = {}"
  by (simp_all add: pro_submit_constructs_the_entry_from_the_actual_reserve_reply
      store_product_result_def pro_original_entry_def pro_initial_def initial_outcome_world_def)

lemma pro_original_reserve_result_needs_no_terminal_publication_to_be_read:
  "result_completion_ready pro_original_entry m_outcomes"
  by (simp add: result_completion_ready_def pro_original_entry_def prp_original_payload_def
      hf_envelope_def hf_reserve_def Let_def)

lemma pro_reserved_endpoint_is_up:
  "call_local_status (product_calls hf_reserved) = Endpoint_Up"
  unfolding prp_actual_reserved_call_machine
  by (rule sample.finality_calls.initial_dispatch_projection(6))

lemma pro_reserved_result_access_is_bound:
  assumes source: "outcome_source m_outcomes = hf_reserved"
  shows "result_access_bound pro_verified 7 ((7,1)::client_call_id) prp_original_payload m_outcomes"
  unfolding result_access_bound_def source
proof (rule conjI)
  show "pro_verified 7 ((7,1)::client_call_id) prp_original_payload"
    unfolding pro_verified_def by (rule TrueI)
  show "product_identity_bound 7 ((7,1)::client_call_id) (payload_envelope prp_original_payload) hf_reserved"
    by (rule pro_reserve_identity_is_bound_before_and_after_submission(2))
qed

lemma pro_submitted_result_access_is_bound:
  "result_access_bound pro_verified 7 ((7,1)::client_call_id) prp_original_payload pro_submitted"
  by (rule pro_reserved_result_access_is_bound[OF pro_submitted_source_and_entry_are_actual(1)])

lemma pro_exact_stored_result_is_read_from_the_actual_entry:
  "read_authoritative_result pro_verified 7 ((7,1)::client_call_id) prp_original_payload pro_submitted = Some pro_original_outcome"
proof -
  have exact: "result_payload pro_original_entry = prp_original_payload"
    by (simp add: pro_original_entry_def)
  have ready: "result_completion_ready pro_original_entry pro_submitted"
    by (rule pro_original_reserve_result_needs_no_terminal_publication_to_be_read)
  have actual: "read_authoritative_result pro_verified 7 ((7,1)::client_call_id) prp_original_payload pro_submitted =
      Some (result_outcome pro_original_entry)"
    by (rule exact_retry_reads_the_committed_outcome[OF pro_submitted_result_access_is_bound
        pro_submitted_source_and_entry_are_actual(2) exact ready])
  show ?thesis using actual by (simp add: pro_original_entry_def)
qed

lemma pro_fresh_completion_only_marks_the_actual_completed_identifier:
  "complete_authoritative_result pro_verified 7 ((7,1)::client_call_id) prp_original_payload pro_submitted =
    (pro_submitted\<lparr>outcome_completed := {(7,1)}\<rparr>, Some pro_original_outcome)"
  unfolding complete_authoritative_result_def pro_submitted_source_and_entry_are_actual(1,3)
    pro_reserved_endpoint_is_up pro_exact_stored_result_is_read_from_the_actual_entry
  by simp

lemma pro_completed_updates_only_the_marker:
  "pro_completed = pro_submitted\<lparr>outcome_completed := {(7,1)}\<rparr>"
  unfolding pro_completed_def pro_fresh_completion_only_marks_the_actual_completed_identifier
  by simp

lemma pro_completed_retains_the_produced_source_and_entry:
  "outcome_source pro_completed = hf_reserved"
  "outcome_entries pro_completed (7,1) = Some pro_original_entry"
  "outcome_completed pro_completed = {(7,1)}"
proof -
  have source: "outcome_source pro_completed = outcome_source pro_submitted"
    unfolding pro_completed_updates_only_the_marker by simp
  have entries: "outcome_entries pro_completed = outcome_entries pro_submitted"
    unfolding pro_completed_updates_only_the_marker by simp
  show "outcome_source pro_completed = hf_reserved"
    unfolding source by (rule pro_submitted_source_and_entry_are_actual(1))
  show "outcome_entries pro_completed (7,1) = Some pro_original_entry"
    unfolding entries by (rule pro_submitted_source_and_entry_are_actual(2))
  show "outcome_completed pro_completed = {(7,1)}"
    unfolding pro_completed_updates_only_the_marker by simp
qed

thm_oracles pro_submit_constructs_the_entry_from_the_actual_reserve_reply
  pro_fresh_completion_only_marks_the_actual_completed_identifier
  pro_completed_retains_the_produced_source_and_entry

ML \<open>
  if null (Thm_Deps.all_oracles @{thms pro_submit_constructs_the_entry_from_the_actual_reserve_reply
      pro_fresh_completion_only_marks_the_actual_completed_identifier
      pro_completed_retains_the_produced_source_and_entry})
  then writeln "P13_STORED_OUTCOME_CONSTRUCTION_ORACLES_EMPTY"
  else error "Unexpected oracle in stored outcome construction"
\<close>

end

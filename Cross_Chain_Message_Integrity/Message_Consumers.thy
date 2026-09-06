(* SPDX-License-Identifier: BSD-3-Clause *)
theory Message_Consumers
  imports Message_Examples
begin

section \<open>Regulatory Permission Consumers\<close>

context source_attestation
begin

definition regulatory_permission :: "execution_context \<Rightarrow> execution_request \<Rightarrow> bool
  \<Rightarrow> reg_state \<Rightarrow> bool" where
  "regulatory_permission c r restriction state =
    (case binding_operation (request_binding r) of
       Ordinary_Transfer_Effect \<Rightarrow>
         transfer_allowed state \<lparr>transfer_path_value = Ordinary_Transfer,
           baseline_clear = authenticated_request c r, restriction_clear = restriction,
           enforcement_approved = False\<rparr>
     | Enforcement_Transfer_Effect kind \<Rightarrow>
         transfer_allowed state \<lparr>transfer_path_value = Authorized_Enforcement kind,
           baseline_clear = False, restriction_clear = restriction,
           enforcement_approved = authenticated_request c r\<rparr>
     | _ \<Rightarrow> False)"

theorem ordinary_permission_uses_authenticated_evidence:
  assumes "binding_operation (request_binding r) = Ordinary_Transfer_Effect"
  shows "regulatory_permission c r restriction state \<longleftrightarrow>
    authenticated_request c r \<and> regulatory_state_gate state restriction"
  using assms ordinary_transfer_uses_both_gates
  by (simp add: regulatory_permission_def)

theorem enforcement_permission_uses_authenticated_action:
  assumes "binding_operation (request_binding r) = Enforcement_Transfer_Effect kind"
  shows "regulatory_permission c r restriction state \<longleftrightarrow>
    authenticated_request c r \<and> enforcement_transfer_action kind"
  using assms enforcement_transfer_is_a_separate_path
  by (simp add: regulatory_permission_def)

theorem regulatory_permission_has_source_and_current_authority:
  assumes permitted: "regulatory_permission c r restriction state"
  shows "current_use_allowed c r \<and>
    stable_source (binding_key (request_binding r)) =
      Some \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
proof -
  have authenticated: "authenticated_request c r"
    using permitted
    by (cases "binding_operation (request_binding r)")
       (auto simp: regulatory_permission_def transfer_allowed_def ordinary_transfer_allowed_def)
  show ?thesis using request_has_stable_binding[OF authenticated] authenticated
    unfolding authenticated_request_def by blast
qed

end

definition unchecked_regulatory_permission :: "execution_request \<Rightarrow> bool \<Rightarrow> reg_state
  \<Rightarrow> bool" where
  "unchecked_regulatory_permission r restriction state =
    (case binding_operation (request_binding r) of
       Ordinary_Transfer_Effect \<Rightarrow> ordinary_transfer_allowed True restriction state
     | Enforcement_Transfer_Effect kind \<Rightarrow>
         transfer_allowed state \<lparr>transfer_path_value = Authorized_Enforcement kind,
           baseline_clear = False, restriction_clear = restriction, enforcement_approved = True\<rparr>
     | _ \<Rightarrow> False)"

lemma example_regulatory_requests_authenticated:
  "event \<in> {18,19,20,21} \<Longrightarrow>
    example.authenticated_request example_context (example_request event)"
  unfolding example.authenticated_request_def example.certificate_ok_def current_use_allowed_def
  by (auto simp: example_request_def example_certificate_def example_statement_def example_binding_def
      example_context_def example_roster_def example_threshold_def example_verifies_def
      example_signed_def example_truth_def)

lemma regulatory_consumer_positive_and_negative:
  "example.regulatory_permission example_context (example_request 18) True ACTIVE \<and>
   \<not> example.regulatory_permission example_context (example_request 18) True FROZEN \<and>
   example.regulatory_permission example_context (example_request 19) True FROZEN"
  using example_regulatory_requests_authenticated[of 18]
        example_regulatory_requests_authenticated[of 19]
  by (simp add: example.regulatory_permission_def example_request_def example_binding_def
      transfer_allowed_def ordinary_transfer_allowed_def)

lemma current_authority_consumer_removal:
  "\<not> example.regulatory_permission example_context
      ((example_request 19)\<lparr>request_authority_epoch := 7\<rparr>) True FROZEN \<and>
   unchecked_regulatory_permission
      ((example_request 19)\<lparr>request_authority_epoch := 7\<rparr>) True FROZEN"
  unfolding example.regulatory_permission_def example.authenticated_request_def current_use_allowed_def
    unchecked_regulatory_permission_def
  by (simp add: example_request_def example_binding_def example_context_def transfer_allowed_def)

lemma current_read_role_is_independent:
  "current_read_allowed example_context 8 4 \<and>
   \<not> current_use_allowed example_context ((example_request 17)\<lparr>request_caller := 8\<rparr>)
     \<and>
   \<not> current_read_allowed example_context 8 3"
  by (simp add: current_read_allowed_def current_use_allowed_def example_context_def example_request_def)

section \<open>A Completed Regulatory Synchronization Consumer\<close>

record regulatory_receiver =
  receiver_snapshot :: global_state
  receiver_applied :: "source_key set"

context source_attestation
begin

definition apply_regulatory_message :: "execution_context \<Rightarrow> execution_request \<Rightarrow>
  regulatory_receiver \<Rightarrow> regulatory_receiver option" where
  "apply_regulatory_message c r s =
    (if \<not> authenticated_request c r \<or> binding_key (request_binding r) \<in> receiver_applied s
     then None
     else case binding_operation (request_binding r) of
       Regulatory_State_Effect action \<Rightarrow>
         (case sync (fst (binding_key (request_binding r))) action
           (binding_asset (request_binding r)) (receiver_snapshot s) of
           None \<Rightarrow> None
         | Some snapshot \<Rightarrow> Some (s\<lparr>receiver_snapshot := snapshot,
             receiver_applied := insert (binding_key (request_binding r)) (receiver_applied s)\<rparr>))
     | _ \<Rightarrow> None)"

theorem accepted_regulatory_message_is_source_bound:
  assumes "apply_regulatory_message c r s = Some t"
  shows "stable_source (binding_key (request_binding r)) =
    Some \<lparr>statement_binding = request_binding r, statement_status = Finalized\<rparr>"
  using assms request_has_stable_binding
  by (auto simp: apply_regulatory_message_def split: if_splits message_operation.splits option.splits)

theorem completed_regulatory_message_preserves_cdsp:
  assumes before: "valid_state (receiver_snapshot s)"
    and applied: "apply_regulatory_message c r s = Some t"
  shows "valid_state (receiver_snapshot t)"
proof -
  obtain action snapshot where sync:
    "sync (fst (binding_key (request_binding r))) action
      (binding_asset (request_binding r)) (receiver_snapshot s) = Some snapshot"
    and after: "receiver_snapshot t = snapshot"
    using applied
    by (auto simp: apply_regulatory_message_def split: if_splits message_operation.splits option.splits)
  obtain prior post_state where prior:
    "get_reg_state (receiver_snapshot s) (fst (binding_key (request_binding r)))
      (binding_asset (request_binding r)) = Some prior"
    and transition: "reg_transition prior action = Some post_state"
    using sync by (auto simp: sync_def split: option.splits)
  have "valid_state snapshot" using valid_state_preservation[OF before prior transition sync] .
  then show ?thesis using after by simp
qed

theorem repeated_regulatory_source_is_rejected:
  assumes "apply_regulatory_message c r s = Some t"
  shows "apply_regulatory_message c' r t = None"
  using assms
  by (auto simp: apply_regulatory_message_def split: if_splits message_operation.splits option.splits)

end

definition example_snapshot :: "reg_state \<Rightarrow> global_state" where
  "example_snapshot state =
    \<lparr>gs_chains = (\<lambda>chain asset. if chain \<in> {0,2} \<and> asset = 20
      then Some \<lparr>as_reg_state = state\<rparr> else None), gs_locks = (\<lambda>_. False)\<rparr>"

lemma example_snapshot_valid:
  "valid_state (example_snapshot state)"
  by (auto simp: example_snapshot_def valid_state_def consistent_state_def no_locked_without_reason_def
      get_reg_state_def get_asset_state_def is_locked_def split: if_splits)

lemma example_completed_freeze:
  "example.apply_regulatory_message example_context (example_request 20)
    \<lparr>receiver_snapshot = example_snapshot ACTIVE, receiver_applied = {}\<rparr> =
    Some \<lparr>receiver_snapshot = example_snapshot FROZEN, receiver_applied = {(0,20)}\<rparr>"
  using example_regulatory_requests_authenticated[of 20]
  unfolding example.apply_regulatory_message_def
  by (simp add: example_request_def example_binding_def sync_def example_snapshot_def
      get_reg_state_def get_asset_state_def acquire_lock_def is_locked_def
      connected_chains_def asset_exists_def update_all_chains_def release_lock_def Let_def fun_eq_iff)

lemma example_completed_freeze_is_valid:
  "valid_state (example_snapshot FROZEN)"
proof -
  have "valid_state (receiver_snapshot
    (\<lparr>receiver_snapshot = example_snapshot FROZEN,
      receiver_applied = {(0,20)}\<rparr> :: regulatory_receiver))"
    by (rule example.completed_regulatory_message_preserves_cdsp[OF _ example_completed_freeze])
       (simp add: example_snapshot_valid)
  then show ?thesis by simp
qed

text \<open>This consumer uses CDSP only for completed atomic regulatory steps
  over a persistent metadata footprint. It neither identifies token balances
  with regulatory holdings nor establishes asynchronous atomicity. The transfer
  permission consumer and the state-update consumer use different operation
  constructors, while sharing source authentication and current-use checks.\<close>

end

theory Reference_Legal_Code
  imports "OIP_Reference_Profile.Reference_Confiscation_Consumption"
begin

definition native_confiscation_gate where
  "native_confiscation_gate order source_mode receiver_mode seizure now =
    (if source_mode = None \<or> source_mode \<noteq> receiver_mode
      then Legal_Refuse Invalid_Legal_State
     else case seizure of None \<Rightarrow> Legal_Refuse Missing_Prior_Seizure
       | Some (key, recorded_deadline) \<Rightarrow>
         if source_mode \<noteq> Some SEIZED \<or> legal_predecessor order \<noteq> Some key
         then Legal_Refuse Missing_Prior_Seizure
         else case legal_appeal_deadline order of None \<Rightarrow> Legal_Refuse Appeal_Deadline_Mismatch
           | Some deadline \<Rightarrow>
             if recorded_deadline \<noteq> Some deadline then Legal_Refuse Appeal_Deadline_Mismatch
             else if now < deadline then Legal_Refuse Appeal_Still_Open
             else if legal_destination order = None then Legal_Refuse Missing_Confiscation_Destination
             else Legal_Admit)"

theorem the_native_confiscation_gate_matches_the_exact_current_legal_state:
  assumes action: "legal_action order = CONFISCATE"
    and source: "source_mode = legal_current_state state (fst (legal_origin order)) (legal_asset order)"
    and configured: "source_mode \<noteq> None" "receiver_mode = source_mode"
    and time: "now = legal_clock state"
    and exact_seizure: "(\<exists>key deadline. seizure = Some (key, deadline) \<and> legal_predecessor order = Some key)
      \<longleftrightarrow> exact_legal_predecessor state order (active_seizure_event state (legal_asset order)) SEIZE"
    and exact_appeal: "\<And>key deadline. seizure = Some (key, deadline) \<Longrightarrow>
      legal_predecessor order = Some key \<Longrightarrow> deadline = recorded_appeal_deadline state (legal_asset order)"
  shows "native_confiscation_gate order source_mode receiver_mode seizure now = legal_state_gate state order"
  using assms
  by (cases seizure)
     (auto simp: native_confiscation_gate_def legal_state_gate_def matching_appeal_deadline_def appeal_has_elapsed_def Let_def
        split: prod.splits option.splits if_splits)

lemma inconsistent_source_and_receiver_modes_fail_the_native_gate:
  assumes "source_mode \<noteq> receiver_mode"
  shows "native_confiscation_gate order source_mode receiver_mode seizure now = Legal_Refuse Invalid_Legal_State"
  using assms by (simp add: native_confiscation_gate_def)

lemma a_different_deadline_or_early_time_cannot_admit_the_native_order:
  assumes "seizure = Some (key, recorded)" "legal_appeal_deadline order = Some supplied"
    "recorded \<noteq> Some supplied \<or> now < supplied"
  shows "native_confiscation_gate order source_mode receiver_mode seizure now \<noteq> Legal_Admit"
  using assms by (auto simp: native_confiscation_gate_def split: if_splits)

record rust_regulation_image =
  rust_legal_modes :: "(nat \<times> nat) \<Rightarrow> reg_state option"
  rust_legal_clock :: nat
  rust_legal_seizures :: "nat \<Rightarrow> (source_key \<times> nat option) option"
  rust_legal_source_units :: "source_account \<Rightarrow> nat"
  rust_legal_destination_units :: "destination_account \<Rightarrow> nat"

definition rust_regulation_matches where
  "rust_regulation_matches code spec \<longleftrightarrow>
    (\<forall>domain asset. rust_legal_modes code (domain,asset) = legal_current_state spec domain asset) \<and>
    rust_legal_clock code = legal_clock spec \<and>
    rust_legal_source_units code = source_units (machine_state (core_parent (legal_current_core spec))) \<and>
    rust_legal_destination_units code = destination_units (machine_state (core_parent (legal_current_core spec)))"

definition rust_confiscate_admission where
  "rust_confiscate_admission code order receiver =
    (case native_confiscation_gate order (rust_legal_modes code (fst (legal_origin order), legal_asset order))
      (rust_legal_modes code (receiver, legal_asset order)) (rust_legal_seizures code (legal_asset order)) (rust_legal_clock code) of
      Legal_Refuse reason \<Rightarrow> Some (code, Legal_Blocked reason) | Legal_Admit \<Rightarrow> None)"

context source_attestation
begin

theorem early_confiscation_refines_the_actual_legal_refusal_and_preserves_the_related_image:
  assumes related: "rust_regulation_matches code spec"
    and confiscation: "legal_action order = CONFISCATE"
    and modes: "legal_current_state spec (fst (legal_origin order)) (legal_asset order) = Some SEIZED"
      "legal_current_state spec receiver (legal_asset order) = Some SEIZED"
    and seizure: "rust_legal_seizures code (legal_asset order) = Some (key, Some deadline)"
      "legal_predecessor order = Some key"
      "exact_legal_predecessor spec order (active_seizure_event spec (legal_asset order)) SEIZE"
    and deadline: "legal_appeal_deadline order = Some deadline" "recorded_appeal_deadline spec (legal_asset order) = Some deadline"
      "legal_clock spec < deadline"
    and authority: "order_verified stage entry who order" "legal_officer order = who" "legal_basis order \<noteq> 0"
      "legal_asset order \<in> legal_scope order"
      "legal_grant stage entry who (legal_jurisdiction order) (legal_asset order) CONFISCATE
          (cut_authority_epoch (legal_current_cut spec))"
    and issuance: "case stage of Legal_Source_Emission \<Rightarrow>
         legal_issuance_epoch order = cut_authority_epoch (legal_current_cut spec) \<and>
         issued_legal_orders spec (legal_origin order) \<in> {None, Some order}
       | Legal_Receiving_Commit \<Rightarrow> issued_legal_orders spec (legal_origin order) = Some order"
  shows "let model = run_legal_effect legal_grant order_verified permitted verified maintainers registered verified_ack
      stage entry who expected call_id order payload spec
    in rust_confiscate_admission code order receiver = Some (code, snd model) \<and>
       rust_regulation_matches code (fst model) \<and> snd model = Legal_Blocked Appeal_Still_Open"
proof -
  have matching: "matching_appeal_deadline spec order"
    by (simp add: matching_appeal_deadline_def deadline)
  have early: "legal_state_gate spec order = Legal_Refuse Appeal_Still_Open"
    by (rule premature_confiscation_gets_appeal_refusal[OF confiscation modes(1) seizure(3) matching deadline(1,3)])
  have admit: "legal_admission_at_cut legal_grant order_verified stage entry who order spec = Legal_Refuse Appeal_Still_Open"
    using authority confiscation issuance early
    by (cases stage) (simp_all add: legal_admission_at_cut_def)
  have native: "rust_confiscate_admission code order receiver = Some (code,Legal_Blocked Appeal_Still_Open)"
    using related modes seizure deadline
    by (simp add: rust_confiscate_admission_def rust_regulation_matches_def native_confiscation_gate_def)
  show ?thesis using native related admit by (simp add: run_legal_effect_def Let_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_native_confiscation_gate_matches_the_exact_current_legal_state
      inconsistent_source_and_receiver_modes_fail_the_native_gate
      a_different_deadline_or_early_time_cannot_admit_the_native_order
      source_attestation.early_confiscation_refines_the_actual_legal_refusal_and_preserves_the_related_image})
  then () else error "Unexpected oracle in native confiscation gate correspondence"
\<close>

end

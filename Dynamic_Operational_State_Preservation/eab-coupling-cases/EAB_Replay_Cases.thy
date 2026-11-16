theory EAB_Replay_Cases
  imports EAB_Dynamic_Cases Evidence_Binding_Composition.Funding_Completion_Separation
begin

lemma replay_fixture_attestation:
  "source_attestation example_roster example_faulty example_bound example_threshold
    (source_receipt_verifies realization_receipts) (source_receipt_signed realization_receipts)
    (controlled_produced_fact sample_balances realization_source_commands)
    (controlled_stable_source sample_balances realization_source_commands)"
  unfolding realization_receipts_def by (rule source_receipts_interpret_source_attestation)

abbreviation replay_fixture_step where
  "replay_fixture_step \<equiv> source_attestation.replayed_receipt_repair example_roster example_threshold
    (source_receipt_verifies realization_receipts)"

lemmas replay_fixture_step_def = source_attestation.replayed_receipt_repair_def[OF replay_fixture_attestation]

abbreviation actual_durable_core :: finality_core where
  "actual_durable_core \<equiv> coupled_core (observation_source (call_authority_state realization_durable_calls))"

definition two_transfer_authority :: eab_primary_authority where
  "two_transfer_authority = \<lparr>terminal_authority = actual_durable_core,
    publication_slots = (\<lambda>seq. if seq = 50 then Some (0, 17) else if seq = 51 then Some (0, 23) else None)\<rparr>"

definition two_transfer_repair :: "nat recovery_state" where
  "two_transfer_repair =
    repair_fixture\<lparr>irreversible_facts := {prod_encode (0, 17), prod_encode (0, 23)}\<rparr>"

lemma durable_source_has_both_native_publications:
  "core_published actual_durable_core = {(0, 17), (0, 23)}"
  using actual_durable_calls_have_the_realized_joint_source separation_exchange_frames(2)
    realization_seed_actual_step realization_two_roots_supply_the_actual_consumers by metis

lemma durable_source_has_the_matching_transfer:
  "published_transfer_receipt (0, 17) 50 actual_durable_core = Some fixture_receipt"
proof -
  have reference: "record_reference actual_durable_core 0 (sample_binding 17) Confirmed_Decision \<noteq> None"
    using actual_durable_calls_have_the_realized_joint_source
      separation_source_inputs(3)[of realization_exchange_finished] by simp
  obtain terminal where at: "core_records actual_durable_core (0, 17) = Some terminal"
    and fields: "terminal_binding terminal = sample_binding 17" "terminal_kind terminal = Confirmed_Decision"
    using reference by (auto simp: record_reference_def fixture_binding split: option.splits if_splits)
  show ?thesis using at fields durable_source_has_both_native_publications
    by (simp add: published_transfer_receipt_def fixture_receipt_def fixture_binding)
qed

lemma current_durable_word_is_replayable:
  "realized.sourced_calls.checked_current_replay realization_durable_calls
      (current_source_candidate realization_durable_calls) = Some (call_authority_state realization_durable_calls)"
  unfolding realization_durable_calls_def realization_call_initial_def
  by (rule realized.sourced_calls.generated_source_supplies_recovery_without_a_truth_flag)

theorem actual_current_journal_drives_the_replica_install:
  "replay_fixture_step {} {} two_transfer_authority fixture_receipt
    realization_durable_calls (current_source_candidate realization_durable_calls)
    two_transfer_repair (Apply_Repair 8 50) (transition_result.Accepted (Installed 8 2 50))
    (install_replica two_transfer_repair 8 2)"
proof -
  have aligned: "terminal_authority two_transfer_authority = actual_durable_core"
    by (simp add: two_transfer_authority_def)
  have bound: "primary_receipt_matches two_transfer_authority fixture_receipt two_transfer_repair"
    using durable_source_has_both_native_publications durable_source_has_the_matching_transfer
    by (simp add: primary_receipt_matches_def two_transfer_authority_def two_transfer_repair_def
        repair_fixture_def fixture_receipt_def)
  have raw: "recovery_step {} {} two_transfer_repair (Apply_Repair 8 50)
      (transition_result.Accepted (Installed 8 2 50)) (install_replica two_transfer_repair 8 2)"
    by (rule recovery_step.Ordinary_Repair) (simp_all add: two_transfer_repair_def repair_fixture_def)
  have install: "receipt_repair_step {} {} two_transfer_authority fixture_receipt two_transfer_repair (Apply_Repair 8 50)
      (transition_result.Accepted (Installed 8 2 50)) (install_replica two_transfer_repair 8 2)"
    using bound raw by (simp add: receipt_repair_step_def)
  show ?thesis
    unfolding replay_fixture_step_def current_durable_word_is_replayable
    using install by (simp add: aligned)
qed

lemma a_stripped_real_journal_cannot_complete_that_repair:
  defines "current \<equiv> realization_durable_calls"
  shows "\<not> replay_fixture_step {} {} two_transfer_authority fixture_receipt
    current ((current_source_candidate current)\<lparr>candidate_entries := []\<rparr>)
    two_transfer_repair (Apply_Repair 8 50) (transition_result.Accepted (Installed 8 2 50))
    (install_replica two_transfer_repair 8 2)"
proof -
  have contract: "realized.sourced_calls.authority_replay_contract current"
    unfolding current_def realization_durable_calls_def realization_call_initial_def
    using realized.sourced_calls.generated_call_contracts by blast
  have nonempty: "call_authority_log current \<noteq> []"
  proof
    assume empty: "call_authority_log current = []"
    have "call_authority_state current = call_genesis current"
      using contract empty by (simp add: realized.sourced_calls.authority_replay_contract_def)
    then show False
      using durable_source_has_both_native_publications
      by (simp add: current_def realization_durable_calls_def realization_call_initial_def
        initial_call_machine_def initial_sourced_observations_def initial_source_coupling_def initial_finality_core_def Let_def)
  qed
  show ?thesis
    by (rule source_attestation.shortened_source_journal_cannot_complete_a_replica_install[OF replay_fixture_attestation])
      (simp add: nonempty)
qed

lemma the_same_replayed_journal_cannot_authorize_a_changed_publication_slot:
  "replay_fixture_step {} {} (two_transfer_authority\<lparr>publication_slots := (\<lambda>_. Some (0, 23))\<rparr>)
    fixture_receipt realization_durable_calls (current_source_candidate realization_durable_calls)
    two_transfer_repair (Apply_Repair 8 50) (transition_result.Operational_Failure Evidence_Unavailable)
    two_transfer_repair"
  using current_durable_word_is_replayable
  by (simp add: replay_fixture_step_def receipt_repair_step_def primary_receipt_matches_def fixture_receipt_def two_transfer_authority_def)

lemma a_current_journal_and_another_authority_cannot_be_combined:
  defines "old_authority \<equiv> two_transfer_authority\<lparr>terminal_authority := finality_sample_certified 17\<rparr>"
  shows "replay_fixture_step {} {} old_authority fixture_receipt
    realization_durable_calls (current_source_candidate realization_durable_calls)
    two_transfer_repair (Apply_Repair 8 50) (transition_result.Operational_Failure Evidence_Unavailable)
    two_transfer_repair"
proof -
  have not_equal: "terminal_authority old_authority \<noteq> actual_durable_core"
  proof
    assume equal: "terminal_authority old_authority = actual_durable_core"
    then have "core_published (terminal_authority old_authority) = core_published actual_durable_core" by simp
    then show False
      by (simp add: old_authority_def fixture_before_publication durable_source_has_both_native_publications)
  qed
  have reversed: "actual_durable_core \<noteq> terminal_authority old_authority"
  proof
    assume same: "actual_durable_core = terminal_authority old_authority"
    from not_equal same[symmetric] show False by contradiction
  qed
  show ?thesis
    by (simp add: replay_fixture_step_def current_durable_word_is_replayable reversed)
qed

lemma the_old_irreversible_set_cannot_authorize_a_repair_after_the_second_publication:
  "replay_fixture_step {} {} two_transfer_authority fixture_receipt
    realization_durable_calls (current_source_candidate realization_durable_calls)
    repair_fixture (Apply_Repair 8 50) (transition_result.Operational_Failure Evidence_Unavailable) repair_fixture"
  using current_durable_word_is_replayable durable_source_has_both_native_publications
  by (simp add: replay_fixture_step_def receipt_repair_step_def primary_receipt_matches_def
      repair_fixture_def two_transfer_authority_def prod_encode_eq)

abbreviation journal_after_join :: "nat recovery_state" where
  "journal_after_join \<equiv> after_join\<lparr>irreversible_facts := irreversible_facts two_transfer_repair\<rparr>"

abbreviation journal_after_handoff :: "nat recovery_state" where
  "journal_after_handoff \<equiv> after_handoff\<lparr>irreversible_facts := irreversible_facts two_transfer_repair\<rparr>"

theorem a_job_handed_to_a_new_domain_installs_from_the_current_journal:
  shows "recovery_step changing_domains {} two_transfer_repair (Activate (Join_Domain 6 9) 2 10 10)
    (transition_result.Accepted (Joined 6 9)) journal_after_join"
    and "recovery_step changing_domains {} journal_after_join (Activate (Leave_Domain 2 6) 3 11 11)
      (transition_result.Accepted (Left 2 6)) journal_after_handoff"
    and "replay_fixture_step changing_domains {} two_transfer_authority fixture_receipt
      realization_durable_calls (current_source_candidate realization_durable_calls)
      journal_after_handoff (Apply_Repair 8 50) (transition_result.Accepted (Installed 8 6 50))
      (install_replica journal_after_handoff 8 6)"
proof -
  have joined: "recovery_step changing_domains {} two_transfer_repair (Activate (Join_Domain 6 9) 2 10 10)
    (transition_result.Accepted (Joined 6 9))
    (two_transfer_repair\<lparr>active_domains := insert 6 (active_domains two_transfer_repair),
      route_epoch := 2, work_owner := (work_owner two_transfer_repair)(9 := Some 6)\<rparr>)"
    by (rule recovery_step.Join_Route)
      (simp_all add: changing_domains_def current_grant_def fresh_work_def two_transfer_repair_def repair_fixture_def)
  show join: "recovery_step changing_domains {} two_transfer_repair (Activate (Join_Domain 6 9) 2 10 10)
    (transition_result.Accepted (Joined 6 9)) journal_after_join"
    using joined by (simp add: after_join_def two_transfer_repair_def repair_fixture_def)
  have left: "recovery_step changing_domains {} journal_after_join (Activate (Leave_Domain 2 6) 3 11 11)
    (transition_result.Accepted (Left 2 6))
    (journal_after_join\<lparr>active_domains := active_domains journal_after_join - {2}, route_epoch := 3,
      work_owner := carry_owner 2 6 (work_owner journal_after_join)\<rparr>)"
    by (rule recovery_step.Leave_Route)
      (simp_all add: changing_domains_def current_grant_def after_join_def repair_fixture_def)
  show leave: "recovery_step changing_domains {} journal_after_join (Activate (Leave_Domain 2 6) 3 11 11)
    (transition_result.Accepted (Left 2 6)) journal_after_handoff"
    using left by (simp add: after_handoff_def after_join_def two_transfer_repair_def repair_fixture_def)
  have bound: "primary_receipt_matches two_transfer_authority fixture_receipt two_transfer_repair"
    using durable_source_has_both_native_publications durable_source_has_the_matching_transfer
    by (simp add: primary_receipt_matches_def two_transfer_authority_def two_transfer_repair_def
        repair_fixture_def fixture_receipt_def)
  then have "primary_receipt_matches two_transfer_authority fixture_receipt journal_after_handoff"
    using recovery_keeps_the_primary_receipt[OF join] recovery_keeps_the_primary_receipt[OF leave] by blast
  moreover have "recovery_step changing_domains {} journal_after_handoff (Apply_Repair 8 50)
      (transition_result.Accepted (Installed 8 6 50)) (install_replica journal_after_handoff 8 6)"
    by (rule recovery_step.Ordinary_Repair)
      (simp_all add: after_handoff_def after_join_def repair_fixture_def carry_owner_def)
  ultimately have "receipt_repair_step changing_domains {} two_transfer_authority fixture_receipt
      journal_after_handoff (Apply_Repair 8 50) (transition_result.Accepted (Installed 8 6 50))
      (install_replica journal_after_handoff 8 6)"
    by (simp add: receipt_repair_step_def)
  then show "replay_fixture_step changing_domains {} two_transfer_authority fixture_receipt
      realization_durable_calls (current_source_candidate realization_durable_calls)
      journal_after_handoff (Apply_Repair 8 50) (transition_result.Accepted (Installed 8 6 50))
      (install_replica journal_after_handoff 8 6)"
    unfolding replay_fixture_step_def current_durable_word_is_replayable
    by (simp add: two_transfer_authority_def)
qed

end

theory P19_Configured_Registry_G0
  imports "OIP_P19_Threshold_G0.P19_Threshold_Raw_G0"
begin

text \<open>
  The host supplies the current epoch and a roster list. A matching row is
  counted once per registration. Two identical rows are ambiguous as well.
  The selected roster is then subject to the existing shape and signature checks.
\<close>

definition p19_roster_slot :: "p19_roster \<Rightarrow> p19_slot" where
  "p19_roster_slot roster_row = (p19_deployment roster_row, p19_source roster_row,
    p19_principal roster_row, p19_group_key roster_row)"

definition p19_rows_at :: "p19_roster list \<Rightarrow> p19_slot \<times> nat \<Rightarrow> p19_roster list" where
  "p19_rows_at roster_rows requested = filter
    (\<lambda>roster_row. (p19_roster_slot roster_row, p19_epoch roster_row) = requested) roster_rows"

fun p19_unique_row :: "'a list \<Rightarrow> 'a option" where
  "p19_unique_row [] = None"
| "p19_unique_row [roster_row] = Some roster_row"
| "p19_unique_row (first_row # second_row # rest_rows) = None"

definition p19_registry_from_rows :: "(p19_slot \<Rightarrow> nat option) \<Rightarrow> p19_roster list \<Rightarrow> p19_registry" where
  "p19_registry_from_rows current_epoch roster_rows = \<lparr>
    p19_current_epoch = current_epoch,
    p19_catalogue = (\<lambda>requested. p19_unique_row (p19_rows_at roster_rows requested))\<rparr>"

lemma p19_only_row_iff:
  "p19_unique_row roster_rows = Some roster_row \<longleftrightarrow> roster_rows = [roster_row]"
  by (cases roster_rows rule: p19_unique_row.cases) auto

lemma p19_rows_at_core:
  "p19_rows_at roster_rows (p19_core_slot wire, wire_authority_epoch wire) =
    filter (\<lambda>roster_row. p19_matches_core roster_row wire) roster_rows"
  by (simp add: p19_rows_at_def p19_roster_slot_def p19_core_slot_def p19_matches_core_def)

theorem p19_selecting_configured_roster_consumes_the_unique_exact_row:
  "p19_select (p19_registry_from_rows current_epoch roster_rows) wire = Some roster_row
    \<longleftrightarrow> current_epoch (p19_core_slot wire) = Some (wire_authority_epoch wire) \<and>
       p19_rows_at roster_rows (p19_core_slot wire, wire_authority_epoch wire) = [roster_row]"
proof -
  have exact: "p19_matches_core roster_row wire"
    if rows: "p19_rows_at roster_rows (p19_core_slot wire, wire_authority_epoch wire) = [roster_row]"
  proof -
    have "roster_row \<in> set (p19_rows_at roster_rows (p19_core_slot wire, wire_authority_epoch wire))"
      using rows by simp
    then show ?thesis by (simp add: p19_rows_at_core)
  qed
  show ?thesis using exact
    by (auto simp: p19_select_def p19_registry_from_rows_def p19_only_row_iff split: option.splits if_splits)
qed

fun p19_first_row :: "'a list \<Rightarrow> 'a option" where
  "p19_first_row [] = None"
| "p19_first_row (roster_row # rest_rows) = Some roster_row"

definition p19_registry_without_ambiguity_guard where
  "p19_registry_without_ambiguity_guard current_epoch roster_rows =
    (p19_registry_from_rows current_epoch roster_rows)\<lparr>
      p19_catalogue := (\<lambda>requested. p19_first_row (p19_rows_at roster_rows requested))\<rparr>"

lemma p19_configured_row_witnesses:
  "p19_select (p19_registry_from_rows (\<lambda>_. Some 6) [p19_test_roster]) p19_test_core = Some p19_test_roster"
  "p19_select (p19_registry_from_rows (\<lambda>_. Some 5) [p19_test_roster]) p19_test_core = None"
  "p19_select (p19_registry_from_rows (\<lambda>_. Some 6) [p19_test_roster,p19_test_roster]) p19_test_core = None"
  "p19_select (p19_registry_without_ambiguity_guard (\<lambda>_. Some 6)
    [p19_test_roster,p19_test_roster]) p19_test_core = Some p19_test_roster"
  by (simp_all add: p19_select_def p19_registry_from_rows_def p19_registry_without_ambiguity_guard_def
      p19_rows_at_def p19_roster_slot_def p19_core_slot_def p19_matches_core_def
      p19_test_roster_def p19_test_core_def)

theorem p19_removing_only_ambiguity_refusal_changes_threshold_acceptance:
  "\<not> p19_threshold_ok (\<lambda>_. True) p19_symbolic_strict
     (p19_registry_from_rows (\<lambda>_. Some 6) [p19_test_roster,p19_test_roster])
     4096 p19_test_core (p19_payload_bytes p19_good_votes)"
  "p19_threshold_ok (\<lambda>_. True) p19_symbolic_strict
     (p19_registry_without_ambiguity_guard (\<lambda>_. Some 6) [p19_test_roster,p19_test_roster])
     4096 p19_test_core (p19_payload_bytes p19_good_votes)"
  using p19_configured_row_witnesses p19_distinct_key_positive p19_good_raw_payload_roundtrip
  by (simp_all add: p19_threshold_ok_def)

definition p19_single_valid_vote :: p19_votes where
  "p19_single_valid_vote = [(1,replicate 64 31)]"

definition p19_without_vote_quorum where
  "p19_without_vote_quorum key_ok strict registry cap wire raw \<longleftrightarrow>
    (case p19_select registry wire of None \<Rightarrow> False | Some roster_row \<Rightarrow>
       p19_roster_ok key_ok roster_row \<and>
       (case p19_decode_payload cap (length (p19_members roster_row)) raw of
         None \<Rightarrow> False | Some votes \<Rightarrow>
           p19_votes_ok strict (roster_row\<lparr>p19_quorum := 0\<rparr>) (envelope_signing_bytes wire) votes))"

lemma p19_single_vote_exact_decode:
  "p19_decode_payload 4096 2 (p19_payload_bytes p19_single_valid_vote) = Some p19_single_valid_vote"
  by (rule p19_decode_encoded_payload) (auto simp: p19_single_valid_vote_def wire_octets_def)

theorem p19_removing_only_vote_quorum_changes_threshold_acceptance:
  "\<not> p19_threshold_ok (\<lambda>_. True) p19_symbolic_strict (p19_test_registry p19_test_roster)
     4096 p19_test_core (p19_payload_bytes p19_single_valid_vote)"
  "p19_without_vote_quorum (\<lambda>_. True) p19_symbolic_strict (p19_test_registry p19_test_roster)
     4096 p19_test_core (p19_payload_bytes p19_single_valid_vote)"
proof -
  have refused: "\<not> p19_votes_ok p19_symbolic_strict p19_test_roster
      (envelope_signing_bytes p19_test_core) p19_single_valid_vote"
    by (simp add: p19_votes_ok_def p19_single_valid_vote_def p19_test_roster_def)
  have admitted: "p19_votes_ok p19_symbolic_strict (p19_test_roster\<lparr>p19_quorum := 0\<rparr>)
      (envelope_signing_bytes p19_test_core) p19_single_valid_vote"
    by (simp add: p19_votes_ok_def p19_single_valid_vote_def p19_test_roster_def
        p19_symbolic_strict_def wire_octets_def)
  show "\<not> p19_threshold_ok (\<lambda>_. True) p19_symbolic_strict (p19_test_registry p19_test_roster)
      4096 p19_test_core (p19_payload_bytes p19_single_valid_vote)"
    using p19_single_vote_exact_decode p19_positive_selected_roster refused
    by (simp add: p19_threshold_ok_def)
  show "p19_without_vote_quorum (\<lambda>_. True) p19_symbolic_strict (p19_test_registry p19_test_roster)
      4096 p19_test_core (p19_payload_bytes p19_single_valid_vote)"
    using p19_single_vote_exact_decode p19_distinct_key_positive(1) p19_positive_selected_roster admitted
    by (simp add: p19_without_vote_quorum_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms p19_selecting_configured_roster_consumes_the_unique_exact_row
    p19_configured_row_witnesses p19_removing_only_ambiguity_refusal_changes_threshold_acceptance
    p19_removing_only_vote_quorum_changes_threshold_acceptance})
  then () else error "Unexpected oracle in configured threshold registration"
\<close>

end

theory Reference_Source_Reader_Code
  imports Reference_Source_Freshness
begin

record ('origin, 'decision, 'binding, 'digest) rust_source_state =
  rust_source_binding :: 'binding
  rust_source_reservation :: "(nat \<times> 'digest) option"
  rust_source_decisions :: "('origin \<times> 'decision) list"

datatype ('origin, 'decision, 'binding, 'digest) rust_source_witness =
    Rust_Source_Missing
  | Rust_Source_Initializing
  | Rust_Source_Selected "('origin, 'decision, 'binding, 'digest) rust_source_state" "nat \<times> 'digest"
  | Rust_Source_Appending
  | Rust_Source_Repairing

definition rust_source_state_valid where
  "rust_source_state_valid registered verified stored \<longleftrightarrow>
    rust_source_binding stored = registered \<and>
    ((rust_source_decisions stored = []) = (rust_source_reservation stored = None)) \<and>
    (\<forall>mark. rust_source_reservation stored = Some mark \<longrightarrow> 0 < fst mark) \<and>
    sorted_wrt (<) (map fst (rust_source_decisions stored)) \<and>
    (\<forall>(key,decision) \<in> set (rust_source_decisions stored). verified key decision)"

fun rust_selected_source_view where
  "rust_selected_source_view (Rust_Source_Selected state mark) = Some (map_of (rust_source_decisions state))"
| "rust_selected_source_view _ = None"

definition read_rust_source_decision where
  "read_rust_source_decision decode encode hash registered verified revision bytes witness origin =
     (case decode bytes of None \<Rightarrow> None | Some journal \<Rightarrow>
       if \<not> rust_source_state_valid registered verified journal \<or> encode journal \<noteq> bytes then None
       else case witness of Rust_Source_Selected selected mark \<Rightarrow>
         if mark = (revision,hash bytes) \<and> 0 < fst mark \<and> journal = selected
         then map_of (rust_source_decisions journal) origin else None
       | _ \<Rightarrow> None)"

lemma a_valid_source_record_has_a_verified_decision_at_every_selected_origin:
  assumes "rust_source_state_valid registered verified state"
    "map_of (rust_source_decisions state) origin = Some decision"
  shows "verified origin decision"
  using assms map_of_SomeD
  by (fastforce simp: rust_source_state_valid_def)

theorem every_successful_rust_source_read_at_the_exact_mark_refines_the_selected_vote:
  assumes raw: "read_rust_source_decision decode encode hash registered verified revision bytes witness origin = Some decision"
    and related: "rust_selected_source_view witness = source_selected_observation model"
  obtains journal where "decode bytes = Some journal" "encode journal = bytes"
    "witness = Rust_Source_Selected journal (revision,hash bytes)" "0 < revision"
    "issue_at_source_selection verified (Some (map_of (rust_source_decisions journal)))
       (source_selected_observation model) origin = Some decision"
proof -
  obtain journal where decoded: "decode bytes = Some journal"
    and enc: "encode journal = bytes"
    and witness: "witness = Rust_Source_Selected journal (revision,hash bytes)"
    and revision: "0 < revision"
    and valid: "rust_source_state_valid registered verified journal"
    and exact: "map_of (rust_source_decisions journal) origin = Some decision"
    using raw by (cases "decode bytes"; cases witness)
      (auto simp: read_rust_source_decision_def split: if_splits)
  have verified: "verified origin decision"
    by (rule a_valid_source_record_has_a_verified_decision_at_every_selected_origin[OF valid exact])
  have selected: "source_selected_observation model = Some (map_of (rust_source_decisions journal))"
    using related witness by simp
  have vote: "issue_at_source_selection verified (Some (map_of (rust_source_decisions journal)))
       (source_selected_observation model) origin = Some decision"
    using selected exact verified by (simp add: issue_at_source_selection_def)
  show thesis using that[OF decoded enc witness revision vote] .
qed

theorem the_rust_read_before_quorum_signing_supplies_the_authoritative_certificate_record:
  assumes raw: "read_rust_source_decision decode encode hash registered valid revision bytes witness
     (evidence_profile claim, fst (evidence_payload claim)) = Some (evidence_epoch claim, snd (evidence_payload claim))"
    and related: "rust_selected_source_view witness = source_selected_observation model"
    and quorum: "source_certificate_quorum keys verify required claim proofs"
  shows "authoritative_source_certificate (source_selection model) keys verify required claim proofs"
proof (rule every_successful_rust_source_read_at_the_exact_mark_refines_the_selected_vote[OF raw related])
  fix journal
  assume vote: "issue_at_source_selection valid (Some (map_of (rust_source_decisions journal)))
      (source_selected_observation model) (evidence_profile claim, fst (evidence_payload claim)) =
        Some (evidence_epoch claim, snd (evidence_payload claim))"
  show ?thesis by (rule a_source_quorum_from_the_selected_journal_has_the_exact_authoritative_record[OF vote quorum])
qed

lemma a_restored_rust_journal_at_a_different_mod_revision_cannot_supply_a_vote:
  assumes "revision \<noteq> selected_revision"
  shows "read_rust_source_decision decode encode hash registered verified revision bytes
      (Rust_Source_Selected selected (selected_revision,digest)) origin = None"
  using assms by (cases "decode bytes") (auto simp: read_rust_source_decision_def)

lemma a_rust_witness_reservation_cannot_supply_a_vote:
  "read_rust_source_decision decode encode hash registered verified revision bytes Rust_Source_Appending origin = None"
  "read_rust_source_decision decode encode hash registered verified revision bytes Rust_Source_Repairing origin = None"
  by (cases "decode bytes"; simp add: read_rust_source_decision_def)+

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms every_successful_rust_source_read_at_the_exact_mark_refines_the_selected_vote
    the_rust_read_before_quorum_signing_supplies_the_authoritative_certificate_record
    a_restored_rust_journal_at_a_different_mod_revision_cannot_supply_a_vote
    a_rust_witness_reservation_cannot_supply_a_vote})
  then () else error "Unexpected oracle in native source reader correspondence"
\<close>

end

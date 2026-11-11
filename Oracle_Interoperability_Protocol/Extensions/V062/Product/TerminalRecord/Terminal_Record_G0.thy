theory Terminal_Record_G0
  imports "OIP_Reference_Execution.Reference_Settlement_Effects_Code"
begin

text \<open>
  The admitted Ledger transition owns a binding and a selected first terminal
  reference. The owner is carried explicitly with the public transfer binding.
  New evidence can refresh the same terminal kind without changing the first
  reference. Settlement reads the exact requested record, including a refresh.
  Authentication and authoritative primary publication are separate inputs.
\<close>

type_synonym tr_funded_binding = "transfer_binding \<times> nat"
type_synonym tr_terminal_record = "tr_funded_binding \<times> native_terminal_path"

record tr_retained_evidence =
  tr_first_reference :: "nat option"
  tr_evidence_rows :: "(nat \<times> tr_terminal_record) list"

datatype tr_record_reply = TR_Record_Rejected | TR_First_Record | TR_Refreshed_Record

definition tr_record_evidence ::
  "bool \<Rightarrow> tr_funded_binding \<Rightarrow> nat \<Rightarrow> tr_terminal_record \<Rightarrow> tr_retained_evidence
    \<Rightarrow> tr_retained_evidence \<times> tr_record_reply" where
  "tr_record_evidence pending owned requested new_record retained =
    (if fst new_record \<noteq> owned \<or> map_of (tr_evidence_rows retained) requested \<noteq> None
     then (retained, TR_Record_Rejected)
     else case tr_first_reference retained of
       None \<Rightarrow> if pending then
         (retained\<lparr>tr_first_reference := Some requested,
           tr_evidence_rows := (requested,new_record) # tr_evidence_rows retained\<rparr>, TR_First_Record)
         else (retained, TR_Record_Rejected)
     | Some first_reference \<Rightarrow> case map_of (tr_evidence_rows retained) first_reference of
         Some first_record \<Rightarrow> if snd first_record = snd new_record then
           (retained\<lparr>tr_evidence_rows := (requested,new_record) # tr_evidence_rows retained\<rparr>, TR_Refreshed_Record)
           else (retained, TR_Record_Rejected)
       | None \<Rightarrow> (retained, TR_Record_Rejected))"

lemma tr_first_reference_is_immutable_after_first_record:
  assumes "tr_first_reference retained \<noteq> None"
  shows "tr_first_reference (fst (tr_record_evidence pending owned requested new_record retained)) =
         tr_first_reference retained"
  using assms by (auto simp: tr_record_evidence_def split: option.splits if_splits)

lemma tr_first_kind_cannot_be_replaced_by_the_opposite_kind:
  assumes "tr_first_reference retained = Some first_reference"
    "map_of (tr_evidence_rows retained) first_reference = Some first_record"
    "snd first_record \<noteq> snd new_record"
  shows "tr_record_evidence pending owned requested new_record retained = (retained, TR_Record_Rejected)"
  using assms by (simp add: tr_record_evidence_def)

definition tr_lookup :: "bool \<Rightarrow> tr_retained_evidence \<Rightarrow> nat \<Rightarrow> tr_terminal_record option" where
  "tr_lookup use_first_fallback retained requested =
    (case map_of (tr_evidence_rows retained) requested of Some selected \<Rightarrow> Some selected
     | None \<Rightarrow> if use_first_fallback then
       (case tr_first_reference retained of None \<Rightarrow> None
          | Some first_reference \<Rightarrow> map_of (tr_evidence_rows retained) first_reference)
       else None)"

definition tr_exact_terminal where
  "tr_exact_terminal use_first_fallback retained owned requested settlement_kind \<longleftrightarrow>
    tr_first_reference retained \<noteq> None \<and>
    tr_lookup use_first_fallback retained requested = Some (owned,settlement_kind)"

definition tr_settlement_effect ::
  "bool \<Rightarrow> tr_retained_evidence \<Rightarrow> tr_funded_binding \<Rightarrow> nat \<Rightarrow> native_terminal_path
    \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> native_settlement_observation \<Rightarrow> native_settlement_observation \<times> bool" where
  "tr_settlement_effect use_first_fallback retained owned requested settlement_kind current_time lease_end before =
    (let selected_balance = (if settlement_kind = Native_Confirm
         then native_funded_destination before else native_available_source before);
         admitted = tr_exact_terminal use_first_fallback retained owned requested settlement_kind \<and>
           (settlement_kind = Native_Confirm \<or> current_time < lease_end)
     in native_settle_observation settlement_kind admitted
        (selected_balance + binding_amount (fst owned) < 2 ^ 64) (fst owned) before)"

lemma tr_missing_requested_reference_cannot_move_funds:
  assumes "map_of (tr_evidence_rows retained) requested = None"
  shows "tr_settlement_effect False retained owned requested settlement_kind current_time lease_end before =
    (before,False)"
  using assms by (simp add: tr_settlement_effect_def tr_exact_terminal_def tr_lookup_def
      native_settle_observation_def Let_def)

lemma tr_a_nonpending_source_cannot_settle_twice:
  assumes "\<not> native_origin_pending before"
  shows "tr_settlement_effect fallback retained owned requested settlement_kind current_time lease_end before =
    (before,False)"
  using assms by (simp add: tr_settlement_effect_def native_settle_observation_def Let_def)

lemma tr_cannot_refund_at_or_after_lease_end:
  assumes "lease_end \<le> current_time"
  shows "tr_settlement_effect fallback retained owned requested Native_Reverse current_time lease_end before =
    (before,False)"
proof -
  have "\<not> current_time < lease_end" using assms by simp
  then show ?thesis by (simp add: tr_settlement_effect_def native_settle_observation_def Let_def)
qed

lemma tr_admitted_settlement_consumes_the_matching_native_effect:
  assumes "snd (tr_settlement_effect False retained owned requested settlement_kind current_time lease_end before)"
  shows "tr_exact_terminal False retained owned requested settlement_kind"
    "native_origin_pending before"
    "tr_settlement_effect False retained owned requested settlement_kind current_time lease_end before =
      native_settle_observation settlement_kind True True (fst owned) before"
  using assms by (auto simp: tr_settlement_effect_def native_settle_observation_def Let_def
      split: if_splits native_terminal_path.splits)

lemma tr_refresh_keeps_primary_and_binds_the_exact_new_reference:
  fixes pending :: bool
  assumes first: "tr_first_reference retained = Some first_reference"
    and first_record: "map_of (tr_evidence_rows retained) first_reference = Some (owned,settlement_kind)"
    and new_reference: "map_of (tr_evidence_rows retained) requested = None"
  defines "refreshed \<equiv> fst (tr_record_evidence pending owned requested (owned,settlement_kind) retained)"
  shows "tr_first_reference refreshed = Some first_reference"
    "tr_exact_terminal False refreshed owned requested settlement_kind"
  using first first_record new_reference
  by (simp_all add: refreshed_def tr_record_evidence_def tr_exact_terminal_def tr_lookup_def)

lemma tr_removing_only_missing_reference_refusal_can_admit_credit:
  assumes "tr_first_reference retained = Some first_reference"
    "map_of (tr_evidence_rows retained) first_reference = Some (owned,Native_Confirm)"
    "map_of (tr_evidence_rows retained) requested = None"
    "native_origin_pending before"
    "native_funded_destination before + binding_amount (fst owned) < 2 ^ 64"
  shows "tr_settlement_effect False retained owned requested Native_Confirm current_time lease_end before = (before,False)"
    "snd (tr_settlement_effect True retained owned requested Native_Confirm current_time lease_end before)"
  using assms
  by (simp_all add: tr_settlement_effect_def tr_exact_terminal_def tr_lookup_def native_settle_observation_def Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms tr_first_reference_is_immutable_after_first_record
      tr_first_kind_cannot_be_replaced_by_the_opposite_kind tr_missing_requested_reference_cannot_move_funds
      tr_a_nonpending_source_cannot_settle_twice tr_cannot_refund_at_or_after_lease_end
      tr_admitted_settlement_consumes_the_matching_native_effect
      tr_refresh_keeps_primary_and_binds_the_exact_new_reference tr_removing_only_missing_reference_refusal_can_admit_credit})
  then () else error "Unexpected oracle in terminal record and settlement evidence"
\<close>

end

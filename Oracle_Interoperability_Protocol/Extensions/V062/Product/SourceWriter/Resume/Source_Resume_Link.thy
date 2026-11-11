theory Source_Resume_Link
  imports "OIP_Source_Writer_Phases.Source_Writer_Phases"
begin

text \<open>Resuming a validated two-store reservation consumes only the
  exact current values and registered configuration. Preparation selects a
  candidate and exact replacement condition. Publication after preparation
  is parameterized by the actual readback revision.\<close>

type_synonym sr_raw_control = "nat \<times> sw_json_bytes"

datatype sr_witness =
    SR_Initializing sw_json_mark
  | SR_Appending sw_json_mark
  | SR_Repairing sw_json_mark sw_json_mark sw_json_mark

datatype sr_call = SR_Initialize | SR_Read sw_origin | SR_Repair

datatype sr_prepare =
    SR_Already_Prepared sr_raw_control
  | SR_Replace_Journal sr_raw_control sw_json_bytes
  | SR_Prepare_Refused

datatype sr_result =
    SR_Invalid_Input
  | SR_Initialize_Refused
  | SR_Read_Result "sw_json_bytes option"
  | SR_Resume_Result sw_json_mark sw_json_bytes sr_prepare

definition sr_mark :: "(sw_json_bytes \<Rightarrow> sw_json_bytes option) \<Rightarrow> sr_raw_control \<Rightarrow> sw_json_mark option" where
  "sr_mark sr_hash sr_raw =
    map_option (\<lambda>sr_sha. (fst sr_raw,sr_sha)) (sr_hash (snd sr_raw))"

definition sr_prepare where
  "sr_prepare sr_hash sr_observed sr_expected sr_candidate =
    (if snd sr_observed = sr_candidate then SR_Already_Prepared sr_observed
     else if sr_mark sr_hash sr_observed = Some sr_expected then SR_Replace_Journal sr_observed sr_candidate
     else SR_Prepare_Refused)"

lemma sr_prepare_reuses_exact_bytes_before_comparing_the_old_mark:
  "snd sr_observed = sr_candidate \<Longrightarrow>
    sr_prepare sr_hash sr_observed sr_expected sr_candidate = SR_Already_Prepared sr_observed"
  by (simp add: sr_prepare_def)

lemma sr_replacement_compares_the_actual_revision_and_digest:
  assumes "sr_prepare sr_hash sr_observed sr_expected sr_candidate = SR_Replace_Journal sr_before sr_bytes"
  shows "sr_before = sr_observed" "sr_bytes = sr_candidate" "snd sr_observed \<noteq> sr_candidate"
    "sr_mark sr_hash sr_observed = Some sr_expected"
  using assms by (auto simp: sr_prepare_def split: if_splits)

definition sr_mark_width :: "sw_json_mark \<Rightarrow> bool" where
  "sr_mark_width sr_m \<longleftrightarrow> 0 < fst sr_m \<and> fst sr_m < 2^64 \<and> sw_octets_of_length 32 (snd sr_m)"

definition sr_mark_names where
  "sr_mark_names sr_hash sr_bytes sr_m \<longleftrightarrow> sr_mark_width sr_m \<and> sr_hash sr_bytes = Some (snd sr_m)"

definition sr_configured_stores where
  "sr_configured_stores sr_hash sr_cfg =
    (let sr_j = sw_digest sr_hash (sw_journal_binding_input sr_cfg);
         sr_w = sw_digest sr_hash (sw_witness_binding_input sr_cfg);
         sr_rules = sw_digest sr_hash (sw_rules_json sr_cfg)
     in if list_all (sw_octets_of_length 32) [sr_j,sr_w,sr_rules]
        then Some (sw_stores_json sr_j sr_w sr_rules) else None)"

definition sr_completed_state where
  "sr_completed_state sr_cfg sr_stores sr_req sr_preparation =
    sw_new_rust_state sr_cfg sr_stores (Some sr_preparation)
      [(sw_request_origin sr_req,sw_decision_json sr_req)]"

fun sr_witness_matches where
  "sr_witness_matches sr_hash sr_cfg sr_stores sr_req sr_issuer sr_raw
      (SR_Initializing sr_empty_mark) =
    (sr_mark_names sr_hash [] sr_empty_mark \<and>
     sr_raw = sw_initializing_json (sw_rust_state_json (sw_new_rust_state sr_cfg sr_stores None [])) sr_empty_mark)"
| "sr_witness_matches sr_hash sr_cfg sr_stores sr_req sr_issuer sr_raw
      (SR_Appending sr_before_mark) =
    (let sr_empty = sw_rust_state_json (sw_new_rust_state sr_cfg sr_stores None []) in
      sw_verified_decision sr_cfg sr_req sr_issuer \<and> sr_mark_names sr_hash sr_empty sr_before_mark \<and>
      sr_raw = sw_appending_json sr_empty sr_before_mark (sw_decision_json sr_req))"
| "sr_witness_matches sr_hash sr_cfg sr_stores sr_req sr_issuer sr_raw
      (SR_Repairing sr_preparation sr_selected_mark sr_observed_mark) =
    (let sr_target = sw_rust_state_json (sr_completed_state sr_cfg sr_stores sr_req sr_preparation) in
      sw_verified_decision sr_cfg sr_req sr_issuer \<and> sr_mark_width sr_preparation \<and>
      sr_mark_names sr_hash sr_target sr_selected_mark \<and> sr_mark_width sr_observed_mark \<and>
      sr_raw = sw_repairing_json sr_target sr_selected_mark sr_observed_mark)"

type_synonym sr_reader_witness =
  "(sw_origin, sw_json_bytes, sw_json_profile \<times> sw_json_bytes, sw_json_bytes) rust_source_witness"

definition sr_reader_during_repair where
  "sr_reader_during_repair sr_key =
    (case rust_selected_source_view (Rust_Source_Repairing :: sr_reader_witness) of
       None \<Rightarrow> None | Some sr_selected \<Rightarrow> sr_selected sr_key)"

lemma sr_repair_read_is_the_existing_reader_no_vote:
  "sr_reader_during_repair sr_key =
    read_rust_source_decision sr_decode sr_encode sr_hash sr_registered sr_verified sr_revision sr_bytes
      (Rust_Source_Repairing :: sr_reader_witness) sr_key"
  by (simp add: sr_reader_during_repair_def a_rust_witness_reservation_cannot_supply_a_vote(2))

definition sr_reference_repairing_state where
  "sr_reference_repairing_state sr_stale sr_target =
    \<lparr>source_journal = sr_stale,source_selection = map_of (rust_source_decisions sr_target),
      source_stage = Source_Repairing\<rparr>"

lemma sr_exact_repair_reselects_the_same_decision:
  fixes sr_stale sr_before sr_after
  assumes "map_of (rust_source_decisions sr_target) sr_key = Some sr_decision"
    "sr_verified sr_key sr_decision"
  defines "sr_before \<equiv> sr_reference_repairing_state sr_stale sr_target"
    and "sr_after \<equiv> reference_source_write sr_verified
      (Repair_Source True (map_of (rust_source_decisions sr_target))) sr_before"
  shows "source_selected_observation sr_before = None"
    "issue_at_source_selection sr_verified (Some (source_journal sr_after))
      (source_selected_observation sr_after) sr_key = Some sr_decision"
  using assms by (simp_all add: sr_before_def sr_after_def sr_reference_repairing_state_def
    source_selected_observation_def issue_at_source_selection_def)

fun sr_resume_operation where
  "sr_resume_operation sr_hash sr_cfg sr_stores sr_req sr_journal SR_Initialize (SR_Initializing sr_empty_mark) =
    (let sr_candidate = sw_rust_state_json (sw_new_rust_state sr_cfg sr_stores None [])
     in SR_Resume_Result sr_empty_mark sr_candidate (sr_prepare sr_hash sr_journal sr_empty_mark sr_candidate))"
| "sr_resume_operation sr_hash sr_cfg sr_stores sr_req sr_journal SR_Initialize (SR_Appending sr_old_mark) =
    SR_Initialize_Refused"
| "sr_resume_operation sr_hash sr_cfg sr_stores sr_req sr_journal (SR_Read sr_origin)
      (SR_Repairing sr_prep sr_selected sr_observed) =
    (let sr_empty = sw_rust_state_json (sw_new_rust_state sr_cfg sr_stores None []);
         sr_target = sw_rust_state_json (sr_completed_state sr_cfg sr_stores sr_req sr_prep)
     in if snd sr_journal = sr_empty \<or> snd sr_journal = sr_target
        then SR_Read_Result (sr_reader_during_repair sr_origin) else SR_Invalid_Input)"
| "sr_resume_operation sr_hash sr_cfg sr_stores sr_req sr_journal SR_Repair
      (SR_Repairing sr_prep sr_selected sr_observed) =
    (let sr_candidate = sw_rust_state_json (sr_completed_state sr_cfg sr_stores sr_req sr_prep)
     in SR_Resume_Result sr_observed sr_candidate (sr_prepare sr_hash sr_journal sr_observed sr_candidate))"
| "sr_resume_operation sr_hash sr_cfg sr_stores sr_req sr_journal sr_other_call sr_other_witness = SR_Invalid_Input"

definition sr_probe where
  "sr_probe sr_hash sr_cfg sr_good_keys sr_req sr_issuer sr_journal sr_witness_raw sr_call sr_witness =
    (if \<not> sw_config_admissible sr_cfg sr_good_keys \<or>
        \<not> sw_u64_words [fst sr_journal,fst sr_witness_raw] \<or>
        fst sr_journal = 0 \<or> fst sr_witness_raw = 0
     then SR_Invalid_Input
     else case sr_configured_stores sr_hash sr_cfg of None \<Rightarrow> SR_Invalid_Input
      | Some sr_stores \<Rightarrow>
        if sr_witness_matches sr_hash sr_cfg sr_stores sr_req sr_issuer (snd sr_witness_raw) sr_witness
        then sr_resume_operation sr_hash sr_cfg sr_stores sr_req sr_journal sr_call sr_witness
        else SR_Invalid_Input)"

definition sr_publish_candidate where
  "sr_publish_candidate sr_readback_mod sr_candidate sr_digest =
    (if sr_mark_width (sr_readback_mod,sr_digest)
     then Some (sw_selected_json sr_candidate (sr_readback_mod,sr_digest)) else None)"

lemma sr_publication_keeps_the_prepared_readback_mark:
  assumes "sr_mark sr_hash sr_readback = Some sr_exact_mark" "snd sr_readback = sr_candidate"
    "sr_mark_width sr_exact_mark"
  shows "sr_publish_candidate (fst sr_readback) sr_candidate (snd sr_exact_mark) =
    Some (sw_selected_json sr_candidate sr_exact_mark)"
proof -
  have "fst sr_exact_mark = fst sr_readback"
    using assms(1) by (auto simp: sr_mark_def split: option.splits)
  then show ?thesis using assms(3)
    by (cases sr_exact_mark) (simp add: sr_publish_candidate_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sr_prepare_reuses_exact_bytes_before_comparing_the_old_mark
      sr_replacement_compares_the_actual_revision_and_digest sr_repair_read_is_the_existing_reader_no_vote
      sr_exact_repair_reselects_the_same_decision sr_publication_keeps_the_prepared_readback_mark})
  then () else error "Unexpected oracle in exact source resume"
\<close>

end

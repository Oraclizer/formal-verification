theory Source_Writer_Phases
  imports "OIP_Source_Writer_JSON_G0.Source_Writer_JSON_G0"
    "OIP_Reference_Profile.Reference_Source_Reader_Code"
begin

text \<open>Fresh, provisioned empty keys, then the first signed source decision.
  These are the logical values of successful reserve, prepare and publish
  readbacks. Physical write, readback, MOD assignment, transport validation,
  and the hash and strict signature primitives are separate facts.\<close>

record sw_writer_config =
  sw_cfg_profile :: sw_json_profile
  sw_journal_binding_input :: sw_json_bytes
  sw_witness_binding_input :: sw_json_bytes
  sw_roster_domain :: nat
  sw_roster_epochs :: "nat list"
  sw_roster_issuer :: sw_json_bytes
  sw_roster_quorum :: nat
  sw_roster_signers :: "(nat \<times> sw_json_bytes) list"
  sw_journal_cap :: nat
  sw_witness_cap :: nat

record sw_writer_request =
  sw_req_profile :: sw_json_profile
  sw_req_epoch :: nat
  sw_req_domain :: nat
  sw_req_event :: nat
  sw_req_asset :: nat
  sw_req_owner :: nat
  sw_req_destination :: nat
  sw_req_recipient :: nat
  sw_req_amount :: nat
  sw_req_kind :: nat
  sw_req_reference :: nat
  sw_req_signature :: sw_json_bytes

record sw_writer_schedule =
  sw_j2 :: nat
  sw_w2 :: nat
  sw_j3 :: nat
  sw_w3 :: nat
  sw_w4 :: nat
  sw_w5 :: nat
  sw_j4 :: nat
  sw_w6 :: nat

type_synonym sw_origin = "nat \<times> nat"
type_synonym sw_rust_state =
  "(sw_origin, sw_json_bytes, sw_json_profile \<times> sw_json_bytes, sw_json_bytes) rust_source_state"

record sw_writer_effects =
  sw_initializing_bytes :: sw_json_bytes
  sw_genesis_bytes :: sw_json_bytes
  sw_selected_genesis_bytes :: sw_json_bytes
  sw_appending_bytes :: sw_json_bytes
  sw_prepared_bytes :: sw_json_bytes
  sw_selected_decision_bytes :: sw_json_bytes
  sw_empty_mark :: sw_json_mark
  sw_genesis_mark :: sw_json_mark
  sw_reservation_mark :: sw_json_mark
  sw_prepared_mark :: sw_json_mark
  sw_initialize_sizes :: "nat list"
  sw_append_sizes :: "nat list"
  sw_final_state :: sw_rust_state

datatype sw_writer_reply =
    SW_Outside_Chain
  | SW_Need_Hash sw_json_bytes
  | SW_Capacity_Exceeded "nat list" "nat list"
  | SW_Writer_Done sw_writer_effects

definition sw_request_origin :: "sw_writer_request \<Rightarrow> sw_origin" where
  "sw_request_origin sw_req = (sw_req_domain sw_req, sw_req_event sw_req)"

definition sw_origin_json where
  "sw_origin_json sw_req =
     code_json_open_key ''domain'' @ sw_decimal (sw_req_domain sw_req) @
     code_json_next_key ''event'' @ sw_decimal (sw_req_event sw_req) @ [125]"

definition sw_binding_json where
  "sw_binding_json sw_req =
     code_json_open_key ''origin'' @ sw_origin_json sw_req @
     code_json_next_key ''asset'' @ sw_decimal (sw_req_asset sw_req) @
     code_json_next_key ''owner'' @ sw_decimal (sw_req_owner sw_req) @
     code_json_next_key ''destination'' @ sw_decimal (sw_req_destination sw_req) @
     code_json_next_key ''recipient'' @ sw_decimal (sw_req_recipient sw_req) @
     code_json_next_key ''amount'' @ sw_decimal (sw_req_amount sw_req) @ [125]"

definition sw_evidence_json where
  "sw_evidence_json sw_req =
     code_json_open_key ''binding'' @ sw_binding_json sw_req @
     code_json_next_key ''kind'' @ [34] @
       code_json_ascii (if sw_req_kind sw_req = 1 then ''Confirmed'' else ''Reversed'') @ [34] @
     code_json_next_key ''reference'' @ sw_decimal (sw_req_reference sw_req) @ [125]"

definition sw_statement_json where
  "sw_statement_json sw_req =
     code_json_open_key ''profile'' @ sw_profile_json (sw_req_profile sw_req) @
     code_json_next_key ''origin_epoch'' @ sw_decimal (sw_req_epoch sw_req) @
     code_json_next_key ''evidence'' @ sw_evidence_json sw_req @ [125]"

definition sw_issuer_preimage where
  "sw_issuer_preimage sw_req =
     code_json_ascii ''oip/source-terminal-record/v1'' @ [0] @ sw_statement_json sw_req"

definition sw_decision_json where
  "sw_decision_json sw_req =
     code_json_open_key ''statement'' @ sw_statement_json sw_req @
     code_json_next_key ''signature'' @ sw_json_octets (sw_req_signature sw_req) @ [125]"

definition sw_json_numeric_entry where
  "sw_json_numeric_entry sw_id sw_value = [34] @ sw_decimal sw_id @ [34,58] @ sw_value"

definition sw_roster_rule_json where
  "sw_roster_rule_json sw_config =
     code_json_open_key ''issuer'' @ sw_json_octets (sw_roster_issuer sw_config) @
     code_json_next_key ''quorum'' @ sw_decimal (sw_roster_quorum sw_config) @
     code_json_next_key ''signers'' @ [123] @
     sw_json_elements (map (\<lambda>(sw_id,sw_key). sw_json_numeric_entry sw_id (sw_json_octets sw_key))
       (sw_roster_signers sw_config)) @ [125,125]"

definition sw_rules_json where
  "sw_rules_json sw_config =
     [123] @ sw_json_numeric_entry (sw_roster_domain sw_config)
       ([123] @ sw_json_elements (map (\<lambda>sw_epoch.
          sw_json_numeric_entry sw_epoch (sw_roster_rule_json sw_config)) (sw_roster_epochs sw_config)) @ [125])
     @ [125]"

definition sw_u64_words :: "nat list \<Rightarrow> bool" where
  "sw_u64_words sw_words \<longleftrightarrow> list_all (\<lambda>sw_n. sw_n < 2^64) sw_words"

definition sw_profile_width :: "sw_json_profile \<Rightarrow> bool" where
  "sw_profile_width sw_cfg \<longleftrightarrow>
    (case sw_cfg of (sw_deploy,sw_format,sw_authority) \<Rightarrow>
      sw_u64_words [sw_deploy,sw_authority] \<and> sw_format < 2^32)"

definition sw_octets_of_length :: "nat \<Rightarrow> sw_json_bytes \<Rightarrow> bool" where
  "sw_octets_of_length sw_size sw_bytes \<longleftrightarrow>
     length sw_bytes = sw_size \<and> list_all (\<lambda>sw_b. sw_b < 256) sw_bytes"

definition sw_config_admissible where
  "sw_config_admissible sw_config sw_good_keys \<longleftrightarrow>
     sw_profile_width (sw_cfg_profile sw_config) \<and>
     sw_journal_binding_input sw_config \<noteq> sw_witness_binding_input sw_config \<and>
     sw_u64_words (sw_roster_domain sw_config # sw_roster_epochs sw_config @ map fst (sw_roster_signers sw_config)) \<and>
     sw_roster_epochs sw_config \<noteq> [] \<and> sorted_wrt (<) (sw_roster_epochs sw_config) \<and>
     sorted_wrt (<) (map fst (sw_roster_signers sw_config)) \<and>
     0 < sw_roster_quorum sw_config \<and> sw_roster_quorum sw_config \<le> length (sw_roster_signers sw_config) \<and>
     distinct (sw_roster_issuer sw_config # map snd (sw_roster_signers sw_config)) \<and>
     list_all (\<lambda>sw_key. sw_octets_of_length 32 sw_key \<and> List.member sw_good_keys sw_key)
       (sw_roster_issuer sw_config # map snd (sw_roster_signers sw_config))"

definition sw_verified_decision where
  "sw_verified_decision sw_config sw_req sw_issuer_facts \<longleftrightarrow>
     sw_req_profile sw_req = sw_cfg_profile sw_config \<and>
     sw_u64_words [sw_req_epoch sw_req, sw_req_domain sw_req, sw_req_event sw_req, sw_req_asset sw_req,
       sw_req_owner sw_req, sw_req_destination sw_req, sw_req_recipient sw_req, sw_req_amount sw_req,
       sw_req_reference sw_req] \<and>
     0 < sw_req_amount sw_req \<and> (sw_req_kind sw_req = 1 \<or> sw_req_kind sw_req = 2) \<and>
     sw_req_domain sw_req = sw_roster_domain sw_config \<and> List.member (sw_roster_epochs sw_config) (sw_req_epoch sw_req) \<and>
     sw_octets_of_length 64 (sw_req_signature sw_req) \<and>
     List.member sw_issuer_facts [sw_roster_issuer sw_config, sw_issuer_preimage sw_req, sw_req_signature sw_req]"

definition sw_admitted_schedule where
  "sw_admitted_schedule sw_revs \<longleftrightarrow>
     0 < sw_j2 sw_revs \<and> sw_j2 sw_revs < sw_j3 sw_revs \<and> sw_j3 sw_revs < sw_j4 sw_revs \<and> sw_j4 sw_revs < 2^64 \<and>
     0 < sw_w2 sw_revs \<and> sw_w2 sw_revs < sw_w3 sw_revs \<and> sw_w3 sw_revs < sw_w4 sw_revs \<and>
     sw_w4 sw_revs < sw_w5 sw_revs \<and> sw_w5 sw_revs < sw_w6 sw_revs \<and> sw_w6 sw_revs < 2^64"

definition sw_ingress_valid where
  "sw_ingress_valid sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts \<longleftrightarrow>
     sw_empty_j = [] \<and> sw_empty_w = [] \<and> sw_admitted_schedule sw_revs \<and>
     sw_config_admissible sw_config sw_good_keys \<and> sw_verified_decision sw_config sw_req sw_issuer_facts"

definition sw_capacity_sizes where
  "sw_capacity_sizes sw_state =
     [length sw_state, length (sw_selected_json sw_state sw_encoding_bound),
      length (sw_repairing_json sw_state sw_encoding_bound sw_encoding_bound)]"

fun sw_sizes_fit where
  "sw_sizes_fit sw_config [sw_journal,sw_selected,sw_repair] =
     (sw_journal \<le> sw_journal_cap sw_config \<and> sw_selected \<le> sw_witness_cap sw_config \<and>
       sw_repair \<le> sw_witness_cap sw_config)"
| "sw_sizes_fit sw_config sw_other = False"

definition sw_rust_state_json :: "sw_rust_state \<Rightarrow> sw_json_bytes" where
  "sw_rust_state_json sw_state =
     sw_state_json (fst (rust_source_binding sw_state)) (snd (rust_source_binding sw_state))
       (rust_source_reservation sw_state) (map snd (rust_source_decisions sw_state))"

definition sw_new_rust_state where
  "sw_new_rust_state sw_config sw_stores sw_prep sw_items =
     (\<lparr>rust_source_binding = (sw_cfg_profile sw_config,sw_stores),
       rust_source_reservation = sw_prep, rust_source_decisions = sw_items\<rparr> :: sw_rust_state)"

definition sw_digest :: "(sw_json_bytes \<Rightarrow> sw_json_bytes option) \<Rightarrow> sw_json_bytes \<Rightarrow> sw_json_bytes" where
  "sw_digest sw_hash sw_raw = (case sw_hash sw_raw of None \<Rightarrow> [] | Some sw_d \<Rightarrow> sw_d)"

definition sw_unresolved where
  "sw_unresolved sw_hash sw_raw \<longleftrightarrow> \<not> sw_octets_of_length 32 (sw_digest sw_hash sw_raw)"

text \<open>The default in sw_digest is only for constructing the list of
  queries. A missing or malformed digest is never returned as a completed
  chain. Each generated query depends only on preceding exact queries.\<close>

definition sw_plan where
  "sw_plan sw_hash sw_config sw_req sw_revs sw_empty_j =
     (let sw_j_input = sw_journal_binding_input sw_config;
          sw_w_input = sw_witness_binding_input sw_config;
          sw_rules = sw_rules_json sw_config;
          sw_stores = sw_stores_json (sw_digest sw_hash sw_j_input) (sw_digest sw_hash sw_w_input) (sw_digest sw_hash sw_rules);
          sw_decision = sw_decision_json sw_req;
          sw_items = [(sw_request_origin sw_req, sw_decision)];
          sw_genesis = sw_rust_state_json (sw_new_rust_state sw_config sw_stores None []);
          sw_first = (sw_j2 sw_revs, sw_digest sw_hash sw_empty_j);
          sw_initialized = (sw_j3 sw_revs, sw_digest sw_hash sw_genesis);
          sw_reserved = sw_appending_json sw_genesis sw_initialized sw_decision;
          sw_reserve_mark = (sw_w5 sw_revs, sw_digest sw_hash sw_reserved);
          sw_bounded = sw_rust_state_json (sw_new_rust_state sw_config sw_stores (Some sw_encoding_bound) sw_items);
          sw_end_state = sw_new_rust_state sw_config sw_stores (Some sw_reserve_mark) sw_items;
          sw_written = sw_rust_state_json sw_end_state;
          sw_last = (sw_j4 sw_revs, sw_digest sw_hash sw_written)
      in ([sw_j_input, sw_w_input, sw_rules, sw_empty_j, sw_genesis, sw_reserved, sw_written],
          \<lparr>sw_initializing_bytes = sw_initializing_json sw_genesis sw_first,
            sw_genesis_bytes = sw_genesis,
            sw_selected_genesis_bytes = sw_selected_json sw_genesis sw_initialized,
            sw_appending_bytes = sw_reserved, sw_prepared_bytes = sw_written,
            sw_selected_decision_bytes = sw_selected_json sw_written sw_last,
            sw_empty_mark = sw_first, sw_genesis_mark = sw_initialized,
            sw_reservation_mark = sw_reserve_mark, sw_prepared_mark = sw_last,
            sw_initialize_sizes = sw_capacity_sizes sw_genesis, sw_append_sizes = sw_capacity_sizes sw_bounded,
            sw_final_state = sw_end_state\<rparr>))"

definition sw_run where
  "sw_run sw_hash sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts =
     (if \<not> sw_ingress_valid sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts then SW_Outside_Chain
      else let sw_build = sw_plan sw_hash sw_config sw_req sw_revs sw_empty_j;
               sw_out = snd sw_build
           in case List.find (sw_unresolved sw_hash) (fst sw_build) of
                Some sw_raw \<Rightarrow> SW_Need_Hash sw_raw
              | None \<Rightarrow>
                 if sw_sizes_fit sw_config (sw_initialize_sizes sw_out) \<and> sw_sizes_fit sw_config (sw_append_sizes sw_out)
                 then SW_Writer_Done sw_out
                 else SW_Capacity_Exceeded (sw_initialize_sizes sw_out) (sw_append_sizes sw_out))"

lemma sw_done_uses_plan:
  assumes "sw_run sw_hash sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts = SW_Writer_Done sw_out"
  shows "sw_ingress_valid sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts"
    "sw_out = snd (sw_plan sw_hash sw_config sw_req sw_revs sw_empty_j)"
    "List.find (sw_unresolved sw_hash) (fst (sw_plan sw_hash sw_config sw_req sw_revs sw_empty_j)) = None"
    "sw_sizes_fit sw_config (sw_initialize_sizes sw_out)"
    "sw_sizes_fit sw_config (sw_append_sizes sw_out)"
  using assms by (auto simp: sw_run_def Let_def split: option.splits if_splits)

lemma sw_done_exact_marks_and_state:
  assumes sw_done: "sw_run sw_hash sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts = SW_Writer_Done sw_out"
  shows "sw_empty_mark sw_out = (sw_j2 sw_revs, sw_digest sw_hash sw_empty_j)"
    "sw_genesis_mark sw_out = (sw_j3 sw_revs, sw_digest sw_hash (sw_genesis_bytes sw_out))"
    "sw_reservation_mark sw_out = (sw_w5 sw_revs, sw_digest sw_hash (sw_appending_bytes sw_out))"
    "sw_prepared_mark sw_out = (sw_j4 sw_revs, sw_digest sw_hash (sw_prepared_bytes sw_out))"
    "sw_prepared_bytes sw_out = sw_rust_state_json (sw_final_state sw_out)"
    "sw_selected_decision_bytes sw_out = sw_selected_json (sw_prepared_bytes sw_out) (sw_prepared_mark sw_out)"
    "rust_source_reservation (sw_final_state sw_out) = Some (sw_reservation_mark sw_out)"
    "rust_source_decisions (sw_final_state sw_out) = [(sw_request_origin sw_req, sw_decision_json sw_req)]"
    "sw_initializing_bytes sw_out = sw_initializing_json (sw_genesis_bytes sw_out) (sw_empty_mark sw_out)"
    "sw_selected_genesis_bytes sw_out = sw_selected_json (sw_genesis_bytes sw_out) (sw_genesis_mark sw_out)"
    "sw_appending_bytes sw_out = sw_appending_json (sw_genesis_bytes sw_out) (sw_genesis_mark sw_out) (sw_decision_json sw_req)"
  using sw_done_uses_plan(2)[OF sw_done]
  by (simp_all add: sw_plan_def Let_def sw_new_rust_state_def)

definition sw_reference_valid where
  "sw_reference_valid sw_config sw_req sw_issuer_facts sw_o sw_d \<longleftrightarrow>
     sw_o = sw_request_origin sw_req \<and> sw_d = sw_decision_json sw_req \<and>
     sw_verified_decision sw_config sw_req sw_issuer_facts"

definition sw_reference_genesis ::
  "(sw_origin, sw_json_bytes) reference_source_storage" where
  "sw_reference_genesis = \<lparr>source_journal = (\<lambda>_. None), source_selection = (\<lambda>_. None),
     source_stage = Source_Selected\<rparr>"

definition sw_reference_reserved where
  "sw_reference_reserved sw_valid sw_req =
     reference_source_write sw_valid (Reserve_Source (\<lambda>_. None) (sw_request_origin sw_req) (sw_decision_json sw_req))
       sw_reference_genesis"

definition sw_reference_prepared where
  "sw_reference_prepared sw_valid sw_req =
     reference_source_write sw_valid (Prepare_Source (\<lambda>_. None) (sw_request_origin sw_req) (sw_decision_json sw_req))
       (sw_reference_reserved sw_valid sw_req)"

definition sw_reference_selected where
  "sw_reference_selected sw_valid sw_req =
     reference_source_write sw_valid (Select_Source (\<lambda>_. None) (sw_request_origin sw_req) (sw_decision_json sw_req))
       (sw_reference_prepared sw_valid sw_req)"

lemma sw_done_first_reference_selection:
  assumes sw_done: "sw_run sw_hash sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts = SW_Writer_Done sw_out"
  defines "sw_valid \<equiv> sw_reference_valid sw_config sw_req sw_issuer_facts"
  shows "source_selected_observation (sw_reference_reserved sw_valid sw_req) = None"
    "source_selected_observation (sw_reference_prepared sw_valid sw_req) = None"
    "source_selected_observation (sw_reference_selected sw_valid sw_req) =
       Some (map_of (rust_source_decisions (sw_final_state sw_out)))"
proof -
  have sw_verified: "sw_verified_decision sw_config sw_req sw_issuer_facts"
    using sw_done_uses_plan(1)[OF sw_done] by (simp add: sw_ingress_valid_def)
  have sw_exact: "sw_valid (sw_request_origin sw_req) (sw_decision_json sw_req)"
    using sw_verified by (simp add: sw_valid_def sw_reference_valid_def)
  show "source_selected_observation (sw_reference_reserved sw_valid sw_req) = None"
    using sw_exact by (simp add: sw_reference_reserved_def sw_reference_genesis_def source_selected_observation_def)
  show "source_selected_observation (sw_reference_prepared sw_valid sw_req) = None"
    using sw_exact by (simp add: sw_reference_prepared_def sw_reference_reserved_def
      sw_reference_genesis_def source_selected_observation_def)
  have sw_map: "map_of [(sw_request_origin sw_req, sw_decision_json sw_req)] =
      (\<lambda>_. None)(sw_request_origin sw_req := Some (sw_decision_json sw_req))"
    by (rule ext) (simp add: fun_upd_def)
  show "source_selected_observation (sw_reference_selected sw_valid sw_req) =
      Some (map_of (rust_source_decisions (sw_final_state sw_out)))"
    using sw_exact sw_done_exact_marks_and_state(8)[OF sw_done] sw_map
    by (simp add: sw_reference_selected_def sw_reference_prepared_def sw_reference_reserved_def
      sw_reference_genesis_def source_selected_observation_def)
qed

theorem sw_done_reads_the_exact_first_decision:
  assumes sw_done: "sw_run sw_hash sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts = SW_Writer_Done sw_out"
    and sw_decode: "sw_decode_journal (sw_prepared_bytes sw_out) = Some (sw_final_state sw_out)"
  defines "sw_valid \<equiv> sw_reference_valid sw_config sw_req sw_issuer_facts"
  shows "read_rust_source_decision sw_decode_journal sw_rust_state_json (sw_digest sw_hash)
       (rust_source_binding (sw_final_state sw_out)) sw_valid (sw_j4 sw_revs) (sw_prepared_bytes sw_out)
       (Rust_Source_Selected (sw_final_state sw_out) (sw_prepared_mark sw_out)) (sw_request_origin sw_req)
     = Some (sw_decision_json sw_req)"
proof -
  note sw_marks = sw_done_exact_marks_and_state[OF sw_done]
  have sw_in: "sw_ingress_valid sw_config sw_req sw_revs sw_empty_j sw_empty_w sw_good_keys sw_issuer_facts"
    by (rule sw_done_uses_plan(1)[OF sw_done])
  have sw_verified: "sw_valid (sw_request_origin sw_req) (sw_decision_json sw_req)"
    using sw_in by (simp add: sw_ingress_valid_def sw_valid_def sw_reference_valid_def)
  have sw_revs_ok: "0 < sw_w5 sw_revs" "0 < sw_j4 sw_revs"
    using sw_in by (auto simp: sw_ingress_valid_def sw_admitted_schedule_def intro: less_trans)
  have sw_state_ok: "rust_source_state_valid (rust_source_binding (sw_final_state sw_out)) sw_valid (sw_final_state sw_out)"
    using sw_revs_ok(1) sw_verified by (simp add: rust_source_state_valid_def sw_marks(3,7,8))
  show ?thesis
    using sw_decode sw_state_ok sw_revs_ok(2)
    by (simp add: read_rust_source_decision_def sw_marks(4,8) flip: sw_marks(5))
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sw_done_uses_plan sw_done_exact_marks_and_state
      sw_done_first_reference_selection sw_done_reads_the_exact_first_decision})
  then () else error "Unexpected oracle in source writer phases"
\<close>

end

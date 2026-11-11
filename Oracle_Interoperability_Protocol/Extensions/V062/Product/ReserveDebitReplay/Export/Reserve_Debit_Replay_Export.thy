theory Reserve_Debit_Replay_Export
  imports "OIP_Reserve_Debit_Replay.Reserve_Debit_Replay_G0"
    "OIP_Reserve_Debit_Finite_Base.Wire_Code_Finite_Integer_ABI"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen"
begin

fun rdr_reply_result :: "code_fixture_replay_reply \<Rightarrow> (nat \<times> nat option) option" where
  "rdr_reply_result Code_Fixture_Initialized = None"
| "rdr_reply_result Code_Fixture_Replay_Pending = None"
| "rdr_reply_result (Code_Fixture_Replay_Error reason) = Some (code_source_error_result reason)"
| "rdr_reply_result (Code_Fixture_Replay_Received arrival outcome) =
    Some (code_source_from_received (Code_Source_Ordinary_Collected outcome)
      (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected outcome))))"
| "rdr_reply_result (Code_Fixture_Replay_Resolved resolution) = Some (code_source_from_resolution resolution)"

fun rdr_reply_kind :: "code_fixture_replay_reply \<Rightarrow> nat" where
  "rdr_reply_kind Code_Fixture_Initialized = 0"
| "rdr_reply_kind Code_Fixture_Replay_Pending = 2"
| "rdr_reply_kind (Code_Fixture_Replay_Error reason) = 3"
| "rdr_reply_kind (Code_Fixture_Replay_Received arrival outcome) = 1"
| "rdr_reply_kind (Code_Fixture_Replay_Resolved resolution) = 4"

fun rdr_arrival_word :: "code_arrival \<Rightarrow> nat" where
  "rdr_arrival_word Code_First = 1"
| "rdr_arrival_word Code_Identical = 2"
| "rdr_arrival_word Code_Replay_Conflict = 3"

fun rdr_optional_position :: "nat option \<Rightarrow> nat" where
  "rdr_optional_position None = 0"
| "rdr_optional_position (Some rdr_position) = rdr_position"

definition rdr_reply_words where
  "rdr_reply_words reply =
    (let result = (case rdr_reply_result reply of None \<Rightarrow> [0,0,0]
          | Some (rdr_code,rdr_commit) \<Rightarrow>
              [rdr_code,if rdr_commit = None then 0 else 1,rdr_optional_position rdr_commit]);
         arrival = (case reply of Code_Fixture_Replay_Received value outcome \<Rightarrow> rdr_arrival_word value | _ \<Rightarrow> 0)
     in [rdr_reply_kind reply] @ result @ [arrival])"

definition rdr_state_words :: "code_fixture_replay_state \<Rightarrow> integer list" where
  "rdr_state_words state =
    (let slice = replay_financial_slice state; financial = finite_machine_state (slice_financial slice);
         phase = map_option reservation_phase (map_of (finite_reservations financial) (0,17))
     in map integer_of_nat
       [slice_revision slice,code_finite_nat_default (finite_source_units financial) (0,17),
        code_finite_nat_default (slice_holder_balances slice) ((0,17),7),
        sum_list (map binding_amount (finite_source_effects financial))] @
       [code_finite_phase_integer phase] @ map integer_of_nat
       [length (finite_machine_journal (slice_financial slice)),length (slice_source_bindings slice),
        length (replay_calls state),length (replay_transport state),length (replay_debit_decisions state),
        length (replay_latest_work state),replay_store_counter state,replay_head_sequence state])"

definition rdr_transport_entry :: "(authenticated_message_id \<times> wire_bytes) \<Rightarrow> (integer list \<times> integer list)" where
  "rdr_transport_entry entry =
    (case entry of ((rdr_dep,rdr_src,rdr_actor,rdr_uuid),rdr_core) \<Rightarrow>
      (map integer_of_nat ([rdr_dep,rdr_src,rdr_actor] @ rdr_uuid),map integer_of_nat rdr_core))"

fun rdr_disposition_word :: "reference_disposition \<Rightarrow> nat" where
  "rdr_disposition_word Ref_Pending = 0"
| "rdr_disposition_word Ref_Applied = 1"
| "rdr_disposition_word Ref_Retained_Refusal = 2"
| "rdr_disposition_word Ref_Explicit_Rejection = 3"

definition rdr_debit_entry ::
  "(client_call_id \<times> (code_source_debit_request \<times> reference_disposition)) \<Rightarrow> (integer list \<times> integer list)" where
  "rdr_debit_entry entry =
    (case entry of ((rdr_map_actor,rdr_map_seq),(request,rdr_disposition)) \<Rightarrow>
      let (rdr_actor,rdr_seq) = source_debit_id request;
          (rdr_origin,rdr_event) = source_debit_origin request
      in (map integer_of_nat [rdr_map_actor,rdr_map_seq,rdr_actor,rdr_seq,rdr_origin,rdr_event,
            source_debit_generation request,rdr_disposition_word rdr_disposition],
          map integer_of_nat (source_debit_packet request)))"

definition rdr_call_entry where
  "rdr_call_entry entry =
    (case entry of ((rdr_actor,rdr_seq),(payload,outcome)) \<Rightarrow>
      map integer_of_nat [rdr_actor,rdr_seq,code_source_ordinary_number (source_outcome_reply outcome),
        if source_outcome_commit outcome = None then 0 else 1,rdr_optional_position (source_outcome_commit outcome)])"

definition rdr_latest_entry where
  "rdr_latest_entry entry =
    (case entry of (((rdr_origin,rdr_event),rdr_generation),(rdr_actor,rdr_seq)) \<Rightarrow>
      map integer_of_nat [rdr_origin,rdr_event,rdr_generation,rdr_actor,rdr_seq])"

type_synonym rdr_integer_row =
  "integer list \<times> (integer list \<times> integer list) list \<times>
    (integer list \<times> integer list) list \<times> integer list list \<times> integer list list"

definition rdr_integer_row :: "code_fixture_stimulus \<Rightarrow>
    (code_fixture_replay_state \<times> code_fixture_replay_reply) \<Rightarrow> rdr_integer_row" where
  "rdr_integer_row event step =
    (let state = fst step in
      (map integer_of_nat ([fixture_stimulus_id event] @ rdr_reply_words (snd step)) @ rdr_state_words state,
       map rdr_transport_entry (replay_transport state),map rdr_debit_entry (replay_debit_decisions state),
       map rdr_call_entry (replay_calls state),map rdr_latest_entry (replay_latest_work state)))"

definition rdr_integer_trace where
  "rdr_integer_trace events =
    map_option (\<lambda>rows. map (\<lambda>(event,row). rdr_integer_row event row) (zip events rows)) (rdr_checked_run events)"

definition rdr_replay_integer_trace :: "unit \<Rightarrow> rdr_integer_row list option" where
  "rdr_replay_integer_trace ignored = rdr_integer_trace code_fixture_stimuli"

definition rdr_same_cut_integer_trace :: "unit \<Rightarrow> rdr_integer_row list option" where
  "rdr_same_cut_integer_trace ignored = rdr_integer_trace rdr_same_cut_stimuli"

definition rdr_identity_words where
  "rdr_identity_words identity =
    (case identity of None \<Rightarrow> [0] | Some value \<Rightarrow>
      map integer_of_nat [1,identity_principal value,identity_domain value,identity_ocid value,identity_rai value])"

definition rdr_fixed_checks :: "unit \<Rightarrow> integer list list option" where
  "rdr_fixed_checks ignored =
    (if rdr_trace_domain code_fixture_stimuli \<and> rdr_trace_domain rdr_same_cut_stimuli then
       let (first,second) = rdr_fixed_token_observations
       in Some [rdr_identity_words first,rdr_identity_words second]
     else None)"

definition rdr_input_counts :: "unit \<Rightarrow> integer list" where
  "rdr_input_counts ignored =
    (let replay_rows = length code_fixture_stimuli;
         replay_seeds = length (filter (\<lambda>event. fixture_stimulus_api event = Code_Fixture_Initialize) code_fixture_stimuli);
         same_rows = length rdr_same_cut_stimuli;
         same_seeds = length (filter (\<lambda>event. fixture_stimulus_api event = Code_Fixture_Initialize) rdr_same_cut_stimuli)
     in map integer_of_nat [replay_rows,replay_seeds,replay_rows - replay_seeds,same_rows,same_seeds,same_rows - same_seeds])"

lemma rdr_integer_projection_cannot_drop_a_checked_row:
  assumes "rdr_integer_trace events = Some result_rows"
  shows "length result_rows = length events"
proof -
  obtain rows where rdr_checked_rows: "rdr_checked_run events = Some rows"
    and rdr_projected_rows: "result_rows = map (\<lambda>(event,row). rdr_integer_row event row) (zip events rows)"
    using assms by (auto simp: rdr_integer_trace_def split: option.splits)
  have rdr_count: "length rows = length events" by (rule rdr_checked_trace_has_one_model_row_per_input_occurrence[OF rdr_checked_rows])
  show ?thesis by (simp add: rdr_projected_rows rdr_count)
qed

lemma rdr_incomplete_primitive_metadata_has_no_serialized_protocol_result:
  "\<not> rdr_trace_domain events \<Longrightarrow> rdr_integer_trace events = None"
  by (simp add: rdr_integer_trace_def rdr_checked_run_def)

text \<open>
  All output rows are projections of the computed replay state and reply.
  The trace guard is evaluated before the original model program. No result
  list, expected code, observed after-state or source execution receipt is an
  input. Initialization rows are counted separately and Pending is explicit.
  This fixed source-account projection does not serialize the entire retained
  product, control JSON, head offsets/digests or signed response envelope.
  Raw transport Core bindings and original signed Debit bytes are retained.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      rdr_integer_projection_cannot_drop_a_checked_row
      rdr_incomplete_primitive_metadata_has_no_serialized_protocol_result})
  then () else error "Unexpected oracle in the independent replay export"
\<close>

export_code rdr_replay_integer_trace rdr_same_cut_integer_trace rdr_fixed_checks rdr_input_counts
  in SML module_name OIP_Reserve_Debit_Replay file_prefix "oip_reserve_debit_replay"

end

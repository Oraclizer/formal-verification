theory Wire_Code_Fixture_Replay_Engine
  imports Reserve_Debit_Seed Wire_Code_Fixture_Replay_Environment
begin

record code_fixture_replay_state =
  replay_financial_slice :: code_finite_source_slice
  replay_calls :: "(client_call_id \<times> (code_source_call_payload \<times> code_source_outcome)) list"
  replay_transport :: "(authenticated_message_id \<times> wire_bytes) list"
  replay_debit_decisions :: "(client_call_id \<times> (code_source_debit_request \<times> reference_disposition)) list"
  replay_latest_work :: "((source_key \<times> nat) \<times> client_call_id) list"
  replay_store_counter :: nat
  replay_head_sequence :: nat

datatype code_fixture_replay_reply =
    Code_Fixture_Initialized
  | Code_Fixture_Replay_Pending
  | Code_Fixture_Replay_Error code_source_wire_error
  | Code_Fixture_Replay_Received code_arrival code_source_outcome
  | Code_Fixture_Replay_Resolved code_source_resolution

definition code_fixture_replay_initial :: code_fixture_replay_state where
  "code_fixture_replay_initial = \<lparr>replay_financial_slice = code_fixture_initial_slice,replay_calls = [],
    replay_transport = [],replay_debit_decisions = [],replay_latest_work = [],replay_store_counter = 2,replay_head_sequence = 0\<rparr>"

definition code_fixture_is_debit :: "code_finite_selected_ordinary \<Rightarrow> bool" where
  "code_fixture_is_debit chosen = (case finite_selected_command chosen of Code_Finite_Debit generation \<Rightarrow> True | _ \<Rightarrow> False)"

definition code_fixture_original_debit :: "wire_bytes \<Rightarrow> code_finite_selected_ordinary \<Rightarrow> code_source_debit_request" where
  "code_fixture_original_debit bytes chosen =
    \<lparr>source_debit_id = native_id (finite_selected_native chosen),source_debit_origin = native_origin (finite_selected_native chosen),
      source_debit_generation = (case finite_selected_command chosen of Code_Finite_Debit generation \<Rightarrow> generation | _ \<Rightarrow> 0),
      source_debit_packet = bytes\<rparr>"

definition code_fixture_control_observation :: "code_fixture_replay_state \<Rightarrow> code_source_control_observation" where
  "code_fixture_control_observation state = \<lparr>source_control_stored = (replay_store_counter state,[]),
    source_control_revoked = [],source_control_cancelled = [],source_control_decisions = replay_debit_decisions state,
    source_control_latest = replay_latest_work state\<rparr>"

definition code_fixture_model_receipt :: "code_fixture_replay_state \<Rightarrow> code_finite_selected_ordinary \<Rightarrow> code_source_receipt option" where
  "code_fixture_model_receipt state chosen =
    (case map_of (replay_calls state) (native_id (finite_selected_native chosen)) of
       None \<Rightarrow> Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting)
     | Some (payload,outcome) \<Rightarrow> Some (Code_Source_Ordinary_Receipt
         (if payload = finite_selected_payload chosen then Code_Source_Collected outcome else Code_Source_Collection_Rejected)))"

definition code_fixture_model_receipt_reservation :: "code_fixture_replay_state \<Rightarrow> code_finite_selected_ordinary \<Rightarrow>
  code_source_receipt_reservation option" where
  "code_fixture_model_receipt_reservation state chosen =
    (let slice = replay_financial_slice state; key = native_origin (finite_selected_native chosen);
         financial = finite_machine_state (slice_financial slice)
     in case (map_of (slice_source_bindings slice) key,map_of (finite_reservations financial) key) of
       (Some binding,Some stored) \<Rightarrow> Some \<lparr>source_reservation_binding = binding,
         source_reservation_holder = reservation_worker stored,source_reservation_generation = reservation_generation stored,
         source_reservation_deadline = reservation_deadline stored,source_reservation_active = active_reservation_phase (reservation_phase stored),
         source_reservation_versions = finite_asset_versions financial\<rparr>
     | _ \<Rightarrow> None)"

definition code_fixture_record_call :: "wire_bytes \<Rightarrow> code_finite_selected_ordinary \<Rightarrow> code_arrival \<Rightarrow>
  code_finite_source_slice \<Rightarrow> code_source_outcome \<Rightarrow> code_fixture_replay_state \<Rightarrow> code_fixture_replay_state" where
  "code_fixture_record_call bytes chosen arrival slice_after outcome state =
    (let native = finite_selected_native chosen; core = finite_selected_core chosen; debit = code_fixture_is_debit chosen;
         applied = source_outcome_reply outcome = Code_Source_Accepted Code_Source_Debited_Reply;
         original = code_fixture_original_debit bytes chosen
     in state\<lparr>replay_financial_slice := slice_after,
       replay_calls := code_finite_put (native_id native) (finite_selected_payload chosen,outcome) (replay_calls state),
       replay_transport := (if arrival = Code_First then code_finite_put (authenticated_wire_message_id core)
         (encode_wire_core core) (replay_transport state) else replay_transport state),
       replay_debit_decisions := (if debit then code_finite_put (native_id native)
         (original,if applied then Ref_Applied else Ref_Retained_Refusal) (replay_debit_decisions state) else replay_debit_decisions state),
       replay_latest_work := (if debit \<and> applied then code_finite_put (code_source_debit_work original) (native_id native)
         (replay_latest_work state) else replay_latest_work state),
       replay_store_counter := replay_store_counter state + (if debit \<and> applied then 2 else 1),
       replay_head_sequence := Suc (replay_head_sequence state)\<rparr>)"

definition code_fixture_receive_selected :: "wire_bytes \<Rightarrow> code_finite_selected_ordinary \<Rightarrow> code_fixture_token \<Rightarrow> nat \<Rightarrow>
  code_fixture_replay_state \<Rightarrow> (code_fixture_replay_state \<times> code_fixture_replay_reply)" where
  "code_fixture_receive_selected bytes chosen token now state =
    (let slice = replay_financial_slice state; native = finite_selected_native chosen; payload = finite_selected_payload chosen;
         core = finite_selected_core chosen; proof = \<lparr>proof_session = native_session native,proof_epoch = 9\<rparr>
     in case code_source_active_identity (code_fixture_authenticate_session now) token proof (code_fixture_current_identity_snapshot slice) of
       None \<Rightarrow> (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation Invalid_Wire_Source))
     | Some identity \<Rightarrow>
       if identity_principal identity \<noteq> wire_principal core \<or> identity_domain identity \<noteq> wire_source_domain core
       then (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation Invalid_Wire_Source))
       else case code_compare_binding (map_of (replay_transport state) (authenticated_wire_message_id core)) (encode_wire_core core) of
         Code_Replay_Conflict \<Rightarrow> (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation Conflicting_Wire_Replay))
       | arrival \<Rightarrow>
         if code_fixture_authorize bytes chosen token now Execute_Ordinary slice = None
         then (state,Code_Fixture_Replay_Error Code_Source_Wire_Product_Rejected)
         else case map_of (replay_calls state) (native_id native) of
           Some (stored,outcome) \<Rightarrow>
             if stored \<noteq> payload then (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation Conflicting_Wire_Replay))
             else if code_fixture_authorize bytes chosen token now Read_Receipt slice = None
             then (state,Code_Fixture_Replay_Error Code_Source_Wire_Product_Rejected)
             else (state,Code_Fixture_Replay_Received arrival outcome)
         | None \<Rightarrow>
           if source_payload_cut payload \<noteq> \<lparr>cut_authority_epoch = 9,cut_revision = slice_revision slice\<rparr>
           then let outcome = \<lparr>source_outcome_reply = Code_Source_Outcome_Busy,source_outcome_commit = None\<rparr>
             in (code_fixture_record_call bytes chosen arrival slice outcome state,Code_Fixture_Replay_Received arrival outcome)
           else if code_fixture_is_debit chosen \<and> source_payload_origin_epoch payload \<noteq> cut_authority_epoch (source_payload_cut payload)
           then (code_fixture_record_call bytes chosen arrival slice code_finite_plain_rejection state,
             Code_Fixture_Replay_Received arrival code_finite_plain_rejection)
           else case code_finite_run_source_slice 1048576 code_fixture_origin_context bytes slice of
             (slice_after,Code_Finite_Source_Decided actual outcome) \<Rightarrow>
               if actual = payload then (code_fixture_record_call bytes chosen arrival slice_after outcome state,Code_Fixture_Replay_Received arrival outcome)
               else (state,Code_Fixture_Replay_Pending)
           | _ \<Rightarrow> (state,Code_Fixture_Replay_Pending))"

definition code_fixture_apply_resolve_close :: "code_source_debit_request \<Rightarrow> code_fixture_replay_state \<Rightarrow> code_fixture_replay_state" where
  "code_fixture_apply_resolve_close request state = state\<lparr>
    replay_debit_decisions := code_finite_put (source_debit_id request) (request,Ref_Explicit_Rejection) (replay_debit_decisions state),
    replay_latest_work := (if map_of (replay_latest_work state) (code_source_debit_work request) = None
      then code_finite_put (code_source_debit_work request) (source_debit_id request) (replay_latest_work state) else replay_latest_work state),
    replay_store_counter := Suc (replay_store_counter state)\<rparr>"

definition code_fixture_resolve_selected :: "wire_bytes \<Rightarrow> code_finite_selected_ordinary \<Rightarrow> code_fixture_token \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow>
  code_fixture_replay_state \<Rightarrow> (code_fixture_replay_state \<times> code_fixture_replay_reply)" where
  "code_fixture_resolve_selected bytes chosen token now close state =
    (let slice = replay_financial_slice state; native = finite_selected_native chosen; core = finite_selected_core chosen;
         original = code_fixture_original_debit bytes chosen; observed = code_fixture_control_observation state
     in if \<not> code_fixture_is_debit chosen then (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation Invalid_Wire_Format))
      else case code_fixture_authorize bytes chosen token now Read_Receipt slice of None \<Rightarrow> (state,Code_Fixture_Replay_Error Code_Source_Wire_Product_Rejected)
       | Some identity \<Rightarrow>
         (case code_source_resolve_debit_tail observed original (authenticated_wire_message_id core) (encode_wire_core core)
             (map_of (replay_transport state) (authenticated_wire_message_id core)) (code_fixture_model_receipt state chosen) close
             (code_fixture_authorize bytes chosen token now Execute_Ordinary slice) (identity_principal identity) 9
             (finite_selected_payload chosen) (code_fixture_model_receipt_reservation state chosen)
             (Some (source_control_stored observed)) (Some True) of
           (Code_Source_Resolve_Error reason,attempt) \<Rightarrow> (state,Code_Fixture_Replay_Error reason)
         | (Code_Source_Resolved result,attempt) \<Rightarrow>
             (case attempt of None \<Rightarrow> (state,Code_Fixture_Replay_Resolved result)
              | Some request \<Rightarrow> (code_fixture_apply_resolve_close request state,Code_Fixture_Replay_Resolved result))))"

definition code_fixture_replay_step :: "code_fixture_stimulus \<Rightarrow> code_fixture_replay_state \<Rightarrow>
  (code_fixture_replay_state \<times> code_fixture_replay_reply)" where
  "code_fixture_replay_step event state =
    (if fixture_stimulus_api event = Code_Fixture_Initialize then (code_fixture_replay_initial,Code_Fixture_Initialized)
     else case fixture_stimulus_packet event of None \<Rightarrow> (state,Code_Fixture_Replay_Pending) | Some bytes \<Rightarrow>
       let resolving = fixture_stimulus_api event \<in> {Code_Fixture_Resolve,Code_Fixture_Resolve_Response};
           now = fixture_stimulus_clock event; token = fixture_stimulus_token event
       in case code_fixture_packet_admission resolving now bytes of
          Some reason \<Rightarrow> (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation reason))
        | None \<Rightarrow> (case code_finite_select_raw_ordinary 1048576 code_fixture_origin_context
              (slice_binding_epoch (replay_financial_slice state)) (slice_separator (replay_financial_slice state)) bytes of
            Code_Finite_Raw_Refused reason \<Rightarrow> (state,Code_Fixture_Replay_Error (Code_Source_Wire_Validation reason))
          | Code_Finite_Raw_Pending \<Rightarrow> (state,Code_Fixture_Replay_Pending)
          | Code_Finite_Raw_Selected chosen \<Rightarrow>
              if resolving then code_fixture_resolve_selected bytes chosen token now (fixture_stimulus_close event = Some True) state
              else code_fixture_receive_selected bytes chosen token now state))"

fun code_fixture_run_stimuli :: "code_fixture_stimulus list \<Rightarrow> code_fixture_replay_state \<Rightarrow>
  (code_fixture_replay_state \<times> code_fixture_replay_reply) list" where
  "code_fixture_run_stimuli [] state = []"
| "code_fixture_run_stimuli (event # events) state =
    (let step = code_fixture_replay_step event state in step # code_fixture_run_stimuli events (fst step))"

definition code_fixture_replay_results where
  "code_fixture_replay_results = code_fixture_run_stimuli code_fixture_stimuli code_fixture_replay_initial"

text \<open>
  This is a concrete fixed-fixture projection, not the general persistent
  authority or permanent raw JSON producer. It computes independent source
  financial/call/transport/control-disposition state from actual stimuli.
  It actually invokes the received source identity/signature functions,
  exact finite financial operations, typed source outcome conversion and
  all-disposition resolver tail. No actual after-state/outcome is read.
  The MemoryCAS fixture counter models its known +1 updates; the erased
  control-byte marker [] is only this projection's stamp. Exact source JSON
  control/journal/head/offset/digest serialization, concurrency and arbitrary
  storage restoration are not proved by this concrete interpreter.
  Source receipt readiness is specialized to these ordinary3 operations;
  legal/spend/settlement and dynamic availability/epoch/grant changes remain
  outside this concrete dataset. Signed response construction is separate.
\<close>

end

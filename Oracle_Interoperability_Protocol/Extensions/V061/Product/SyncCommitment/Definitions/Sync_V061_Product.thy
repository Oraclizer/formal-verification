theory Sync_V061_Product
  imports Sync_V061_Attestation_Model "OIP_Reference_Profile.Reference_Read_Cuts"
begin

record 'product sync_snapshot =
  sync_entries :: "sync_stream \<Rightarrow> sync_entry option"
  sync_product_value :: 'product

record 'key sync_policy =
  sync_sessions :: "product_session_id \<Rightarrow> (product_session_binding \<times> nat) option"
  sync_exec_scope :: "(product_session_id \<times> product_asset) set"
  sync_full_scope :: "(product_session_id \<times> sync_stream) set"
  sync_read_scope :: "(product_session_id \<times> sync_stream) set"
  sync_origin_registry :: "'key sync_registry"

datatype sync_failure = Sync_Busy | Sync_Unavailable | Sync_Proof_Rejected | Sync_Mismatch | Sync_Stale
datatype sync_outcome = Sync_Uncommitted sync_failure | Sync_Committed nat

fun sync_outcome_wire :: "sync_outcome \<Rightarrow> (nat \<times> nat option)" where
  "sync_outcome_wire (Sync_Uncommitted Sync_Busy) = (2,None)"
| "sync_outcome_wire (Sync_Uncommitted Sync_Unavailable) = (3,None)"
| "sync_outcome_wire (Sync_Uncommitted Sync_Proof_Rejected) = (41,None)"
| "sync_outcome_wire (Sync_Uncommitted Sync_Mismatch) = (39,None)"
| "sync_outcome_wire (Sync_Uncommitted Sync_Stale) = (40,None)"
| "sync_outcome_wire (Sync_Committed position) = (29,Some position)"

datatype sync_result = Sync_Bad_Operands | Sync_Denied | Sync_Call_Conflict | Sync_Recorded sync_outcome
datatype sync_fresh_decision = Sync_Reject sync_failure | Sync_Accept sync_statement

record ('key, 'product) sync_receiver =
  sync_deployment_at :: nat
  sync_target_at :: nat
  sync_receiver_epoch :: nat
  sync_genesis :: "'product sync_snapshot"
  sync_revision_tail :: "'product sync_snapshot list"
  sync_selected_policy :: "'key sync_policy"
  sync_used_events :: "source_key \<Rightarrow> (client_call_id \<times> sync_statement) option"
  sync_outcome_table :: "client_call_id \<Rightarrow> (wire_bytes \<times> sync_outcome) option"

definition sync_reference_history where
  "sync_reference_history state =
    \<lparr>reference_history_epoch = sync_receiver_epoch state,
     reference_history_prefixes = sync_genesis state # sync_revision_tail state\<rparr>"

abbreviation sync_current_cut where
  "sync_current_cut state \<equiv> reference_observed_cut (sync_reference_history state)"

abbreviation sync_current_snapshot where
  "sync_current_snapshot state \<equiv> last (reference_history_prefixes (sync_reference_history state))"

abbreviation sync_retained where
  "sync_retained state stream \<equiv> sync_entries (sync_current_snapshot state) stream"

definition sync_current_identity where
  "sync_current_identity state core session \<longleftrightarrow>
    wire_deployment core = sync_deployment_at state \<and>
    wire_target_domain core = sync_target_at state \<and>
    wire_authority_epoch core = cut_authority_epoch (sync_current_cut state) \<and>
    sync_sessions (sync_selected_policy state) session =
      Some (\<lparr>session_principal = wire_principal core, session_epoch = wire_authority_epoch core\<rparr>,
            wire_source_domain core)"

definition sync_execute_allowed where
  "sync_execute_allowed state core request \<longleftrightarrow>
    sync_current_identity state core (sync_session request) \<and>
    (sync_session request, fst (sync_key request)) \<in> sync_exec_scope (sync_selected_policy state)"

fun sync_mode_ok where
  "sync_mode_ok policy request a None =
    (sync_mode request = Sync_Initial \<and> sync_predecessor a = None)"
| "sync_mode_ok policy request a (Some prior) =
    (case sync_mode request of Sync_Initial \<Rightarrow> False
     | Sync_Incremental \<Rightarrow>
       sync_claimed_prior request = Some (sync_commitment prior) \<and>
       sync_predecessor a = Some (sync_commitment prior)
     | Sync_Full \<Rightarrow>
       sync_predecessor a = None \<and> (sync_session request, sync_key request) \<in> sync_full_scope policy)"

definition sync_event_key where
  "sync_event_key request = (snd (sync_key request), sync_event (sync_requested request))"

definition sync_position_and_event_fresh where
  "sync_position_and_event_fresh state request \<longleftrightarrow>
    sync_used_events state (sync_event_key request) = None \<and>
    (\<forall>prior. sync_retained state (sync_key request) = Some prior \<longrightarrow>
      sync_position prior < sync_position (sync_requested request))"

definition sync_fresh_assess where
  "sync_fresh_assess verify state core request =
    (if sync_signed_cut request \<noteq> sync_current_cut state then Sync_Reject Sync_Busy
     else case sync_decode_proof (sync_attestation request) of
       None \<Rightarrow> Sync_Reject Sync_Proof_Rejected
     | Some (a,votes) \<Rightarrow>
       if \<not> sync_proof_ok verify (sync_origin_registry (sync_selected_policy state)) core request a votes
       then Sync_Reject Sync_Proof_Rejected
       else if \<not> sync_mode_ok (sync_selected_policy state) request a (sync_retained state (sync_key request))
       then Sync_Reject Sync_Mismatch
       else if \<not> sync_position_and_event_fresh state request then Sync_Reject Sync_Stale
       else Sync_Accept a)"

definition sync_next_snapshot where
  "sync_next_snapshot state request =
    (sync_current_snapshot state)\<lparr>sync_entries :=
      (sync_entries (sync_current_snapshot state))(sync_key request := Some (sync_requested request))\<rparr>"

definition sync_write_outcome where
  "sync_write_outcome state core request outcome =
    state\<lparr>sync_outcome_table :=
      (sync_outcome_table state)(sync_call request := Some (encode_wire_core core,outcome))\<rparr>"

definition sync_commit_record where
  "sync_commit_record state core request a =
    sync_write_outcome
      (state\<lparr>sync_revision_tail := sync_revision_tail state @ [sync_next_snapshot state request],
        sync_used_events := (sync_used_events state)(sync_event_key request := Some (sync_call request,a))\<rparr>)
      core request (Sync_Committed (cut_revision (sync_current_cut state)))"

fun sync_finish_fresh where
  "sync_finish_fresh state core request (Sync_Reject reason) =
    (sync_write_outcome state core request (Sync_Uncommitted reason), Sync_Recorded (Sync_Uncommitted reason))"
| "sync_finish_fresh state core request (Sync_Accept a) =
    (sync_commit_record state core request a, Sync_Recorded (Sync_Committed (cut_revision (sync_current_cut state))))"

definition sync_receive_verified where
  "sync_receive_verified verify core state =
    (case sync_read_operands core of None \<Rightarrow> (state,Sync_Bad_Operands)
     | Some request \<Rightarrow>
       if \<not> sync_execute_allowed state core request then (state,Sync_Denied)
       else case sync_outcome_table state (sync_call request) of
         Some (original,outcome) \<Rightarrow>
           if original = encode_wire_core core then (state,Sync_Recorded outcome) else (state,Sync_Call_Conflict)
       | None \<Rightarrow> sync_finish_fresh state core request (sync_fresh_assess verify state core request))"

record sync_query =
  sync_query_session :: product_session_id
  sync_query_cut :: product_cut
  sync_query_key :: sync_stream

definition sync_read_query where
  "sync_read_query core =
    (let body = wire_operation_body core in
     if sync_operation core \<noteq> (Wire_Query,9) \<or> wire_deadline body \<noteq> Deadline_Absent \<or>
        wire_blobs body \<noteq> [] then None
     else case wire_words body of [session,revision_word,asset,origin] \<Rightarrow>
       Some \<lparr>sync_query_session = session, sync_query_cut =
          \<lparr>cut_authority_epoch = wire_authority_epoch core, cut_revision = revision_word\<rparr>,
          sync_query_key = (asset,origin)\<rparr>
     | _ \<Rightarrow> None)"

definition sync_query_allowed where
  "sync_query_allowed state core request \<longleftrightarrow>
    sync_current_identity state core (sync_query_session request) \<and>
    (sync_query_session request,sync_query_key request) \<in> sync_read_scope (sync_selected_policy state)"

definition sync_query_verified where
  "sync_query_verified core state =
    Option.bind (sync_read_query core) (\<lambda>request.
      current_reference_observation (sync_query_allowed state core request)
        (\<lambda>snapshot. sync_entries snapshot (sync_query_key request))
        (sync_query_cut request) (sync_reference_history state))"

end

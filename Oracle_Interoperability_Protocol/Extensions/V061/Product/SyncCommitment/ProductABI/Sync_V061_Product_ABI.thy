theory Sync_V061_Product_ABI
  imports "OIP_Sync_V061_Position_Boundary.Sync_V061_Reference_Boundary"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen"
begin

declare [[code drop: sync_parse_votes]]

lemma sync_abi_parse_votes_code [code]:
  "sync_parse_votes count raw = (if count = 0 then [] else
    (sync_take_word raw, take 64 (drop 8 raw)) # sync_parse_votes (count - 1) (drop 72 raw))"
  by (cases count) simp_all

lemma sync_abi_fresh_code [code]:
  "sync_position_and_event_fresh state request =
    (sync_used_events state (sync_event_key request) = None \<and>
      (case sync_retained state (sync_key request) of None \<Rightarrow> True
       | Some prior \<Rightarrow> sync_position prior < sync_position (sync_requested request)))"
  by (cases "sync_retained state (sync_key request)") (simp_all add: sync_position_and_event_fresh_def)

lemma sync_abi_vote_list:
  "(\<forall>(signer,signature) \<in> set votes. \<exists>key. keys signer = Some key \<and> verify key statement signature) =
    list_all (\<lambda>(signer,signature). case keys signer of None \<Rightarrow> False
      | Some key \<Rightarrow> verify key statement signature) votes"
proof (induction votes)
  case Nil
  show ?case by simp
next
  case (Cons vote votes)
  obtain signer signature where head: "vote = (signer,signature)" by (cases vote)
  have check: "(\<exists>key. keys signer = Some key \<and> verify key statement signature) =
    (case keys signer of None \<Rightarrow> False | Some key \<Rightarrow> verify key statement signature)"
    by (cases "keys signer") simp_all
  show ?case using Cons.IH check by (simp add: head)
qed

lemma sync_abi_proof_ok_code [code]:
  "sync_proof_ok verify registry core r a votes =
    (sync_format a = 1 \<and> sync_claim a = 1 \<and> sync_deployment a = wire_deployment core \<and>
     (sync_asset a, sync_origin a) = sync_key r \<and> sync_item a = sync_requested r \<and>
     sync_predecessor a = sync_claimed_prior r \<and>
     sync_current_roster registry (sync_origin a) = Some (sync_origin_epoch (sync_item a), sync_roster a) \<and>
     (case sync_registered_rosters registry (sync_deployment a,sync_origin a,sync_origin_epoch (sync_item a),sync_roster a) of
       None \<Rightarrow> False | Some (quorum,keys) \<Rightarrow> 0 < quorum \<and> quorum \<le> length votes \<and>
         sorted_wrt (<) (map fst votes) \<and> distinct (map (keys \<circ> fst) votes) \<and>
         list_all (\<lambda>(signer,signature). case keys signer of None \<Rightarrow> False
           | Some key \<Rightarrow> verify key (sync_statement_bytes a) signature) votes))"
proof (cases "sync_registered_rosters registry
    (sync_deployment a,sync_origin a,sync_origin_epoch (sync_item a),sync_roster a)")
  case None
  then show ?thesis by (simp add: sync_proof_ok_def)
next
  case (Some entry)
  obtain quorum keys where entry: "entry = (quorum,keys)" by (cases entry)
  note vote_check = sync_abi_vote_list[where keys=keys and verify=verify
    and statement="sync_statement_bytes a" and votes=votes]
  show ?thesis using vote_check by (simp add: sync_proof_ok_def Some entry)
qed

type_synonym sync_abi_fact = "wire_bytes \<times> wire_bytes \<times> wire_bytes"
type_synonym sync_abi_observation = "nat list \<times> wire_bytes list"
type_synonym sync_abi_receiver = "(wire_bytes,unit) sync_receiver"
type_synonym sync_abi_step = "wire_bytes \<times> nat list \<times> wire_bytes \<times> wire_bytes"

record sync_abi_context =
  sync_abi_boundary :: wire_boundary
  sync_abi_nesting :: nat
  sync_abi_watch :: sync_stream
  sync_abi_accepted :: "(wire_family \<times> nat) set"
  sync_abi_envelope_key :: wire_bytes
  sync_abi_session_key :: wire_bytes
  sync_abi_registered :: "nat list"
  sync_abi_receipts :: "(nat \<times> nat) set"

record sync_abi_state =
  sync_abi_product :: sync_abi_receiver
  sync_abi_transport :: wire_dedup_store
  sync_abi_selected_index :: nat

definition sync_abi_initial where
  "sync_abi_initial boundary policy =
    \<lparr>sync_abi_product = \<lparr>sync_deployment_at = boundary_deployment boundary,
      sync_target_at = boundary_target boundary, sync_receiver_epoch = boundary_epoch boundary,
      sync_genesis = \<lparr>sync_entries = (\<lambda>_. None), sync_product_value = ()\<rparr>, sync_revision_tail = [],
      sync_selected_policy = policy, sync_used_events = (\<lambda>_. None), sync_outcome_table = (\<lambda>_. None)\<rparr>,
      sync_abi_transport = (\<lambda>_. None), sync_abi_selected_index = 0\<rparr>"

definition sync_abi_note_binding where
  "sync_abi_note_binding arrival core state product =
    (let next = state\<lparr>sync_abi_product := product\<rparr> in
     case arrival of Code_First \<Rightarrow> next\<lparr>sync_abi_transport :=
        (sync_abi_transport state)(code_transport_key core := Some (encode_wire_core core)),
        sync_abi_selected_index := sync_abi_selected_index state + 1\<rparr>
     | _ \<Rightarrow> next)"

definition sync_abi_entry :: "sync_entry option \<Rightarrow> sync_abi_observation" where
  "sync_abi_entry entry = (case entry of None \<Rightarrow> ([0],[])
     | Some a \<Rightarrow> ([1,sync_origin_epoch a,sync_event a,sync_position a],[sync_commitment a]))"

definition sync_abi_cut_words :: "product_cut \<Rightarrow> nat list" where
  "sync_abi_cut_words observed_cut = [cut_authority_epoch observed_cut,cut_revision observed_cut]"

definition sync_abi_outcome_words where
  "sync_abi_outcome_words outcome = (case sync_outcome_wire outcome of (code,position) \<Rightarrow>
    case position of None \<Rightarrow> [code,0,0] | Some value \<Rightarrow> [code,1,value])"

definition sync_abi_failure :: "sync_abi_state \<Rightarrow> nat \<Rightarrow> (sync_abi_state \<times> sync_abi_observation)" where
  "sync_abi_failure state code = (state,([0,code],[]))"

definition sync_abi_call where
  "sync_abi_call context verify connected lost arrival core state =
    (let gate = \<lparr>sync_endpoint_up = True, sync_source_connected = connected,
        sync_registered_asset = (\<lambda>asset. asset \<in> set (sync_abi_registered context)),
        sync_other_claimed = (\<lambda>_. False), sync_ordered_debit = (\<lambda>_. False),
        sync_receipt_granted = (\<lambda>session asset. (session,asset) \<in> sync_abi_receipts context)\<rparr>
     in case sync_reference_product None gate verify core (sync_abi_product state) of (product,result) \<Rightarrow>
       (case result of Sync_Transport_Refusal reason \<Rightarrow> sync_abi_failure state (code_transport_refusal_number reason)
       | Sync_Product_Refusal \<Rightarrow> sync_abi_failure state 77
       | Sync_Reference_Outcome outcome \<Rightarrow> (sync_abi_note_binding arrival core state product,
           ((if lost then [4,51] else [1,(if arrival = Code_First then 0 else 1)]) @ sync_abi_outcome_words outcome, []))))"

definition sync_abi_current where
  "sync_abi_current arrival core state =
    (let product = sync_abi_product state in
     case sync_read_query core of None \<Rightarrow> sync_abi_failure state 70 | Some request \<Rightarrow>
       if \<not> sync_query_allowed product core request then sync_abi_failure state 77
       else case sync_query_verified core product of None \<Rightarrow>
           (sync_abi_note_binding arrival core state product, ([5,2],[]))
       | Some (observed_cut,entry) \<Rightarrow> (case sync_abi_entry entry of (entry_words,blobs) \<Rightarrow>
           (sync_abi_note_binding arrival core state product, ([2] @ sync_abi_cut_words observed_cut @ entry_words,blobs))))"

definition sync_abi_receipt where
  "sync_abi_receipt context arrival core state =
    (let fuel = sync_abi_nesting context; product = sync_abi_product state in
     case sync_parse_query_eight fuel core of None \<Rightarrow> sync_abi_failure state 70 | Some receipt \<Rightarrow>
       if \<not> code_same_original core (sync_receipt_inner receipt) then sync_abi_failure state 72
       else case code_compare_binding (sync_abi_transport state (code_transport_key (sync_receipt_inner receipt)))
               (sync_receipt_exact_core receipt) of
         Code_First \<Rightarrow> sync_abi_failure state 50
       | Code_Replay_Conflict \<Rightarrow> sync_abi_failure state 76
       | Code_Identical \<Rightarrow>
         (let asset = fst (sync_key (sync_receipt_request receipt));
              granted = (\<lambda>_ _ session. (session,asset) \<in> sync_abi_receipts context)
          in case sync_query_eight_observe granted fuel core product of
            None \<Rightarrow> sync_abi_failure state 77
          | Some outcome \<Rightarrow> (sync_abi_note_binding arrival core state product, ([3] @ sync_abi_outcome_words outcome,[]))))"

definition sync_abi_session where
  "sync_abi_session fuel core =
    (case sync_operation core of (family,opcode) \<Rightarrow>
      if (family,opcode) = (Wire_State_Sync,7) then map_option sync_session (sync_read_operands core)
      else if (family,opcode) = (Wire_Query,9) then map_option sync_query_session (sync_read_query core)
      else map_option sync_receipt_session (sync_parse_query_eight fuel core))"

definition sync_abi_step where
  "sync_abi_step context facts input state =
    (case input of (raw,meta,token_preimage,token_signature) \<Rightarrow>
      (case meta of [row_now,row_connected,row_lost,row_session,row_principal,row_epoch,row_domain] \<Rightarrow>
        (let authority = (sync_abi_boundary context)\<lparr>boundary_now := row_now\<rparr>;
             verify = (\<lambda>key data signature. (key,data,signature) \<in> set facts)
         in case sync_v6_gate Sync_V061 (sync_abi_accepted context)
             (\<lambda>_ data signature. verify (sync_abi_envelope_key context) data signature)
             (\<lambda>_. True) (\<lambda>_ _. True) authority raw of
           Gate_Refused reason \<Rightarrow> sync_abi_failure state (code_transport_refusal_number reason)
         | Gate_Admitted packet \<Rightarrow>
           (let core = packet_core packet in
             if sync_abi_session (sync_abi_nesting context) core = None then sync_abi_failure state 70
             else if sync_abi_session (sync_abi_nesting context) core \<noteq> Some row_session \<or>
                 wire_principal core \<noteq> row_principal \<or> wire_authority_epoch core \<noteq> row_epoch \<or>
                 wire_source_domain core \<noteq> row_domain \<or>
                 \<not> verify (sync_abi_session_key context) token_preimage token_signature
             then sync_abi_failure state 72
             else case code_compare_binding (sync_abi_transport state (code_transport_key core)) (encode_wire_core core) of
               Code_Replay_Conflict \<Rightarrow> sync_abi_failure state 76
             | arrival \<Rightarrow>
                 if sync_operation core = (Wire_State_Sync,7) then sync_abi_call context verify (row_connected = 1) (row_lost = 1) arrival core state
                 else if sync_operation core = (Wire_Query,9) then sync_abi_current arrival core state
                 else sync_abi_receipt context arrival core state))
      | _ \<Rightarrow> sync_abi_failure state 70))"

definition sync_abi_project where
  "sync_abi_project context state =
    (let product = sync_abi_product state in
     case sync_abi_entry (sync_retained product (sync_abi_watch context)) of (words,blobs) \<Rightarrow>
       (sync_abi_cut_words (sync_current_cut product) @ [sync_abi_selected_index state] @ words,blobs))"

fun sync_abi_trace where
  "sync_abi_trace context facts [] state = []"
| "sync_abi_trace context facts (input # rest) state =
    (case sync_abi_step context facts input state of (next,result) \<Rightarrow>
      (result,sync_abi_project context next) # sync_abi_trace context facts rest next)"

definition sync_abi_policy where
  "sync_abi_policy deployment sessions execute full current rosters =
    \<lparr>sync_sessions = map_of (map (\<lambda>(session,principal,epoch,source).
      (session,(\<lparr>session_principal = principal, session_epoch = epoch\<rparr>,source))) sessions),
     sync_exec_scope = set execute, sync_full_scope = set full, sync_read_scope = set current,
     sync_origin_registry = \<lparr>sync_current_roster = map_of (map (\<lambda>((origin,epoch,roster),_,_). (origin,(epoch,roster))) rosters),
       sync_registered_rosters = map_of (map (\<lambda>((origin,epoch,roster),quorum,signers).
         ((deployment,origin,epoch,roster),(quorum,map_of signers))) rosters)\<rparr>\<rparr>"

definition sync_abi_context where
  "sync_abi_context config families atomicities schemes envelope_key session_key registered receipts =
    (case config of [cfg_deployment,cfg_source,cfg_target,cfg_principal,cfg_key,cfg_epoch,cfg_scope,cfg_ttl,cfg_skew,cfg_frame,
      cfg_nesting,cfg_asset,cfg_origin,cfg_wire_version,cfg_accept_sync,cfg_accept_query] \<Rightarrow>
      let profile = \<lparr>negotiated_version = cfg_wire_version,
        negotiated_families = code_numeric_family_set families,
        negotiated_atomicities = set atomicities, negotiated_schemes = set schemes\<rparr>;
          boundary = \<lparr>boundary_profile = profile, boundary_deployment = cfg_deployment, boundary_source = cfg_source,
            boundary_target = cfg_target, boundary_principal = cfg_principal, boundary_key = cfg_key, boundary_epoch = cfg_epoch,
            boundary_route_scope = cfg_scope, boundary_now = 0, boundary_asset_ttl_floor = cfg_ttl, boundary_future_skew = cfg_skew,
            boundary_max_frame = cfg_frame, boundary_version_floor = 6, boundary_critical_allowed = False,
            boundary_threshold_supported = False\<rparr>;
          accepted = [(Wire_Query,8)] @ (if cfg_accept_sync = 1 then [(Wire_State_Sync,7)] else []) @
             (if cfg_accept_query = 1 then [(Wire_Query,9)] else [])
      in Some \<lparr>sync_abi_boundary = boundary, sync_abi_nesting = cfg_nesting, sync_abi_watch = (cfg_asset,cfg_origin),
        sync_abi_accepted = set accepted, sync_abi_envelope_key = envelope_key, sync_abi_session_key = session_key,
        sync_abi_registered = registered, sync_abi_receipts = set receipts\<rparr>
    | _ \<Rightarrow> None)"

definition sync_product_integer_trace where
  "sync_product_integer_trace config families atomicities schemes envelope_key session_key registered receipts
      sessions execute full current rosters facts inputs =
    (let n = nat_of_integer; ns = map n; pair = (\<lambda>(a,b). (n a,n b));
         stream = (\<lambda>(session,asset,origin). (n session,(n asset,n origin)));
         output = (\<lambda>(words,blobs). (map integer_of_nat words,map (map integer_of_nat) blobs))
     in case sync_abi_context (ns config) (ns families) (ns atomicities) (ns schemes) (ns envelope_key) (ns session_key)
            (ns registered) (map pair receipts) of None \<Rightarrow> None | Some context \<Rightarrow>
       (let policy = sync_abi_policy (boundary_deployment (sync_abi_boundary context))
          (map (\<lambda>(session,principal,epoch,source). (n session,n principal,n epoch,n source)) sessions)
          (map pair execute) (map stream full) (map stream current)
          (map (\<lambda>((origin,epoch,roster),quorum,signers). ((n origin,n epoch,n roster),n quorum,
             map (\<lambda>(id,key). (n id,ns key)) signers)) rosters);
          primitives = map (\<lambda>(key,data,signature). (ns key,ns data,ns signature)) facts;
          steps = map (\<lambda>(raw,meta,preimage,signature). (ns raw,ns meta,ns preimage,ns signature)) inputs
        in Some (map (\<lambda>(result,post). (output result,output post))
           (sync_abi_trace context primitives steps (sync_abi_initial (sync_abi_boundary context) policy)))))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_abi_parse_votes_code sync_abi_fresh_code sync_abi_vote_list sync_abi_proof_ok_code})
  then () else error "Unexpected oracle in the synchronization product ABI"
\<close>

export_code sync_product_integer_trace
  in SML module_name OIP_Sync_Product_ABI file_prefix "oip_sync_product_abi"

end

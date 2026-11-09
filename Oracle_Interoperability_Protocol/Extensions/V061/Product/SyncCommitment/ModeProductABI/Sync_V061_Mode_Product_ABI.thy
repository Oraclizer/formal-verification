theory Sync_V061_Mode_Product_ABI
  imports "OIP_Sync_V061_Product_ABI.Sync_V061_Product_ABI"
begin

text \<open>The input is the observed current projection of each independent fresh step.
  The prefix length represents the current cut. Earlier snapshots and the payload of
  an already used event are outside this fresh consumer's observation.\<close>

definition sync_mode_event_witness :: "client_call_id \<times> sync_statement" where
  "sync_mode_event_witness = ((0,0), \<lparr>sync_format = 0, sync_claim = 0, sync_deployment = 0,
    sync_origin = 0, sync_roster = 0, sync_asset = 0,
    sync_item = \<lparr>sync_commitment = [], sync_position = 0, sync_origin_epoch = 0, sync_event = 0\<rparr>,
    sync_predecessor = None\<rparr>)"

definition sync_mode_start where
  "sync_mode_start boundary policy revision serial entries events =
    (let initial = sync_abi_initial boundary policy;
         snapshot = \<lparr>sync_entries = map_of entries, sync_product_value = ()\<rparr>;
         seeded = (sync_abi_product initial)\<lparr>sync_genesis := snapshot, sync_revision_tail := replicate revision snapshot,
            sync_used_events := (\<lambda>event. if event \<in> set events then Some sync_mode_event_witness else None)\<rparr>
     in initial\<lparr>sync_abi_product := seeded, sync_abi_selected_index := serial\<rparr>)"

lemma sync_mode_start_cut:
  "sync_abi_cut_words (sync_current_cut (sync_abi_product (sync_mode_start boundary policy revision serial entries events))) =
    [boundary_epoch boundary,revision]"
  by (simp add: sync_mode_start_def sync_abi_initial_def sync_abi_cut_words_def sync_reference_history_def reference_observed_cut_def Let_def)

lemma sync_mode_start_current:
  "sync_retained (sync_abi_product (sync_mode_start boundary policy revision serial entries events)) stream = map_of entries stream"
  by (cases revision) (simp_all add: sync_mode_start_def sync_abi_initial_def sync_reference_history_def Let_def)

lemma sync_mode_start_event_membership:
  "sync_used_events (sync_abi_product (sync_mode_start boundary policy revision serial entries events)) event \<noteq> None
    \<longleftrightarrow> event \<in> set events"
  by (simp add: sync_mode_start_def sync_mode_event_witness_def Let_def)

definition sync_mode_keep_key where
  "sync_mode_keep_key keys key = (if key \<in> set keys then keys else keys @ [key])"

definition sync_mode_record_view where
  "sync_mode_record_view product request =
    (case sync_outcome_table product (sync_call request) of None \<Rightarrow> ([0],[])
      | Some (exact,outcome) \<Rightarrow> ([1] @ sync_abi_outcome_words outcome,[exact]))"

definition sync_mode_binding_view where
  "sync_mode_binding_view state core =
    (case sync_abi_transport state (code_transport_key core) of None \<Rightarrow> ([0],[]) | Some bytes \<Rightarrow> ([1],[bytes]))"

definition sync_mode_post where
  "sync_mode_post context entries events core request state =
    (let product = sync_abi_product state;
         (base_words,base_blobs) = sync_abi_project context state;
         (record_words,record_blobs) = sync_mode_record_view product request;
         (binding_words,binding_blobs) = sync_mode_binding_view state core;
         streams = sync_mode_keep_key (map fst entries) (sync_key request);
         sources = sync_mode_keep_key events (sync_event_key request);
         stream_values = map (\<lambda>stream. sync_abi_entry (sync_retained product stream)) streams;
         event_values = concat (map (\<lambda>(origin,event). [origin,event,
           if sync_used_events product (origin,event) = None then 0 else 1]) sources);
         stream_words = concat (map (\<lambda>(stream,view). [fst stream,snd stream] @ fst view) (zip streams stream_values))
     in (base_words @ record_words @ binding_words @ [length streams] @ stream_words @ [length sources] @ event_values,
         base_blobs @ record_blobs @ binding_blobs @ concat (map snd stream_values)))"

definition sync_mode_run where
  "sync_mode_run context policy facts input =
    (case input of (raw,metadata,token_preimage,token_signature,(revision,serial,entries,events)) \<Rightarrow>
     let initial = sync_mode_start (sync_abi_boundary context) policy revision serial entries events;
         (next,result) = sync_abi_step context facts (raw,metadata,token_preimage,token_signature) initial;
         post = (case sync_decode_packet raw of None \<Rightarrow> sync_abi_project context next
          | Some packet \<Rightarrow> (case sync_read_operands (packet_core packet) of
              None \<Rightarrow> sync_abi_project context next
            | Some request \<Rightarrow> sync_mode_post context entries events (packet_core packet) request next))
     in (result,post))"

definition sync_mode_integer_trace where
  "sync_mode_integer_trace config families atomicities schemes envelope_key session_key registered receipts
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
          read_entry = (\<lambda>((asset,origin),(epoch,event,position),commitment). ((n asset,n origin),
            \<lparr>sync_commitment = ns commitment, sync_position = n position, sync_origin_epoch = n epoch, sync_event = n event\<rparr>));
          steps = map (\<lambda>(raw,metadata,preimage,signature,(revision,serial,entries,events)).
             (ns raw,ns metadata,ns preimage,ns signature,(n revision,n serial,map read_entry entries,map pair events))) inputs
        in Some (map (\<lambda>input. case sync_mode_run context policy primitives input of (result,post) \<Rightarrow>
          (output result,output post)) steps)))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_mode_start_cut sync_mode_start_current sync_mode_start_event_membership})
  then () else error "Unexpected oracle in the Sync mode projection input"
\<close>

export_code sync_mode_integer_trace
  in SML module_name OIP_Sync_Mode_Product_ABI file_prefix "oip_sync_mode_product_abi"

end

theory Reference_Write_Authority
  imports "OIP_Reference_Write_Profile.Reference_Write_Profile"
    "OIP_Reference_Profile.Reference_Product_Image"
    "OIP_Reference_Profile.Reference_Lock_Consumption"
    "OIP_Message_Code.Wire_Code_Response_Outcome"
    "Preemptive_Lock_Correctness.Reservation_Frame"
begin

record 'head reference_write_store =
  write_product_image :: "'head reference_product_image"
  write_effect_positions :: "client_call_id \<Rightarrow> nat option"
  write_original_cores :: "client_call_id \<Rightarrow> wire_core option"

abbreviation write_history where
  "write_history before \<equiv> image_read_history (write_product_image before)"

abbreviation write_authority where
  "write_authority before \<equiv> image_authority (write_product_image before)"

abbreviation write_ledger_cut where
  "write_ledger_cut before \<equiv> reference_observed_cut (write_history before)"

abbreviation write_source where
  "write_source connection before \<equiv> reference_lock_source connection (write_authority before)"

fun reference_write_asset_ready where
  "reference_write_asset_ready registered source (Client_Protocol endpoint index (Write_Intent request generation versions value)) =
    (let binding = request_binding request; asset = binding_asset binding in
      endpoint = fst (binding_key binding) \<and> endpoint \<in> registered \<and> binding_destination binding \<in> registered \<and>
      product_owners (product_durable source) asset \<noteq> None \<and> value < 2^64 \<and>
      Suc (asset_version (authoritative_reservation_state source) asset) < 2^64)"
| "reference_write_asset_ready registered source command = False"

definition reference_write_ready where
  "reference_write_ready registered actor call_id payload source before \<longleftrightarrow>
    (let envelope = payload_envelope payload; command = envelope_command envelope; calls = product_calls source in
      reference_permitted_at (reference_inputs (write_authority before)) Normal_Lock_Entry actor command \<and>
      lock_envelope_admitted actor envelope (payload_credential payload) source \<and>
      reference_write_asset_ready registered source command \<and>
      Suc (cut_revision (write_ledger_cut before)) < 2^64 \<and>
      product_requests (product_durable source) call_id = None \<and>
      call_invocations calls call_id = None \<and> call_authority_results calls call_id = None \<and>
      call_local_status calls = Endpoint_Up)"

lemma a_ready_write_has_the_current_route_grant_and_exact_lock_credential:
  assumes ready: "reference_write_ready registered actor call_id payload source before"
    and command: "envelope_command (payload_envelope payload) = Client_Protocol endpoint index (Write_Intent request generation versions value)"
  shows "reference_permitted_at (reference_inputs (write_authority before)) Normal_Lock_Entry actor
      (Client_Protocol endpoint index (Write_Intent request generation versions value))"
    "\<exists>credential. payload_credential payload = Some credential \<and> lock_credential_matches actor credential request (Some generation) source"
  using assms by (auto simp: reference_write_ready_def lock_envelope_admitted_def Let_def split: option.splits)

definition record_reference_write where
  "record_reference_write call_id payload outcome changed before =
    (let image = write_product_image before; authority = image_authority image; records = reference_product authority;
         source = (case changed of None \<Rightarrow> retained_source records | Some next \<Rightarrow> capture_retained_source next);
         entry = \<lparr>result_payload = payload, result_outcome = outcome\<rparr>;
         next_records = records\<lparr>retained_source := source, retained_outcomes := (retained_outcomes records)(call_id := Some entry)\<rparr>;
         next_authority = authority\<lparr>reference_product := next_records\<rparr>;
         steps = (case changed of None \<Rightarrow> 0 | Some _ \<Rightarrow> 1);
         position = (case changed of None \<Rightarrow> None | Some _ \<Rightarrow> Some (cut_revision (write_ledger_cut before)))
     in (before\<lparr>write_product_image := record_reference_product_image next_authority steps image,
             write_effect_positions := (write_effect_positions before)(call_id := position)\<rparr>, Some (outcome,position)))"

fun reference_write_code :: "product_outcome \<times> nat option \<Rightarrow> (nat \<times> nat option) option" where
  "reference_write_code (Authority_Reply (Protocol_Response Data_Updated), Some position) =
    Some (code_source_ordinary_number (Code_Source_Accepted Code_Source_Data_Reply), Some position)"
| "reference_write_code (Authority_Rejected, None) = Some (code_source_ordinary_number Code_Source_Outcome_Rejected, None)"
| "reference_write_code (Authority_Busy, None) = Some (code_source_ordinary_number Code_Source_Outcome_Busy, None)"
| "reference_write_code (Authority_Unavailable, None) = Some (code_source_ordinary_number Code_Source_Outcome_Unavailable, None)"
| "reference_write_code other = None"

lemma write_success_uses_data_updated_with_a_commit:
  "reference_write_code (Authority_Reply (Protocol_Response Data_Updated), Some position) = Some (20,Some position)"
  "reference_response_compatible Wire_Lock 7 Recorded_Result 20 True"
  "\<not> reference_response_compatible Wire_Lock 7 Recorded_Result 20 False"
  by (simp_all add: reference_response_compatible_def reference_result_codes_def reference_result_targets_def)

lemma recording_a_write_without_effect_keeps_the_exact_authority_view:
  "write_history (fst (record_reference_write call_id payload outcome None before)) = write_history before"
  "retained_source (reference_product (write_authority (fst (record_reference_write call_id payload outcome None before)))) =
    retained_source (reference_product (write_authority before))"
  "snd (record_reference_write call_id payload outcome None before) = Some (outcome,None)"
  by (simp_all add: record_reference_write_def record_reference_product_image_def
      an_effectless_record_does_not_advance_the_ledger_read_cut Let_def)

lemma a_write_record_keeps_its_exact_result:
  "retained_outcomes (reference_product (write_authority (fst (record_reference_write call_id payload outcome changed before)))) call_id =
    Some \<lparr>result_payload = payload, result_outcome = outcome\<rparr>"
  by (simp add: record_reference_write_def record_reference_product_image_def Let_def)

lemma a_write_effect_and_observation_share_the_commit_position:
  assumes history: "reference_history_prefixes (write_history before) \<noteq> []"
    and after: "after = fst (record_reference_write call_id payload outcome (Some next) before)"
  shows "reference_image_views_agree (write_product_image after)"
    "cut_revision (write_ledger_cut after) = Suc (cut_revision (write_ledger_cut before))"
    "write_effect_positions after call_id = Some (cut_revision (write_ledger_cut before))"
    "last (reference_history_prefixes (write_history after)) =
      capture_snapshot (call_authority_state (product_calls next))"
proof -
  let ?records = "(reference_product (write_authority before))\<lparr>retained_source := capture_retained_source next,
    retained_outcomes := (retained_outcomes (reference_product (write_authority before)))
      (call_id := Some \<lparr>result_payload = payload, result_outcome = outcome\<rparr>)\<rparr>"
  let ?authority = "(write_authority before)\<lparr>reference_product := ?records\<rparr>"
  have image: "write_product_image after = record_reference_product_image ?authority 1 (write_product_image before)"
    by (simp add: after record_reference_write_def Let_def)
  show agree: "reference_image_views_agree (write_product_image after)"
    unfolding image by (rule a_ledger_advance_captures_the_view_of_its_actual_product) simp
  have revision: "cut_revision (reference_observed_cut (record_reference_advance (reference_records_epoch ?records) 1
      (capture_reference_view ?authority) (write_history before))) = cut_revision (write_ledger_cut before) + 1"
    by (rule an_accepted_batch_advances_by_its_number_of_contexts[OF history]) simp
  show "cut_revision (write_ledger_cut after) = Suc (cut_revision (write_ledger_cut before))"
    using revision by (simp add: image record_reference_product_image_def)
  show "write_effect_positions after call_id = Some (cut_revision (write_ledger_cut before))"
    by (simp add: after record_reference_write_def Let_def)
  show "last (reference_history_prefixes (write_history after)) = capture_snapshot (call_authority_state (product_calls next))"
    using agree by (simp add: reference_image_views_agree_def image record_reference_product_image_def
      capture_reference_view_def capture_retained_source_def Let_def)
qed

context source_attestation
begin

definition reference_write_dispatch where
  "reference_write_dispatch source call_id envelope =
    (let command = envelope_command envelope;
         next = product_apply_public [Begin_Call call_id command, Dispatch_Call call_id command] source
     in next\<lparr>product_durable := (product_durable next)\<lparr>product_requests :=
       (product_requests (product_durable next))(call_id := Some envelope)\<rparr>\<rparr>)"

lemma reference_write_dispatch_uses_the_existing_execution:
  assumes "call_invocations (product_calls source) call_id = None"
    "call_authority_results (product_calls source) call_id = None"
    "call_local_status (product_calls source) = Endpoint_Up"
    "call_connection (product_calls source) = Authority_Connected"
  shows "call_authority_state (product_calls (reference_write_dispatch source call_id envelope)) =
      fst (execute_finality_client (envelope_command envelope) (call_authority_state (product_calls source)))"
    "call_authority_results (product_calls (reference_write_dispatch source call_id envelope)) call_id =
      Some (envelope_command envelope,
        snd (execute_finality_client (envelope_command envelope) (call_authority_state (product_calls source))),
        length (call_authority_log (product_calls source)))"
proof -
  let ?command = "envelope_command envelope"
  let ?begun = "finality_calls.begin_client_call call_id ?command (product_calls source)"
  have vacant: "call_authority_results ?begun call_id = None"
    using assms by (simp add: finality_calls.begin_client_call_def)
  have beginning: "call_authority_state ?begun = call_authority_state (product_calls source)"
    "call_authority_log ?begun = call_authority_log (product_calls source)"
    using assms by (simp_all add: finality_calls.begin_client_call_def)
  have calls: "product_calls (reference_write_dispatch source call_id envelope) =
    finality_calls.execute_authority_once call_id ?command ?begun"
    using assms by (simp add: reference_write_dispatch_def product_apply_public_def
      finality_calls.begin_client_call_def finality_calls.dispatch_client_call_def Let_def)
  show "call_authority_state (product_calls (reference_write_dispatch source call_id envelope)) =
      fst (execute_finality_client ?command (call_authority_state (product_calls source)))"
    by (simp only: calls finality_calls.first_dispatch_records_the_actual_execution(1)[OF vacant] beginning)
  show "call_authority_results (product_calls (reference_write_dispatch source call_id envelope)) call_id =
      Some (?command,snd (execute_finality_client ?command (call_authority_state (product_calls source))),
        length (call_authority_log (product_calls source)))"
    by (simp only: calls finality_calls.first_dispatch_records_the_actual_execution(2)[OF vacant] beginning)
qed

lemma a_write_client_step_uses_the_existing_reservation_write:
  shows "snd (execute_finality_client (Client_Protocol endpoint index (Write_Intent request generation versions value)) core) =
    Protocol_Response (snd (write_asset_data (current_lock_view core endpoint) request generation (vector_lookup versions) value (core_parent core)))"
    "core_parent (fst (execute_finality_client (Client_Protocol endpoint index (Write_Intent request generation versions value)) core)) =
      fst (write_asset_data (current_lock_view core endpoint) request generation (vector_lookup versions) value (core_parent core))"
  by (simp_all add: execute_finality_client_def finality_step_def invoke_protocol_def lift_protocol_result_def Let_def)

definition reference_write_fresh where
  "reference_write_fresh registered connection actor call_id payload before =
    (let source = write_source connection before; envelope = payload_envelope payload in
      if call_connection (product_calls source) \<noteq> Authority_Connected
      then record_reference_write call_id payload Authority_Unavailable (None :: product_world option) before
      else if envelope_cut envelope \<noteq> write_ledger_cut before
      then record_reference_write call_id payload Authority_Busy (None :: product_world option) before
      else if \<not> reference_write_ready registered actor call_id payload source before
      then record_reference_write call_id payload Authority_Rejected (None :: product_world option) before
      else let next = reference_write_dispatch source call_id envelope;
               result = map_option (\<lambda>(_, reply, _). reply) (call_authority_results (product_calls next) call_id)
           in if result = Some (Protocol_Response Data_Updated)
              then record_reference_write call_id payload (Authority_Reply (Protocol_Response Data_Updated)) (Some next) before
              else record_reference_write call_id payload Authority_Rejected (None :: product_world option) before)"

definition collect_reference_write where
  "collect_reference_write verified connection actor call_id payload before =
    (case observe_collection verified actor call_id payload
       (current_product_outcomes (reopen_retained_product connection (reference_product (write_authority before)))) of
       Collected outcome \<Rightarrow> Some (outcome,write_effect_positions before call_id) | _ \<Rightarrow> None)"

definition execute_reference_write where
  "execute_reference_write directory policy authenticate verify verified registered connection route token proof target actor call_id payload before =
    (let authority = write_authority before; records = reference_product authority;
         live = reopen_retained_product connection records; outcomes = current_product_outcomes live;
         envelope = payload_envelope payload; command = envelope_command envelope;
         action = Ordinary_Product_Action (Execute_Checked Normal_Lock_Entry actor (envelope_cut envelope) call_id payload)
     in if \<not> reference_image_views_agree (write_product_image before) \<or>
           \<not> reference_grants_fit registered records (reference_inputs authority) \<or>
           map_option snd (reference_command_permission command) \<noteq> Some Ref_Write \<or>
           \<not> authorized_endpoint_action directory policy authenticate verify route token proof target action live \<or>
           \<not> result_access_bound verified actor call_id payload outcomes
        then (before,None)
        else if authority_has_call_id call_id live then
          (if retained_receipt_permission policy authenticate token proof target payload \<and> unclaimed_regulated_call live call_id
           then (before,collect_reference_write verified connection actor call_id payload before)
           else (before,None))
        else reference_write_fresh registered connection actor call_id payload before)"

definition execute_reference_write_from_core where
  "execute_reference_write_from_core attach directory policy authenticate verify verified registered connection route token proof core before =
    (case select_reference_write attach core of None \<Rightarrow> (before,None)
     | Some (call_id,payload) \<Rightarrow>
         let known = authority_has_call_id call_id (reopen_retained_product connection (reference_product (write_authority before)));
             result = execute_reference_write directory policy authenticate verify verified registered connection
               route token proof (wire_target_domain core) (fst call_id) call_id payload before
         in if known then
              if write_original_cores before call_id = Some core then result else (before,None)
            else case snd result of None \<Rightarrow> result | Some outcome \<Rightarrow>
              ((fst result)\<lparr>write_original_cores := (write_original_cores before)(call_id := Some core)\<rparr>,Some outcome))"

lemma an_existing_write_call_requires_the_same_admitted_core:
  assumes selected: "select_reference_write attach core = Some (call_id,payload)"
    and known: "authority_has_call_id call_id (reopen_retained_product connection (reference_product (write_authority before)))"
    and different: "write_original_cores before call_id \<noteq> Some core"
  shows "execute_reference_write_from_core attach directory policy authenticate verify verified registered connection route token proof core before =
    (before,None)"
  using assms by (simp add: execute_reference_write_from_core_def Let_def)

lemma a_new_selected_write_retains_the_admitted_core_with_its_result:
  assumes selected: "select_reference_write attach core = Some (call_id,payload)"
    and fresh: "\<not> authority_has_call_id call_id (reopen_retained_product connection (reference_product (write_authority before)))"
    and returned: "execute_reference_write_from_core attach directory policy authenticate verify verified registered connection route token proof core before =
      (after,Some outcome)"
  shows "write_original_cores after call_id = Some core"
  using assms by (auto simp: execute_reference_write_from_core_def Let_def split: option.splits)

lemma a_fresh_reference_write_result_passes_current_caller_authorization:
  assumes fresh: "\<not> authority_has_call_id call_id (reopen_retained_product connection (reference_product (write_authority before)))"
    and result: "snd (execute_reference_write directory policy authenticate verify verified registered connection route token proof target
      actor call_id payload before) = Some outcome"
  shows "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked Normal_Lock_Entry actor (envelope_cut (payload_envelope payload)) call_id payload))
      (reopen_retained_product connection (reference_product (write_authority before)))"
    "result_access_bound verified actor call_id payload
      (current_product_outcomes (reopen_retained_product connection (reference_product (write_authority before))))"
    "reference_image_views_agree (write_product_image before)"
    "reference_grants_fit registered (reference_product (write_authority before)) (reference_inputs (write_authority before))"
    "execute_reference_write directory policy authenticate verify verified registered connection route token proof target actor call_id payload before =
      reference_write_fresh registered connection actor call_id payload before"
  using assms by (auto simp: execute_reference_write_def Let_def split: if_splits)

lemma an_obsolete_fresh_write_records_busy_without_advancing_history:
  assumes "call_connection (product_calls (write_source connection before)) = Authority_Connected"
    "envelope_cut (payload_envelope payload) \<noteq> write_ledger_cut before"
  shows "reference_write_fresh registered connection actor call_id payload before =
    record_reference_write call_id payload Authority_Busy (None :: product_world option) before"
  using assms by (simp add: reference_write_fresh_def Let_def)

lemma a_fresh_write_commits_when_the_current_guards_pass:
  assumes connected: "call_connection (product_calls (write_source connection before)) = Authority_Connected"
    and current: "envelope_cut (payload_envelope payload) = write_ledger_cut before"
    and ready: "reference_write_ready registered actor call_id payload (write_source connection before) before"
    and command: "envelope_command (payload_envelope payload) = Client_Protocol endpoint index (Write_Intent request generation versions value)"
    and kernel: "let core = call_authority_state (product_calls (write_source connection before));
      ctxt = current_lock_view core endpoint; state = machine_state (core_parent core) in
      owns_current_reservation ctxt request generation (vector_lookup versions) state \<and>
      phase_at state (binding_key (request_binding request)) = Some Reservation_Held \<and>
      (request_caller request,binding_asset (request_binding request),value) \<in> lock_write_permissions ctxt"
  shows "reference_write_fresh registered connection actor call_id payload before =
    record_reference_write call_id payload (Authority_Reply (Protocol_Response Data_Updated))
      (Some (reference_write_dispatch (write_source connection before) call_id (payload_envelope payload))) before"
proof -
  let ?source = "write_source connection before"
  let ?envelope = "payload_envelope payload"
  let ?core = "call_authority_state (product_calls ?source)"
  have fresh: "call_invocations (product_calls ?source) call_id = None"
    "call_authority_results (product_calls ?source) call_id = None"
    "call_local_status (product_calls ?source) = Endpoint_Up"
    using ready by (simp_all add: reference_write_ready_def Let_def)
  note dispatch = reference_write_dispatch_uses_the_existing_execution(2)[OF fresh connected, where envelope="?envelope"]
  have reply: "snd (write_asset_data (current_lock_view ?core endpoint) request generation (vector_lookup versions) value
        (core_parent ?core)) = Data_Updated"
    by (rule successful_write_guard[THEN iffD2, OF kernel[unfolded Let_def]])
  show ?thesis using connected current ready
    by (simp add: reference_write_fresh_def Let_def dispatch command a_write_client_step_uses_the_existing_reservation_write(1) reply)
qed

lemma a_fresh_write_without_a_commit_keeps_value_version_and_history:
  assumes "reference_write_fresh registered connection actor call_id payload before = (after,Some (outcome,None))"
  shows "write_history after = write_history before"
    "retained_source (reference_product (write_authority after)) = retained_source (reference_product (write_authority before))"
proof -
  let ?refused = "record_reference_write call_id payload outcome (None :: product_world option) before"
  have refusal: "reference_write_fresh registered connection actor call_id payload before = ?refused"
    using assms by (auto simp: reference_write_fresh_def record_reference_write_def Let_def split: if_splits)
  have recorded: "(after,Some (outcome,None)) = ?refused"
    by (rule trans[OF assms[symmetric] refusal])
  have after: "after = fst ?refused"
    using arg_cong[OF recorded, where f=fst] by (simp only: fst_conv)
  show "write_history after = write_history before"
    unfolding after by (rule recording_a_write_without_effect_keeps_the_exact_authority_view(1))
  show "retained_source (reference_product (write_authority after)) = retained_source (reference_product (write_authority before))"
    unfolding after by (rule recording_a_write_without_effect_keeps_the_exact_authority_view(2))
qed

theorem a_fresh_write_commit_binds_the_current_guard_value_and_position:
  assumes committed: "reference_write_fresh registered connection actor call_id payload before =
      (after,Some (Authority_Reply (Protocol_Response Data_Updated),Some position))"
    and command: "envelope_command (payload_envelope payload) = Client_Protocol endpoint index
      (Write_Intent request generation versions value)"
    and history: "reference_history_prefixes (write_history before) \<noteq> []"
  shows "envelope_cut (payload_envelope payload) = write_ledger_cut before"
    "reference_write_ready registered actor call_id payload (write_source connection before) before"
    "let core = call_authority_state (product_calls (write_source connection before));
         ctxt = current_lock_view core endpoint; state = machine_state (core_parent core)
      in owns_current_reservation ctxt request generation (vector_lookup versions) state \<and>
        phase_at state (binding_key (request_binding request)) = Some Reservation_Held \<and>
        (request_caller request,binding_asset (request_binding request),value) \<in> lock_write_permissions ctxt"
    "let asset = binding_asset (request_binding request);
         snapshot = last (reference_history_prefixes (write_history after))
      in stored_query (Application_Value asset) snapshot = Units_Value value \<and>
        asset_version (snapshot_financial snapshot) asset =
          Suc (asset_version (authoritative_reservation_state (write_source connection before)) asset)"
    "position = cut_revision (write_ledger_cut before)"
    "cut_revision (write_ledger_cut after) = Suc position"
    "write_effect_positions after call_id = Some position"
    "retained_outcomes (reference_product (write_authority after)) call_id =
      Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Data_Updated)\<rparr>"
proof -
  let ?source = "write_source connection before"
  let ?envelope = "payload_envelope payload"
  let ?next = "reference_write_dispatch ?source call_id ?envelope"
  let ?core = "call_authority_state (product_calls ?source)"
  let ?operation = "write_asset_data (current_lock_view ?core endpoint) request generation
    (vector_lookup versions) value (core_parent ?core)"
  let ?outcome = "Authority_Reply (Protocol_Response Data_Updated)"
  let ?recorded = "record_reference_write call_id payload ?outcome (Some ?next) before"
  have verdict: "snd (reference_write_fresh registered connection actor call_id payload before) =
    Some (?outcome,Some position)"
    using arg_cong[OF committed, where f=snd] by (simp only: snd_conv)
  have connected: "call_connection (product_calls ?source) = Authority_Connected"
    and current: "envelope_cut ?envelope = write_ledger_cut before"
    and ready: "reference_write_ready registered actor call_id payload ?source before"
    and applied: "map_option (\<lambda>(_, reply, _). reply) (call_authority_results (product_calls ?next) call_id) =
      Some (Protocol_Response Data_Updated)"
    using verdict by (auto simp: reference_write_fresh_def record_reference_write_def Let_def split: if_splits)
  have exact_record: "?recorded = (after,Some (?outcome,Some position))"
    using committed connected current ready applied by (simp add: reference_write_fresh_def Let_def)
  have after: "after = fst ?recorded"
    using arg_cong[OF exact_record[symmetric], where f=fst] by (simp only: fst_conv)
  have position: "position = cut_revision (write_ledger_cut before)"
    using arg_cong[OF exact_record, where f=snd] by (simp add: record_reference_write_def Let_def)
  have fresh: "call_invocations (product_calls ?source) call_id = None"
    "call_authority_results (product_calls ?source) call_id = None"
    "call_local_status (product_calls ?source) = Endpoint_Up"
    using ready by (simp_all add: reference_write_ready_def Let_def)
  note dispatch = reference_write_dispatch_uses_the_existing_execution[OF fresh connected]
  have kernel: "snd ?operation = Data_Updated"
    using applied by (simp add: dispatch(2) command a_write_client_step_uses_the_existing_reservation_write(1))
  have core: "core_parent (call_authority_state (product_calls ?next)) = fst ?operation"
    by (simp only: dispatch(1) command a_write_client_step_uses_the_existing_reservation_write(2))
  note effect = a_write_effect_and_observation_share_the_commit_position[OF history after]
  show "envelope_cut ?envelope = write_ledger_cut before" by (rule current)
  show "reference_write_ready registered actor call_id payload ?source before" by (rule ready)
  show "let core = call_authority_state (product_calls ?source);
         ctxt = current_lock_view core endpoint; state = machine_state (core_parent core)
      in owns_current_reservation ctxt request generation (vector_lookup versions) state \<and>
        phase_at state (binding_key (request_binding request)) = Some Reservation_Held \<and>
        (request_caller request,binding_asset (request_binding request),value) \<in> lock_write_permissions ctxt"
    unfolding Let_def by (rule successful_write_guard[THEN iffD1, OF kernel])
  show "let asset = binding_asset (request_binding request);
         snapshot = last (reference_history_prefixes (write_history after))
      in stored_query (Application_Value asset) snapshot = Units_Value value \<and>
        asset_version (snapshot_financial snapshot) asset =
          Suc (asset_version (authoritative_reservation_state ?source) asset)"
    using successful_write_value_and_version[OF kernel]
    by (simp add: effect(4) core capture_snapshot_def authoritative_reservation_state_def Let_def)
  show "position = cut_revision (write_ledger_cut before)" by (rule position)
  show "cut_revision (write_ledger_cut after) = Suc position" using effect(2) position by simp
  show "write_effect_positions after call_id = Some position" using effect(3) position by simp
  show "retained_outcomes (reference_product (write_authority after)) call_id =
      Some \<lparr>result_payload = payload, result_outcome = ?outcome\<rparr>"
    unfolding after by (rule a_write_record_keeps_its_exact_result)
qed

lemma a_current_write_reservation_carries_the_exact_generation_deadline_and_footprint:
  assumes "owns_current_reservation ctxt request generation (vector_lookup versions) state"
  obtains reservation where
    "reservation_at state (binding_key (request_binding request)) = Some reservation"
    "reservation_binding reservation = request_binding request"
    "reservation_worker reservation = request_caller request"
    "reservation_generation reservation = generation"
    "reservation_clock state < reservation_deadline reservation"
    "set (reservation_footprint reservation) = set (required_footprint ctxt (request_binding request))"
    "\<forall>asset\<in>set (reservation_footprint reservation).
      asset_owner state asset = Some (binding_key (request_binding request)) \<and>
      vector_lookup versions asset = asset_version state asset"
  using assms unfolding owns_current_reservation_def owns_recorded_reservation_def by blast

end

lemma reopening_the_write_authority_restores_the_exact_result_table:
  "outcome_entries (current_product_outcomes (reopen_retained_product connection records)) = retained_outcomes records"
  by (simp add: reopen_retained_product_def initial_product_reads_def current_product_outcomes_def
      legal_underlying_outcomes_def Let_def)

lemma reopened_write_outcomes_are_available_to_the_endpoint:
  "call_local_status (product_calls (outcome_source (current_product_outcomes (reopen_retained_product connection records)))) = Endpoint_Up"
  by (simp add: reopen_retained_product_def reopen_retained_source_def initial_product_reads_def
      current_product_outcomes_def legal_underlying_outcomes_def Let_def)

context source_attestation
begin

lemma a_known_write_call_never_executes_a_second_effect:
  assumes "authority_has_call_id call_id (reopen_retained_product connection (reference_product (write_authority before)))"
  shows "fst (execute_reference_write directory policy authenticate verify verified registered connection route token proof target actor call_id payload before) = before"
  using assms by (simp add: execute_reference_write_def Let_def split: if_splits)

theorem a_reopened_exact_write_returns_its_retained_result_and_position:
  fixes before connection
  assumes coherent: "reference_image_views_agree (write_product_image before)"
    and grants: "reference_grants_fit registered (reference_product (write_authority before)) (reference_inputs (write_authority before))"
    and command: "envelope_command (payload_envelope payload) = Client_Protocol endpoint index (Write_Intent request generation versions value)"
    and admitted: "authorized_endpoint_action directory policy authenticate verify route token proof target
      (Ordinary_Product_Action (Execute_Checked Normal_Lock_Entry actor (envelope_cut (payload_envelope payload)) call_id payload))
      (reopen_retained_product connection (reference_product (write_authority before)))"
    and bound: "result_access_bound verified actor call_id payload
      (current_product_outcomes (reopen_retained_product connection (reference_product (write_authority before))))"
    and receipt: "retained_receipt_permission policy authenticate token proof target payload"
    and ordinary: "unclaimed_regulated_call (reopen_retained_product connection (reference_product (write_authority before))) call_id"
    and recorded: "retained_outcomes (reference_product (write_authority before)) call_id =
      Some \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Data_Updated)\<rparr>"
  shows "execute_reference_write directory policy authenticate verify verified registered connection route token proof target actor call_id payload before =
    (before,Some (Authority_Reply (Protocol_Response Data_Updated),write_effect_positions before call_id))"
proof -
  let ?live = "reopen_retained_product connection (reference_product (write_authority before))"
  let ?outcomes = "current_product_outcomes ?live"
  let ?outcome = "Authority_Reply (Protocol_Response Data_Updated)"
  have known: "authority_has_call_id call_id ?live"
    using recorded by (simp add: authority_has_call_id_def reopening_the_write_authority_restores_the_exact_result_table)
  have observed: "observe_collection verified actor call_id payload ?outcomes = Collected ?outcome"
    using recorded bound command by (simp add: observe_collection_def result_completion_ready_def Let_def
      reopening_the_write_authority_restores_the_exact_result_table reopened_write_outcomes_are_available_to_the_endpoint)
  show ?thesis using coherent grants command admitted bound receipt ordinary known observed
    by (simp add: execute_reference_write_def collect_reference_write_def Let_def)
qed

lemma an_existing_write_id_with_changed_payload_cannot_collect_or_execute:
  assumes recorded: "retained_outcomes (reference_product (write_authority before)) call_id = Some entry"
    and changed: "result_payload entry \<noteq> payload"
  shows "execute_reference_write directory policy authenticate verify verified registered connection route token proof target actor call_id payload before =
    (before,None)"
proof -
  let ?live = "reopen_retained_product connection (reference_product (write_authority before))"
  have entry: "outcome_entries (current_product_outcomes ?live) call_id = Some entry"
    using recorded by (simp add: reopening_the_write_authority_restores_the_exact_result_table)
  have known: "authority_has_call_id call_id ?live" using entry by (simp add: authority_has_call_id_def)
  have refused: "observe_collection verified actor call_id payload (current_product_outcomes ?live) = Collection_Rejected"
    by (rule conflicting_payload_is_observably_rejected[OF entry changed reopened_write_outcomes_are_available_to_the_endpoint])
  show ?thesis using known refused by (simp add: execute_reference_write_def collect_reference_write_def Let_def split: if_splits)
qed

end

end

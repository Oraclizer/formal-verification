theory Regulated_Acceptance
  imports Regulated_Program "OIP_Product_Base.Outcome_Gates"
begin

context source_attestation
begin

lemma new_dispatch_uses_the_actual_client_execution:
  fixes who call_id envelope source command before result after
  defines "command \<equiv> envelope_command envelope"
    and "before \<equiv> product_calls source"
    and "result \<equiv> execute_finality_client command (call_authority_state before)"
  assumes fresh: "product_new_call who call_id envelope source"
  defines "after \<equiv> product_calls (product_submit (\<lambda>_ _ _. True) who call_id envelope source)"
  shows "call_authority_state after = fst result"
    "call_authority_results after call_id = Some (command, snd result, length (call_authority_log before))"
proof -
  have ready: "call_invocations before call_id = None" "call_authority_results before call_id = None"
    "call_local_status before = Endpoint_Up" "call_connection before = Authority_Connected"
    using fresh by (simp_all add: product_new_call_def before_def)
  have word: "after = finality_calls.run_calls [Begin_Call call_id command, Dispatch_Call call_id command] before"
    unfolding after_def command_def before_def
    using product_new_call_uses_authoritative_dispatch[OF _ fresh, of "\<lambda>_ _ _. True"] by simp
  show "call_authority_state after = fst result"
    "call_authority_results after call_id = Some (command, snd result, length (call_authority_log before))"
    unfolding word result_def using ready
    by (simp_all add: finality_calls.begin_client_call_def finality_calls.dispatch_client_call_def
        finality_calls.execute_authority_once_def Let_def)
qed

lemma checked_fresh_execution_uses_the_authority_outcome:
  fixes reads payload who call_id entry permitted verified maintainers registered verified_ack
    authority origins outcomes source envelope command result result_reads result_outcomes
  defines "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
    and "command \<equiv> envelope_command envelope"
    and "result \<equiv> execute_finality_client command (authoritative_read_core authority)"
  assumes fresh: "product_new_call who call_id envelope source"
    and authentic: "verified who call_id payload"
    and unrecorded: "outcome_entries outcomes call_id = None"
    and scope: "permitted entry who command" "registered_lock_envelope registered envelope"
      "lock_envelope_admitted who envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
  defines "result_reads \<equiv> execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry who (observed_product_cut authority) call_id payload reads"
    and "result_outcomes \<equiv> origin_outcomes (settlement_primary (read_authority (fst result_reads)))"
  shows "snd result_reads = Forwarded_At_Checked_Cut \<and>
    outcome_entries result_outcomes call_id = Some \<lparr>result_payload = payload, result_outcome = normalized_authority_reply (snd result)\<rparr> \<and>
    call_authority_state (outcome_calls result_outcomes) = fst result"
proof -
  let ?permitted = "\<lambda>route actor cmd. permitted route actor cmd \<and>
    origin_command_allowed origins envelope (payload_origin_epoch payload) cmd"
  let ?forward = "lock_product_step ?permitted (\<lambda>_ _ _ _. True) maintainers registered
    (Lock_Submit entry who call_id envelope (payload_credential payload)) source"
  have forward: "?forward = product_submit (\<lambda>_ _ _. True) who call_id envelope source"
    using scope by (simp add: command_def submit_lock_entry_def lock_submission_allowed_def)
  have core: "authoritative_read_core authority = call_authority_state (product_calls source)"
    by (simp add: authoritative_read_core_def exact_calls_def outcome_calls_def source_def outcomes_def origins_def)
  have result_core: "call_authority_state (product_calls ?forward) = fst result"
    and result_call: "call_authority_results (product_calls ?forward) call_id =
      Some (command, snd result, length (call_authority_log (product_calls source)))"
    unfolding forward result_def core command_def
    by (rule new_dispatch_uses_the_actual_client_execution[OF fresh])+
  have access: "result_access_bound verified who call_id payload outcomes"
    using fresh authentic by (simp add: result_access_bound_def product_new_call_def envelope_def source_def)
  have ready: "call_invocations (product_calls source) call_id = None"
    "call_authority_results (product_calls source) call_id = None"
    "call_local_status (product_calls source) = Endpoint_Up"
    "call_connection (product_calls source) = Authority_Connected"
    using fresh by (simp_all add: product_new_call_def)
  have revision: "envelope_cut envelope = observed_product_cut authority"
    using fresh by (simp add: product_new_call_def observed_product_cut_def observed_product_source_def
        source_def outcomes_def origins_def)
  have live: "read_authority_available reads"
    using ready(3,4) by (simp add: read_authority_available_def exact_calls_def outcome_calls_def
        source_def outcomes_def origins_def authority_def)
  have routed: "result_reads = (reads\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
    (Exact_Submit entry who call_id payload) authority\<rparr>, Forwarded_At_Checked_Cut)"
    using access revision live
    by (simp add: result_reads_def execute_at_checked_cut_def Let_def envelope_def outcomes_def origins_def authority_def)
  have stored: "submit_authoritative_call ?permitted verified maintainers registered entry who call_id payload outcomes =
    store_product_result call_id payload (normalized_authority_reply (snd result)) ?forward outcomes"
    using first_connected_call_records_its_public_result[OF access unrecorded] ready result_call
    by (simp del: lock_product_step.simps add: Let_def source_def envelope_def)
  have projected: "result_outcomes = store_product_result call_id payload (normalized_authority_reply (snd result)) ?forward outcomes"
    unfolding result_outcomes_def routed
    using unrecorded stored
    by (simp del: lock_product_step.simps add: submit_origin_call_def origin_metadata_retention_keeps_the_authority_result
        Let_def split: option.splits prod.splits add: command_def envelope_def outcomes_def origins_def)
  show ?thesis
    unfolding projected routed using result_core by (simp add: store_product_result_def outcome_calls_def)
qed

theorem admitted_enforcement_executes_and_records_the_exact_funded_spend:
  fixes s payload who call_id entry permitted verified maintainers registered verified_ack
    legal reads authority origins outcomes source envelope command
  defines "legal \<equiv> governed_legal (regulated_orders s)"
    and "reads \<equiv> legal_reads legal"
    and "authority \<equiv> read_authority reads"
    and "origins \<equiv> settlement_primary authority"
    and "outcomes \<equiv> origin_outcomes origins"
    and "source \<equiv> outcome_source outcomes"
    and "envelope \<equiv> payload_envelope payload"
    and "command \<equiv> envelope_command envelope"
  assumes spend: "command = Client_Protocol endpoint index (Descendant_Intent r root sender recipient amount)"
    and lawful: "lawful_enforcement_preconditions (authoritative_read_core authority)
      endpoint index r root sender recipient amount kind"
    and admitted: "governed_spend_is_admitted grant spend_verified who payload authorization legal"
    and fresh: "product_new_call who call_id envelope source"
    and authentic: "verified who call_id payload"
    and unrecorded: "outcome_entries outcomes call_id = None"
      "legal_receipts (regulated_orders s) call_id = None" "spend_receipts s call_id = None"
    and scope: "permitted (regulatory_lock_entry entry) who command" "registered_lock_envelope registered envelope"
      "lock_envelope_admitted who envelope (payload_credential payload) source"
      "origin_command_allowed origins envelope (payload_origin_epoch payload) command"
  shows "let after = fst (submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
                entry who (observed_product_cut authority) call_id payload authorization s);
             recorded = legal_underlying_outcomes (governed_legal (regulated_orders after));
             new = authoritative_reservation_state (outcome_source recorded);
             old = authoritative_reservation_state source
         in outcome_entries recorded call_id = Some
              \<lparr>result_payload = payload, result_outcome = Authority_Reply (Protocol_Response Descendant_Executed)\<rparr> \<and>
            (\<exists>event. lawful_descendants new = lawful_descendants old @ [event] \<and>
               lineage_root event = root \<and> lineage_from event = sender \<and> lineage_to event = recipient \<and>
               lineage_amount event = amount \<and> lineage_caller event = request_caller r)"
proof -
  let ?entry = "regulatory_lock_entry entry"
  let ?checked = "execute_at_checked_cut permitted verified maintainers registered verified_ack
    ?entry who (observed_product_cut authority) call_id payload reads"
  let ?next = "origin_outcomes (settlement_primary (read_authority (fst ?checked)))"
  let ?core = "authoritative_read_core authority"
  let ?result = "execute_finality_client command ?core"
  note unfold_path = source_def outcomes_def origins_def authority_def envelope_def command_def
  have submitted: "snd ?checked = Forwarded_At_Checked_Cut \<and>
    outcome_entries ?next call_id = Some \<lparr>result_payload = payload, result_outcome = normalized_authority_reply (snd ?result)\<rparr> \<and>
    call_authority_state (outcome_calls ?next) = fst ?result"
    unfolding unfold_path
    by (rule checked_fresh_execution_uses_the_authority_outcome)
      (use fresh authentic unrecorded(1) scope in \<open>simp_all only: unfold_path\<close>)
  let ?invoke = "invoke_protocol endpoint (core_epoch ?core) index (Descendant_Intent r root sender recipient amount) ?core"
  have actual: "snd ?result = snd ?invoke" "core_parent (fst ?result) = core_parent (fst ?invoke)"
    by (simp_all add: spend execute_finality_client_def finality_step_def)
  have lineage: "snd ?result = Protocol_Response Descendant_Executed \<and>
      (\<exists>event. lawful_descendants (machine_state (core_parent (fst ?result))) =
          lawful_descendants (machine_state (core_parent ?core)) @ [event] \<and>
          lineage_root event = root \<and> lineage_from event = sender \<and> lineage_to event = recipient \<and>
          lineage_amount event = amount \<and> lineage_caller event = request_caller r)"
    unfolding actual using lawful_enforcement_consumes_the_exact_confirmed_root[OF lawful]
    by (simp only: Let_def)
  have core: "call_authority_state (product_calls source) = ?core"
    by (simp add: authoritative_read_core_def exact_calls_def outcome_calls_def unfold_path)
  have live: "read_authority_available reads"
    using fresh by (simp add: product_new_call_def read_authority_available_def exact_calls_def outcome_calls_def unfold_path)
  have access: "result_access_bound verified who call_id payload outcomes"
    using fresh authentic by (simp add: result_access_bound_def product_new_call_def unfold_path)
  have nested: "legal_underlying_outcomes legal = outcomes"
    by (simp add: legal_underlying_outcomes_def unfold_path reads_def)
  let ?after = "fst (submit_governed_spend grant spend_verified permitted verified maintainers registered verified_ack
    entry who (observed_product_cut authority) call_id payload authorization s)"
  have "legal_underlying_outcomes (governed_legal (regulated_orders ?after)) = ?next"
    using access live admitted unrecorded nested
    by (simp add: submit_governed_spend_def run_spend_effect_def Let_def
        replace_regulated_reads_def legal_underlying_outcomes_def read_authority_available_def
        legal_def reads_def)
  with submitted lineage core show ?thesis
    by (simp add: Let_def outcome_calls_def authoritative_reservation_state_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms source_attestation.admitted_enforcement_executes_and_records_the_exact_funded_spend})
  then () else error "Unexpected oracle in regulated acceptance"
\<close>

end

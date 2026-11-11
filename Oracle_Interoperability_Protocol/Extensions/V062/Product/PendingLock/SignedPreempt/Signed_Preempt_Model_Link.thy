theory Signed_Preempt_Model_Link
  imports "OIP_Lock_Clock_Model_Link.Lock_Clock_Model_Link"
    "OIP_Message_Code.Wire_Code_Operands_Native"
    "OIP_Message_Code.Wire_Code_Response_Outcome"
begin

definition spp_payload_words where
  "spp_payload_words spv_native spv_request =
    [native_reference spv_native,fst (native_id spv_native),snd (native_id spv_native),
     plr_endpoint spv_request,plr_session spv_request,plr_cut_epoch spv_request,
     plr_cut_revision spv_request,native_origin_epoch spv_native,5] @
    pl_binding_words (plr_binding spv_request) @ pl_command_words (plr_command spv_request) @
    concat (map (\<lambda>(spv_asset,spv_version). [spv_asset,spv_version]) (plr_versions spv_request))"

definition spp_decode_request where
  "spp_decode_request spv_core spv_actor spv_verified spv_owner_proof =
    (case code_decode_ordinary spv_core of
      Code_Ordinary_Ready spv_native None spv_versions (Wire_Preempt spv_duration) \<Rightarrow>
        (if native_proof_bytes spv_native \<noteq> [spv_owner_proof] then None else
         let spv_cut = native_cut spv_native;
             spv_request = \<lparr>plr_binding = \<lparr>pl_origin = native_origin spv_native, pl_asset = native_asset spv_native,
                 pl_owner = native_funding_owner spv_native, pl_destination = native_destination spv_native,
                 pl_recipient = native_recipient spv_native, pl_amount = native_amount spv_native\<rparr>,
               plr_actor = spv_actor, plr_caller = fst (native_id spv_native), plr_session = native_session spv_native,
               plr_endpoint = wire_target_domain spv_core, plr_cut_epoch = cut_authority_epoch spv_cut,
               plr_cut_revision = cut_revision spv_cut, plr_route = 0, plr_verified = spv_verified,
               plr_credential = None, plr_versions = spv_versions, plr_command = PL_Preempt spv_duration\<rparr>
         in Some (spp_payload_words spv_native spv_request,spv_request))
    | _ \<Rightarrow> None)"

lemma spp_exact_ready_outcome_uses_the_authority_lookup:
  assumes "result_access_bound spv_verified spv_actor spv_call spv_payload spv_world"
    "outcome_entries spv_world spv_call = Some spv_saved" "result_payload spv_saved = spv_payload"
    "result_completion_ready spv_saved spv_world"
  shows "read_authoritative_result spv_verified spv_actor spv_call spv_payload spv_world = Some (result_outcome spv_saved)"
  by (rule exact_retry_reads_the_committed_outcome[OF assms])

definition spp_existing_annotation :: "nat list \<Rightarrow> (nat \<times> nat option) option" where
  "spp_existing_annotation spv_words =
    (case spv_words of [spv_tag,spv_position,spv_completed] \<Rightarrow>
      (if spv_tag = 1 \<and> spv_completed = 1 then Some
        (code_source_ordinary_result \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Preempted_Reply,
          source_outcome_commit = Some spv_position\<rparr>) else None)
     | _ \<Rightarrow> None)"

lemma spp_existing_preempt_commit_is_preserved:
  "spp_existing_annotation [1,spv_position,1] = Some (14,Some spv_position)"
  by (simp add: spp_existing_annotation_def code_source_ordinary_result_def)

type_synonym spp_integer_result = "integer list list \<times> pl_integer_result"

definition spp_case_result where
  "spp_case_result spv_mode spv_common spv_receipt spv_core spv_shape spv_request spv_state
      spv_stored spv_bound_core spv_annotation =
    (if spv_mode = 0 \<and> spv_stored = [] \<and> spv_bound_core = [] \<and> spv_annotation = [] then
       Some ([],pl_clock_result spv_state spv_request (pl_step True spv_request spv_state))
     else if spv_mode = 1 \<and> spv_common \<and> spv_receipt \<and> pls_connected spv_state \<and>
         plr_actor spv_request = plr_caller spv_request \<and> plr_cut_epoch spv_request = pls_epoch spv_state \<and>
         map_of (pls_sessions spv_state) (plr_session spv_request) = Some (plr_actor spv_request,pls_epoch spv_state) \<and>
         spv_core = spv_bound_core \<and> spv_shape = spv_stored
     then case spp_existing_annotation spv_annotation of
         Some (spv_code,Some spv_position) \<Rightarrow> Some (map integer_of_nat [spv_code,spv_position],
           pl_clock_result spv_state spv_request (spv_state,PL_Preempted))
       | _ \<Rightarrow> None
     else None)"

fun spp_natural_abi :: "nat list list \<Rightarrow> nat list list list \<Rightarrow> spp_integer_result option" where
  "spp_natural_abi [[spv_mode,spv_actor],spv_packet,spv_core_bytes,spv_preimage,spv_signature,spv_owner_proof,
        spv_context,spv_expected,[spv_outer_ok,spv_token_ok,spv_owner_ok,spv_execute_ok,spv_recover_ok,spv_receipt_ok,spv_scope_ok],
        spv_stored,spv_bound_core,spv_annotation] spv_state_rows =
    (if \<not> list_all (\<lambda>spv_flag. spv_flag \<le> 1)
          [spv_outer_ok,spv_token_ok,spv_owner_ok,spv_execute_ok,spv_recover_ok,spv_receipt_ok,spv_scope_ok] \<or>
        length spv_owner_proof \<noteq> 64 \<or>
        \<not> list_all (\<lambda>spv_byte. spv_byte < 256)
          (spv_packet @ spv_core_bytes @ spv_preimage @ spv_signature @ spv_owner_proof @ spv_bound_core)
     then None else
      case (decode_wire_packet spv_packet,pl_clock_parse_state spv_state_rows) of
        (Some spv_decoded,Some spv_state) \<Rightarrow>
          let spv_core = packet_core spv_decoded;
              spv_common = (spv_outer_ok = 1 \<and> spv_token_ok = 1 \<and> spv_execute_ok = 1 \<and> spv_scope_ok = 1);
              spv_verified = (spv_common \<and> spv_owner_ok = 1 \<and> spv_recover_ok = 1)
          in if wire_version spv_core \<noteq> 6 \<or> wire_signature_scheme spv_core \<noteq> 1 \<or>
                wire_message_family spv_core \<noteq> Wire_Lock \<or> wire_opcode (wire_operation_body spv_core) \<noteq> 5 \<or>
                [wire_deployment spv_core,wire_source_domain spv_core,wire_target_domain spv_core,
                 wire_principal spv_core,wire_authority_epoch spv_core] @ wire_uuid spv_core \<noteq> spv_context \<or>
                encode_wire_core spv_core \<noteq> spv_core_bytes \<or> envelope_signing_bytes spv_core \<noteq> spv_preimage \<or>
                packet_signature spv_decoded \<noteq> spv_signature
             then None else
               (case spp_decode_request spv_core spv_actor spv_verified spv_owner_proof of
                 None \<Rightarrow> None | Some (spv_shape,spv_request) \<Rightarrow>
                   if spv_shape \<noteq> spv_expected then None else
                     map_option (\<lambda>(spv_retained,spv_view). ([map integer_of_nat [spv_mode,3,5],
                       map integer_of_nat spv_shape,map integer_of_nat spv_core_bytes,spv_retained],spv_view))
                       (spp_case_result spv_mode spv_common (spv_receipt_ok = 1) spv_core_bytes spv_shape spv_request spv_state
                         spv_stored spv_bound_core spv_annotation))
      | _ \<Rightarrow> None)"
| "spp_natural_abi _ _ = None"

definition spp_integer_abi :: "integer list list \<Rightarrow> integer list list list \<Rightarrow> spp_integer_result option" where
  "spp_integer_abi spv_wire spv_state =
    (if list_all (list_all pl_clock_u64) spv_wire \<and> pl_clock_matrix_u64 spv_state
     then spp_natural_abi (map (map nat_of_integer) spv_wire) (map (map (map nat_of_integer)) spv_state)
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms pl_preempt_preserves_source_obligation_and_evidence
      spp_exact_ready_outcome_uses_the_authority_lookup spp_existing_preempt_commit_is_preserved})
  then () else error "Unexpected oracle in signed Preempt link"
\<close>

export_code spp_integer_abi in SML
  module_name OIP_Signed_Preempt_Link file_prefix "oip_signed_preempt_link"

end

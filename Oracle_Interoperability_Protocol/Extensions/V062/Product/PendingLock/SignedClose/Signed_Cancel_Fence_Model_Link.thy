theory Signed_Cancel_Fence_Model_Link
  imports "OIP_Lock_Clock_Model_Link.Lock_Clock_Model_Link"
    "OIP_Message_Code.Wire_Code_Operands_Native"
    "OIP_Message_Code.Wire_Code_Response_Outcome"
begin

text \<open>
  The exact packet and ordinary operand use the checked codec. The two fresh
  rows run the existing Pending Lock transition. The two retained rows use an
  exact saved payload and an independently supplied existing commit annotation.
  No journal or transport write is modeled by either projection.
\<close>

fun scf_close_command :: "nat \<Rightarrow> ordinary_wire_command \<Rightarrow> pl_command option" where
  "scf_close_command scf_opcode (Wire_Cancel scf_generation) =
    (if scf_opcode = 3 then Some (PL_Cancel scf_generation) else None)"
| "scf_close_command scf_opcode (Wire_Fence scf_generation) =
    (if scf_opcode = 4 then Some (PL_Fence scf_generation) else None)"
| "scf_close_command _ _ = None"

definition scf_credential :: "product_lock_credential \<Rightarrow> pl_credential" where
  "scf_credential scf_token =
    (let scf_lock = credential_token scf_token in
     \<lparr>plc_asset = token_asset scf_lock, plc_origin = credential_origin scf_token,
      plc_holder = token_owner scf_lock, plc_generation = token_generation scf_lock,
      plc_epoch = credential_epoch scf_token\<rparr>)"

definition scf_payload_projection where
  "scf_payload_projection scf_native scf_opcode scf_request =
    [native_reference scf_native,fst (native_id scf_native),snd (native_id scf_native),
     plr_endpoint scf_request,plr_session scf_request,plr_cut_epoch scf_request,
     plr_cut_revision scf_request,native_origin_epoch scf_native,scf_opcode] @
    pl_binding_words (plr_binding scf_request) @ pl_command_words (plr_command scf_request) @
    (case plr_credential scf_request of None \<Rightarrow> [] | Some scf_token \<Rightarrow>
      [plc_asset scf_token,fst (plc_origin scf_token),snd (plc_origin scf_token),
       plc_holder scf_token,plc_generation scf_token,plc_epoch scf_token]) @
    concat (map (\<lambda>(scf_asset,scf_version). [scf_asset,scf_version]) (plr_versions scf_request))"

definition scf_decode_request where
  "scf_decode_request scf_core scf_actor scf_verified scf_owner_proof =
    (let scf_opcode = wire_opcode (wire_operation_body scf_core) in
      if wire_version scf_core \<noteq> 6 \<or> wire_signature_scheme scf_core \<noteq> 1 \<or>
         wire_message_family scf_core \<noteq> Wire_Lock then None else
      case code_decode_ordinary scf_core of
        Code_Ordinary_Ready scf_native (Some scf_token) scf_versions scf_wire_command \<Rightarrow>
          (case scf_close_command scf_opcode scf_wire_command of None \<Rightarrow> None | Some scf_command \<Rightarrow>
            if native_proof_bytes scf_native \<noteq> [scf_owner_proof] then None else
            let scf_cut = native_cut scf_native;
                scf_request = \<lparr>plr_binding = \<lparr>pl_origin = native_origin scf_native, pl_asset = native_asset scf_native,
                     pl_owner = native_funding_owner scf_native, pl_destination = native_destination scf_native,
                     pl_recipient = native_recipient scf_native, pl_amount = native_amount scf_native\<rparr>,
                  plr_actor = scf_actor, plr_caller = fst (native_id scf_native), plr_session = native_session scf_native,
                  plr_endpoint = wire_target_domain scf_core, plr_cut_epoch = cut_authority_epoch scf_cut,
                  plr_cut_revision = cut_revision scf_cut, plr_route = 0, plr_verified = scf_verified,
                  plr_credential = Some (scf_credential scf_token), plr_versions = scf_versions, plr_command = scf_command\<rparr>
            in Some (scf_payload_projection scf_native scf_opcode scf_request,scf_request))
      | _ \<Rightarrow> None)"

lemma scf_live_close_is_the_parent_footprint_release:
  assumes "(\<exists>scf_generation. plr_command scf_request = PL_Cancel scf_generation \<and> pls_phase scf_state = PL_Held) \<or>
           (\<exists>scf_generation. plr_command scf_request = PL_Fence scf_generation \<and> pls_phase scf_state = PL_Dispatched)"
    "pls_exists scf_state" "plr_binding scf_request = pls_binding scf_state"
    "pl_request_admitted scf_request scf_state" "plr_verified scf_request"
    "pl_effect_credential scf_request scf_state" "Suc (pls_revision scf_state) < 2^64"
    "pls_clock scf_state < pls_expires scf_state"
  shows "pl_step True scf_request scf_state =
    ((pl_release PL_Closed scf_state)\<lparr>pls_revision := Suc (pls_revision scf_state)\<rparr>,PL_Closed_Reply)"
  using assms by (auto simp: pl_step_def pl_apply_def Let_def)

lemma scf_release_preserves_the_finite_money_view:
  assumes "pls_phase scf_state = PL_Held \<or> pls_phase scf_state = PL_Dispatched"
  shows "pl_visible_mass (pl_release PL_Closed scf_state) = pl_visible_mass scf_state"
    "pls_root_funding (pl_release PL_Closed scf_state) = pls_root_funding scf_state"
  using assms by (auto simp: pl_release_def pl_visible_mass_def pl_pending_def)

lemma scf_exact_ready_outcome_reuses_authority_lookup:
  assumes "result_access_bound scf_verified scf_actor scf_call scf_payload scf_world"
    "outcome_entries scf_world scf_call = Some scf_saved" "result_payload scf_saved = scf_payload"
    "result_completion_ready scf_saved scf_world"
  shows "read_authoritative_result scf_verified scf_actor scf_call scf_payload scf_world = Some (result_outcome scf_saved)"
  by (rule exact_retry_reads_the_committed_outcome[OF assms])

definition scf_existing_annotation :: "nat list \<Rightarrow> (nat \<times> nat option) option" where
  "scf_existing_annotation scf_words =
    (case scf_words of [scf_tag,scf_position,scf_completed] \<Rightarrow>
      (if scf_tag = 1 \<and> scf_completed = 1 then Some
        (code_source_ordinary_result \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Closed_Reply,
          source_outcome_commit = Some scf_position\<rparr>) else None)
     | _ \<Rightarrow> None)"

lemma scf_existing_closed_commit_is_preserved:
  "scf_existing_annotation [1,scf_position,1] = Some (13,Some scf_position)"
  by (simp add: scf_existing_annotation_def code_source_ordinary_result_def)

type_synonym scf_integer_result = "integer list list \<times> pl_integer_result"

definition scf_case_result where
  "scf_case_result scf_mode scf_common scf_receipt scf_packet_core scf_shape scf_request scf_state
      scf_stored scf_bound_core scf_annotation =
    (if scf_mode = 0 \<and> scf_stored = [] \<and> scf_bound_core = [] \<and> scf_annotation = [] then
       Some ([[]],pl_clock_result scf_state scf_request (pl_step True scf_request scf_state))
     else if scf_mode = 1 \<and> scf_common \<and> scf_receipt \<and> pls_connected scf_state \<and>
         plr_actor scf_request = plr_caller scf_request \<and> plr_cut_epoch scf_request = pls_epoch scf_state \<and>
         map_of (pls_sessions scf_state) (plr_session scf_request) = Some (plr_actor scf_request,pls_epoch scf_state) \<and>
         scf_packet_core = scf_bound_core \<and> scf_shape = scf_stored
     then case scf_existing_annotation scf_annotation of
         Some (scf_code,Some scf_position) \<Rightarrow> Some ([map integer_of_nat [scf_code,scf_position]],
           pl_clock_result scf_state scf_request (scf_state,PL_Closed_Reply))
       | _ \<Rightarrow> None
     else None)"

fun scf_natural_abi :: "nat list list \<Rightarrow> nat list list list \<Rightarrow> scf_integer_result option" where
  "scf_natural_abi [[scf_mode,scf_actor],scf_packet_bytes,scf_core_bytes,scf_preimage,scf_outer_signature,scf_owner_proof,
        scf_expected_shape,[scf_outer_ok,scf_token_ok,scf_owner_ok,scf_execute_ok,scf_recover_ok,scf_receipt_ok,scf_policy_ok],
        scf_stored,scf_bound_core,scf_annotation] scf_state_words =
    (if \<not> list_all (\<lambda>scf_flag. scf_flag \<le> 1)
          [scf_outer_ok,scf_token_ok,scf_owner_ok,scf_execute_ok,scf_recover_ok,scf_receipt_ok,scf_policy_ok] \<or>
        length scf_owner_proof \<noteq> 64 \<or>
        \<not> list_all (\<lambda>scf_byte. scf_byte < 256)
          (scf_packet_bytes @ scf_core_bytes @ scf_preimage @ scf_outer_signature @ scf_owner_proof @ scf_bound_core)
     then None else
      case (decode_wire_packet scf_packet_bytes,pl_clock_parse_state scf_state_words) of
        (Some scf_packet,Some scf_state) \<Rightarrow>
          let scf_core = packet_core scf_packet;
              scf_common = (scf_outer_ok = 1 \<and> scf_token_ok = 1 \<and> scf_execute_ok = 1 \<and> scf_policy_ok = 1);
              scf_verified = (scf_common \<and> scf_owner_ok = 1 \<and> scf_recover_ok = 1)
          in if encode_wire_core scf_core \<noteq> scf_core_bytes \<or> envelope_signing_bytes scf_core \<noteq> scf_preimage \<or>
                packet_signature scf_packet \<noteq> scf_outer_signature
             then None else
               (case scf_decode_request scf_core scf_actor scf_verified scf_owner_proof of
                 None \<Rightarrow> None | Some (scf_shape,scf_request) \<Rightarrow>
                   if scf_shape \<noteq> scf_expected_shape then None else
                     map_option (\<lambda>(scf_result,scf_views). ([map integer_of_nat [scf_mode,3,wire_opcode (wire_operation_body scf_core)],
                       map integer_of_nat scf_shape,map integer_of_nat scf_core_bytes] @ scf_result,scf_views))
                       (scf_case_result scf_mode scf_common (scf_receipt_ok = 1) scf_core_bytes scf_shape scf_request scf_state
                         scf_stored scf_bound_core scf_annotation))
      | _ \<Rightarrow> None)"
| "scf_natural_abi _ _ = None"

definition scf_integer_abi :: "integer list list \<Rightarrow> integer list list list \<Rightarrow> scf_integer_result option" where
  "scf_integer_abi scf_wire scf_state =
    (if list_all (list_all pl_clock_u64) scf_wire \<and> pl_clock_matrix_u64 scf_state
     then scf_natural_abi (map (map nat_of_integer) scf_wire) (map (map (map nat_of_integer)) scf_state)
     else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms scf_live_close_is_the_parent_footprint_release
      scf_release_preserves_the_finite_money_view scf_exact_ready_outcome_reuses_authority_lookup
      scf_existing_closed_commit_is_preserved every_source_ordinary_result_retains_the_existing_decoded_operands})
  then () else error "Unexpected oracle in signed Cancel/Fence link"
\<close>

export_code scf_integer_abi in SML
  module_name OIP_Signed_Cancel_Fence_Link file_prefix "oip_signed_cancel_fence_link"

end

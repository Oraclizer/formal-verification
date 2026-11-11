theory Resolver_Current_Control_Link
  imports "OIP_Resolver_Waiting_Model_Link.Resolver_Waiting_ABI"
    "OIP_P19_Threshold_Export.P19_Threshold_Export"
    "OIP_Source_Writer_JSON_G0.Source_Writer_JSON_G0"
    "OIP_Message_Code.Wire_Code_Session_Authentication"
begin

text \<open>Current ordered controls for an exact retained threshold Debit.
  The selected record supplies the stored payload, outcome and Core binding.
  The final read is either the same control or an intended valid Dispatch
  cancellation becoming visible. No physical new MOD or Txn result is an input.\<close>

record rcc_context =
  rcc_session_config :: code_source_session_config
  rcc_identity_snapshot :: code_source_identity_snapshot
  rcc_signing_peer :: code_source_signing_peer
  rcc_scope :: wire_boundary
  rcc_channel :: code_channel_guard
  rcc_registry :: p19_registry
  rcc_key_checks :: p19_key_checks
  rcc_strict_checks :: p19_strict_checks
  rcc_token_preimage :: wire_bytes
  rcc_token_signature :: wire_bytes
  rcc_host_clock :: nat
  rcc_resolution_clock :: nat
  rcc_security_preimage :: wire_bytes
  rcc_security_digest :: wire_bytes

definition rcc_curve where
  "rcc_curve rcc_facts rcc_k rcc_m rcc_s \<longleftrightarrow> List.member rcc_facts (rcc_k,rcc_m,rcc_s,True)"

definition rcc_digest where
  "rcc_digest rcc_hash rcc_raw = (case rcc_hash rcc_raw of None \<Rightarrow> [] | Some rcc_sha \<Rightarrow> rcc_sha)"

definition rcc_current_identity where
  "rcc_current_identity rcc_context rcc_hash rcc_proof =
    code_source_active_identity
      (\<lambda>_ rcc_session_proof. code_source_authenticate_session_bytes (rcc_session_config rcc_context)
        (rcc_digest rcc_hash) (rcc_curve (rcc_strict_checks rcc_context))
        (rcc_token_preimage rcc_context) (rcc_token_signature rcc_context) rcc_session_proof (Some (rcc_host_clock rcc_context)))
      () rcc_proof (rcc_identity_snapshot rcc_context)"

definition rcc_threshold_current where
  "rcc_threshold_current rcc_context rcc_raw =
    (let rcc_result = p19_export_packet (boundary_max_frame (rcc_scope rcc_context))
        [1,2] (rcc_registry rcc_context) (rcc_key_checks rcc_context) (rcc_strict_checks rcc_context) rcc_raw
     in case fst rcc_result of [] \<Rightarrow> False | rcc_tag # _ \<Rightarrow> rcc_tag = 1)"

definition rcc_receipt where
  "rcc_receipt rcc_snapshot rcc_id rcc_payload =
    (if List.member (rdw_other_claims rcc_snapshot) rcc_id then None
     else Some (Code_Source_Ordinary_Receipt (rdw_collection (fst
       (cg_collect_view (map_option (\<lambda>(rcc_saved,rcc_result).
          (rcc_saved = rcc_payload,rcc_saved = rcc_payload \<and>
            (rdw_nonfinal_saved rcc_result \<or> source_outcome_reply rcc_result = Code_Source_Accepted Code_Source_Debited_Reply),rcc_result))
        (map_of (rdw_ordinary_calls rcc_snapshot) rcc_id)))))))"

definition rcc_authorize_ordered where
  "rcc_authorize_ordered rcc_observed rcc_actor rcc_key rcc_resolve =
    (case code_source_resolution_principal_refusal rcc_observed rcc_actor of Some rcc_error \<Rightarrow> Some rcc_error
     | None \<Rightarrow> if \<not> rcc_resolve \<and> List.member (source_control_cancelled rcc_observed) rcc_key
       then Some Code_Source_Wire_Cancelled else None)"

lemma rcc_resolve_true_uses_current_revocation_and_ignores_cancellation:
  "rcc_authorize_ordered rcc_observed rcc_actor rcc_key True =
    code_source_resolution_principal_refusal rcc_observed rcc_actor"
  by (simp add: rcc_authorize_ordered_def split: option.splits)

definition rcc_key_json where
  "rcc_key_json rcc_key =
    (case rcc_key of (rcc_deployment,rcc_source,rcc_principal,rcc_uuid) \<Rightarrow>
       code_json_open_key ''deployment'' @ sw_decimal rcc_deployment @
       code_json_next_key ''source'' @ sw_decimal rcc_source @
       code_json_next_key ''principal'' @ sw_decimal rcc_principal @
       code_json_next_key ''uuid'' @ sw_json_octets rcc_uuid @ [125])"

definition rcc_dispatch_exact where
  "rcc_dispatch_exact rcc_snapshot rcc_raw =
    Option.bind (decode_wire_core rcc_raw) (\<lambda>rcc_core.
      case code_decode_ordinary rcc_core of
        Code_Ordinary_Ready rcc_native rcc_credential rcc_versions (Wire_Dispatch rcc_generation) \<Rightarrow>
          let rcc_payload = code_source_payload_from_native rcc_core rcc_native rcc_credential rcc_versions (Wire_Dispatch rcc_generation);
              rcc_key = authenticated_wire_message_id rcc_core
          in if map_of (rdw_transport_bindings rcc_snapshot) rcc_key = Some rcc_raw \<and>
                (case map_of (rdw_ordinary_calls rcc_snapshot) (native_id rcc_native) of None \<Rightarrow> False
                 | Some (rcc_saved,rcc_result) \<Rightarrow> rcc_saved = rcc_payload \<and>
                     source_outcome_reply rcc_result = Code_Source_Accepted Code_Source_Dispatched_Reply)
             then Some rcc_key else None
       | _ \<Rightarrow> None)"

fun rcc_intended_cancel where
  "rcc_intended_cancel rcc_snapshot rcc_original_key [rcc_prefix,rcc_suffix,rcc_dispatch] =
    (let rcc_raw = snd (source_control_stored (rdw_observation rcc_snapshot));
         rcc_key = code_json_next_key ''cancelled'';
         rcc_next = code_json_next_key ''decisions''
     in if source_control_cancelled (rdw_observation rcc_snapshot) = [] \<and>
           rcc_raw = rcc_prefix @ [91,93] @ rcc_suffix \<and> length rcc_key \<le> length rcc_prefix \<and>
           drop (length rcc_prefix - length rcc_key) rcc_prefix = rcc_key \<and>
           take (length rcc_next) rcc_suffix = rcc_next
        then Option.bind (rcc_dispatch_exact rcc_snapshot rcc_dispatch) (\<lambda>rcc_dispatch_key.
          let rcc_candidate = rcc_prefix @ [91] @ rcc_key_json rcc_dispatch_key @ [93] @ rcc_suffix
          in if rcc_dispatch_key \<noteq> rcc_original_key \<and> rcc_candidate \<noteq> rcc_raw
             then Some rcc_candidate else None)
        else None)"
| "rcc_intended_cancel _ _ _ = None"

lemma rcc_intended_changed_bytes_fence_every_physical_readback_revision:
  assumes "rcc_other \<noteq> snd (source_control_stored rcc_observed)"
  shows "code_source_resolution_observation_fence rcc_observed (Some (rcc_any_mod,rcc_other)) =
    Some (Code_Source_Wire_Recovery Code_Source_Recovery_Hold)"
  using assms by (cases "source_control_stored rcc_observed")
    (simp add: code_source_resolution_observation_fence_def)

lemma rcc_reference_cancel_keeps_the_other_selected_controls:
  "control_head (reference_order_cancel rcc_key rcc_state) = control_head rcc_state"
  "control_decisions (reference_order_cancel rcc_key rcc_state) = control_decisions rcc_state"
  "control_revoked (reference_order_cancel rcc_key rcc_state) = control_revoked rcc_state"
  "control_cancelled (reference_order_cancel rcc_key rcc_state) = insert rcc_key (control_cancelled rcc_state)"
  by (simp_all add: reference_order_cancel_def)

lemma rcc_published_result_holds_for_every_mod_when_the_final_bytes_changed:
  assumes principal: "code_source_resolution_principal_refusal rcc_observed rcc_actor = None"
    and status: "code_source_resolution_disposition rcc_observed rcc_request = Inr (Some Ref_Applied)"
    and pending: "code_source_pending_transport_refusal rcc_key (source_debit_packet rcc_request) (source_control_decisions rcc_observed) = None"
    and original: "rcc_prior = Some rcc_exact"
    and bytes: "rcc_other \<noteq> snd (source_control_stored rcc_observed)"
  shows "code_source_resolve_debit_tail rcc_observed rcc_request rcc_key rcc_exact rcc_prior
    (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected rcc_outcome))) False None rcc_actor rcc_epoch
    rcc_payload None (Some (rcc_any_mod,rcc_other)) None =
      (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),None)"
  using assms
  by (simp add: code_source_resolve_debit_tail_def code_compare_binding_def code_source_finish_resolution_observation_def
    rcc_intended_changed_bytes_fence_every_physical_readback_revision)

definition rcc_tail where
  "rcc_tail rcc_snapshot rcc_packet rcc_request rcc_payload rcc_actor rcc_epoch rcc_current =
    (let rcc_core = packet_core rcc_packet; rcc_key = authenticated_wire_message_id rcc_core in
      code_source_resolve_debit_tail (rdw_observation rcc_snapshot) rcc_request rcc_key (encode_wire_core rcc_core)
        (map_of (rdw_transport_bindings rcc_snapshot) rcc_key)
        (rcc_receipt rcc_snapshot (source_debit_id rcc_request) rcc_payload) False None rcc_actor rcc_epoch
        rcc_payload None rcc_current None)"

fun rcc_error_word where
  "rcc_error_word None = 0"
| "rcc_error_word (Some rcc_error) = code_source_error_number rcc_error"

fun rcc_receipt_words where
  "rcc_receipt_words (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected rcc_result))) =
    [3,case source_outcome_reply rcc_result of Code_Source_Accepted rcc_value \<Rightarrow> code_source_accepted_number rcc_value | _ \<Rightarrow> 0,
       case source_outcome_commit rcc_result of None \<Rightarrow> 0 | Some rcc_position \<Rightarrow> Suc rcc_position]"
| "rcc_receipt_words rcc_other = [rdw_receipt_word rcc_other,0,0]"

definition rcc_decode_original where
  "rcc_decode_original rcc_packet_raw rcc_packet =
    (let rcc_core = packet_core rcc_packet in
      case code_decode_original_debit rcc_packet_raw rcc_core of None \<Rightarrow> None
       | Some rcc_original \<Rightarrow>
         (case code_decode_ordinary rcc_core of
            Code_Ordinary_Ready rcc_native rcc_credential rcc_versions (Wire_Debit rcc_generation) \<Rightarrow>
              Some (rdw_original_request rcc_original,
                code_source_payload_from_native rcc_core rcc_native rcc_credential rcc_versions (Wire_Debit rcc_generation))
          | _ \<Rightarrow> None))"

definition rcc_boundary_ok where
  "rcc_boundary_ok rcc_context rcc_cut =
    (let rcc_current_scope = (rcc_scope rcc_context)\<lparr>boundary_now := rcc_host_clock rcc_context\<rparr>
     in case code_boundary_at (Some (rcc_current_scope,source_signing_public_key (rcc_signing_peer rcc_context)))
          (rcc_channel rcc_context) (boundary_deployment rcc_current_scope) rcc_cut None False of
          Inl _ \<Rightarrow> False | Inr _ \<Rightarrow> True)"

definition rcc_run where
  "rcc_run rcc_context rcc_hash rcc_snapshot rcc_raw rcc_core_raw rcc_late =
    (if \<not> rdw_selected_ok rcc_hash rcc_snapshot \<or>
        rcc_hash (rcc_security_preimage rcc_context) \<noteq> Some (rcc_security_digest rcc_context) then [[0]]
     else case decode_wire_packet rcc_raw of None \<Rightarrow> [[0]]
       | Some rcc_packet \<Rightarrow> (case rcc_decode_original rcc_raw rcc_packet of None \<Rightarrow> [[0]]
        | Some (rcc_request,rcc_payload) \<Rightarrow>
          let rcc_core = packet_core rcc_packet; rcc_key = authenticated_wire_message_id rcc_core;
              rcc_proof = \<lparr>proof_session = source_payload_session rcc_payload,
                proof_epoch = cut_authority_epoch (rdw_cut rcc_snapshot)\<rparr>;
              rcc_identity = rcc_current_identity rcc_context rcc_hash rcc_proof;
              rcc_scope_value = (rcc_scope rcc_context)\<lparr>boundary_now := rcc_resolution_clock rcc_context\<rparr>
          in if encode_wire_core rcc_core \<noteq> rcc_core_raw \<or> wire_signature_scheme rcc_core \<noteq> 2 \<or>
                rcc_resolution_clock rcc_context \<noteq> wire_sent_seconds rcc_core \<or>
                \<not> rcc_boundary_ok rcc_context (rdw_cut rcc_snapshot) \<or>
                \<not> rcc_threshold_current rcc_context rcc_raw \<or> code_check_versioned_scope rcc_core rcc_scope_value 6 \<noteq> None
             then [[0]]
             else case rcc_identity of None \<Rightarrow> [[0]] | Some rcc_actor \<Rightarrow>
               if identity_principal rcc_actor \<noteq> wire_principal rcc_core \<or> identity_domain rcc_actor \<noteq> wire_source_domain rcc_core \<or>
                  \<not> code_source_session_call_grant (rcc_signing_peer rcc_context) (proof_session rcc_proof)
                    (wire_target_domain rcc_core) Read_Receipt (source_binding_asset (source_payload_binding rcc_payload))
               then [[0]]
               else let rcc_before = source_control_stored (rdw_observation rcc_snapshot);
                        rcc_intent = (if rcc_late = [] then Some (snd rcc_before)
                          else rcc_intended_cancel rcc_snapshot rcc_key rcc_late)
                    in case rcc_intent of None \<Rightarrow> [[0]] | Some rcc_final_bytes \<Rightarrow>
                       [rdw_request_words rcc_request] @ rdw_payload_rows rcc_payload @
                       [[identity_principal rcc_actor,
                           rdw_disposition_words (code_source_resolution_disposition (rdw_observation rcc_snapshot) rcc_request),
                           rdw_arrival_word (code_compare_binding (map_of (rdw_transport_bindings rcc_snapshot) rcc_key) rcc_core_raw)],
                         rcc_receipt_words (rcc_receipt rcc_snapshot (source_debit_id rcc_request) rcc_payload),
                         [rcc_error_word (rcc_authorize_ordered (rdw_observation rcc_snapshot) (identity_principal rcc_actor) rcc_key False),
                          rcc_error_word (rcc_authorize_ordered (rdw_observation rcc_snapshot) (identity_principal rcc_actor) rcc_key True)],
                         rdw_tail_words (rcc_tail rcc_snapshot rcc_packet rcc_request rcc_payload (identity_principal rcc_actor)
                           (proof_epoch rcc_proof) (Some (fst rcc_before,rcc_final_bytes))),
                         (if rcc_late = [] then [] else rcc_final_bytes)]))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms rcc_resolve_true_uses_current_revocation_and_ignores_cancellation
    rcc_intended_changed_bytes_fence_every_physical_readback_revision
    rcc_reference_cancel_keeps_the_other_selected_controls rcc_published_result_holds_for_every_mod_when_the_final_bytes_changed})
  then () else error "Unexpected oracle in resolver current control"
\<close>

end

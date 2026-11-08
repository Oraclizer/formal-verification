theory Wire_Code_Typed_Metadata_Values
  imports Wire_Code_Typed_Call_Values
begin

fun code_ir_query :: "application_query \<Rightarrow> nat list" where
  "code_ir_query (Application_Value oip_binder_asset) = code_ir_node 160 [code_ir_scalar oip_binder_asset]"
| "code_ir_query (Source_Balance oip_binder_account) = code_ir_node 161 [code_ir_pair oip_binder_account]"
| "code_ir_query (Destination_Balance oip_binder_account) = code_ir_node 162 [code_ir_triple oip_binder_account]"
| "code_ir_query (Root_Balance oip_binder_origin oip_binder_account) =
    code_ir_node 163 [code_ir_pair oip_binder_origin,code_ir_triple oip_binder_account]"
| "code_ir_query (Regulatory_State oip_binder_domain oip_binder_asset) =
    code_ir_node 164 [code_ir_scalar oip_binder_domain,code_ir_scalar oip_binder_asset]"
| "code_ir_query (Terminal_Receipt oip_binder_origin) = code_ir_node 165 [code_ir_pair oip_binder_origin]"

fun code_ir_read_request :: "identity_read_request \<Rightarrow> nat list" where
  "code_ir_read_request (Current_Data oip_binder_query oip_binder_expected) =
    code_ir_node 150 [code_ir_query oip_binder_query,code_ir_cut oip_binder_expected]"
| "code_ir_read_request (Historical_Data oip_binder_query oip_binder_revision) =
    code_ir_node 151 [code_ir_query oip_binder_query,code_ir_scalar oip_binder_revision]"
| "code_ir_read_request (Raw_Data oip_binder_query) = code_ir_node 152 [code_ir_query oip_binder_query]"
| "code_ir_read_request (Operation_Status oip_binder_origin) = code_ir_node 153 [code_ir_pair oip_binder_origin]"
| "code_ir_read_request Authority_Journal = code_ir_node 154 []"
| "code_ir_read_request (Owner_Data oip_binder_asset) = code_ir_node 155 [code_ir_scalar oip_binder_asset]"

definition code_ir_session_proof :: "session_proof \<Rightarrow> nat list" where
  "code_ir_session_proof oip_binder_proof = code_ir_node 104
    [code_ir_scalar (proof_session oip_binder_proof),code_ir_scalar (proof_epoch oip_binder_proof)]"

fun code_ir_parsed_query :: "parsed_wire_query \<Rightarrow> nat list" where
  "code_ir_parsed_query (Wire_Read_Request oip_binder_proof oip_binder_request) =
    code_ir_node 13 [code_ir_session_proof oip_binder_proof,code_ir_read_request oip_binder_request]"
| "code_ir_parsed_query (Wire_Cache_Request oip_binder_proof oip_binder_query) =
    code_ir_node 14 [code_ir_session_proof oip_binder_proof,code_ir_query oip_binder_query]"

definition code_ir_ack :: "native_scheduled_ack \<Rightarrow> nat list" where
  "code_ir_ack oip_binder_ack = code_ir_node 17 [code_ir_node 105
    [code_ir_pair (fst (scheduled_ack_key oip_binder_ack)),code_ir_scalar (snd (scheduled_ack_key oip_binder_ack)),
     code_ir_scalar (scheduled_ack_target oip_binder_ack),code_ir_scalar (scheduled_ack_asset oip_binder_ack),
     code_ir_scalar (scheduled_ack_owner oip_binder_ack),code_ir_scalar (scheduled_ack_destination oip_binder_ack),
     code_ir_scalar (scheduled_ack_recipient oip_binder_ack),code_ir_scalar (scheduled_ack_amount oip_binder_ack),
     code_ir_scalar (scheduled_ack_epoch oip_binder_ack),
     code_ir_scalar (case scheduled_ack_kind oip_binder_ack of Confirmed_Decision \<Rightarrow> 1 | Reversed_Decision \<Rightarrow> 2)]]"

definition code_ir_capability :: "code_raw_capability_offer \<Rightarrow> nat list" where
  "code_ir_capability oip_binder_offer = code_ir_node 18
    [code_ir_scalar (capability_deployment oip_binder_offer),code_ir_scalar (capability_sender oip_binder_offer),
     code_ir_scalar (capability_receiver oip_binder_offer),code_ir_scalar (capability_challenge oip_binder_offer),
     code_ir_scalar (capability_expires oip_binder_offer),code_ir_set (capability_versions oip_binder_offer),
     code_ir_set (capability_families oip_binder_offer),code_ir_set (capability_atomicities oip_binder_offer),
     code_ir_set (capability_schemes oip_binder_offer)]"

fun code_ir_heartbeat :: "wire_core \<Rightarrow> code_heartbeat_fields \<Rightarrow> nat list option" where
  "code_ir_heartbeat oip_binder_core (Code_Capabilities oip_binder_challenge oip_binder_expires oip_binder_versions oip_binder_families oip_binder_atomicities oip_binder_schemes) =
    map_option code_ir_capability
      (code_capability_offer oip_binder_core (Code_Capabilities oip_binder_challenge oip_binder_expires oip_binder_versions oip_binder_families oip_binder_atomicities oip_binder_schemes))"
| "code_ir_heartbeat oip_binder_core (Code_Liveness oip_binder_challenge oip_binder_expires) =
    Some (code_ir_node 19 [code_ir_scalar oip_binder_challenge,code_ir_scalar oip_binder_expires])"

definition code_ir_dependency :: "(nat \<times> nat list) \<Rightarrow> nat list" where
  "code_ir_dependency oip_binder_dependency = code_ir_node 109
    [code_ir_scalar (fst oip_binder_dependency),code_ir_list code_ir_scalar (snd oip_binder_dependency)]"

definition code_ir_context :: "code_json_endpoint_context \<Rightarrow> nat list" where
  "code_ir_context oip_binder_context = code_ir_node 106
    [code_ir_scalar (json_context_endpoint oip_binder_context),code_ir_scalar (json_context_epoch oip_binder_context),
     code_ir_list code_ir_triple (json_context_grants oip_binder_context),
     code_ir_list code_ir_dependency (json_context_dependencies oip_binder_context),
     code_ir_list code_ir_triple (json_context_write_permissions oip_binder_context)]"

definition code_ir_session_binding :: "(nat \<times> code_json_session_binding) \<Rightarrow> nat list" where
  "code_ir_session_binding oip_binder_entry = code_ir_node 107
    [code_ir_scalar (fst oip_binder_entry),code_ir_scalar (json_session_principal (snd oip_binder_entry)),
     code_ir_scalar (json_session_epoch (snd oip_binder_entry))]"

fun code_ir_governance :: "code_governance_fields \<Rightarrow> nat list" where
  "code_ir_governance (Code_Governance_Handover oip_binder_session oip_binder_selected_cut oip_binder_asset oip_binder_previous oip_binder_successor oip_binder_old_session oip_binder_new_session oip_binder_epoch oip_binder_contexts oip_binder_first oip_binder_second) =
    code_ir_node 20 [code_ir_scalar oip_binder_session,code_ir_cut oip_binder_selected_cut,code_ir_scalar oip_binder_asset,
      code_ir_scalar oip_binder_previous,code_ir_scalar oip_binder_successor,code_ir_scalar oip_binder_old_session,
      code_ir_scalar oip_binder_new_session,code_ir_scalar oip_binder_epoch,code_ir_list code_ir_context oip_binder_contexts,
      code_ir_bytes oip_binder_first,code_ir_bytes oip_binder_second]"
| "code_ir_governance (Code_Governance_Install oip_binder_session oip_binder_selected_cut oip_binder_epoch oip_binder_contexts oip_binder_sessions oip_binder_proof) =
    code_ir_node 21 [code_ir_scalar oip_binder_session,code_ir_cut oip_binder_selected_cut,code_ir_scalar oip_binder_epoch,
      code_ir_list code_ir_context oip_binder_contexts,code_ir_list code_ir_session_binding oip_binder_sessions,
      code_ir_bytes oip_binder_proof]"

lemma a_parsed_current_read_keeps_both_the_actual_query_and_expected_cut:
  "code_ir_parsed_query (Wire_Read_Request oip_binder_proof (Current_Data oip_binder_query oip_binder_expected)) =
    code_ir_node 13 [code_ir_session_proof oip_binder_proof,
      code_ir_node 150 [code_ir_query oip_binder_query,code_ir_cut oip_binder_expected]]"
  by simp

lemma a_settlement_ack_summary_is_from_the_existing_native_product_parser:
  "map_option code_ir_ack (code_decode_settlement_ack oip_binder_core) =
    map_option code_ir_ack (parse_native_scheduled_ack oip_binder_core)"
  by (simp add: the_source_settlement_ack_parser_has_the_existing_exact_product_value)

lemma governance_summary_keeps_the_decoded_contexts_and_both_proofs:
  "code_ir_governance (Code_Governance_Handover oip_binder_session oip_binder_selected_cut oip_binder_asset oip_binder_previous oip_binder_successor oip_binder_old_session oip_binder_new_session oip_binder_epoch oip_binder_contexts oip_binder_first oip_binder_second) =
    code_ir_node 20 [code_ir_scalar oip_binder_session,code_ir_cut oip_binder_selected_cut,code_ir_scalar oip_binder_asset,
      code_ir_scalar oip_binder_previous,code_ir_scalar oip_binder_successor,code_ir_scalar oip_binder_old_session,
      code_ir_scalar oip_binder_new_session,code_ir_scalar oip_binder_epoch,code_ir_list code_ir_context oip_binder_contexts,
      code_ir_bytes oip_binder_first,code_ir_bytes oip_binder_second]"
  by simp

end

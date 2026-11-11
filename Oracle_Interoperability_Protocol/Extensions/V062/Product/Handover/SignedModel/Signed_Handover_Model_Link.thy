theory Signed_Handover_Model_Link
  imports "OIP_Message_Code.Wire_Code_Typed_Summary_Check"
    "OIP_Message_Code.Wire_Code_Read_Service"
    "OIP_V062_Handover_Finite_Export.Handover_Finite_Export"
    "OIP_Reference_Execution.Reference_Signed_Handover_Sessions"
begin

definition shm_packet where
  "shm_packet shm_limit shm_raw shm_exact =
    (if code_check_declared_version shm_raw shm_limit \<noteq> None then None
     else Option.bind (decode_wire_packet shm_raw) (\<lambda>shm_decoded.
       if encode_wire_packet shm_decoded = shm_raw \<and>
          encode_wire_core (packet_core shm_decoded) = shm_exact \<and>
          wire_signature_scheme (packet_core shm_decoded) = 2
       then Some shm_decoded else None))"

definition shm_governance :: "nat list list list \<Rightarrow> nat list list option" where
  "shm_governance shm_input =
    (case shm_input of [[shm_raw,shm_exact],[[shm_limit]]] \<Rightarrow>
       Option.bind (shm_packet shm_limit shm_raw shm_exact) (\<lambda>shm_decoded.
         let shm_core = packet_core shm_decoded in
         if wire_message_family shm_core \<noteq> Wire_Governance \<or> wire_opcode (wire_operation_body shm_core) \<noteq> 1
         then None else
         (case code_decode_governance shm_core of
           Some (Code_Governance_Handover shm_outer_session shm_cut shm_asset shm_former shm_incoming
             shm_old_session shm_new_session shm_new_epoch shm_contexts shm_left shm_right) \<Rightarrow>
             Some [[shm_outer_session,cut_authority_epoch shm_cut,cut_revision shm_cut,shm_asset,shm_former,
               shm_incoming,shm_old_session,shm_new_session,shm_new_epoch,length shm_contexts],
               encode_wire_core shm_core,packet_signature shm_decoded,shm_left,shm_right]
         | _ \<Rightarrow> None))
     | _ \<Rightarrow> None)"

definition shm_binding where
  "shm_binding shm_principal shm_epoch = \<lparr>session_principal = shm_principal,session_epoch = shm_epoch\<rparr>"

definition shm_registrations where
  "shm_registrations shm_registry shm_key =
    map fst (filter (\<lambda>shm_entry. List.member (snd shm_entry) shm_key) shm_registry)"

definition shm_session_binding where
  "shm_session_binding shm_next_epoch shm_registry shm_live_keys shm_installed =
    list_all (\<lambda>shm_key. case shm_installed shm_key of None \<Rightarrow> True
       | Some shm_live \<Rightarrow> session_epoch shm_live = shm_next_epoch \<and>
          shm_registrations shm_registry shm_key = [session_principal shm_live]) shm_live_keys"

definition shm_batch where
  "shm_batch shm_next_epoch shm_endpoints shm_assets shm_contexts =
    (map json_context_endpoint shm_contexts = shm_endpoints \<and>
      list_all (\<lambda>shm_ctx. json_context_epoch shm_ctx = shm_next_epoch \<and>
        list_all (\<lambda>shm_dep. List.member shm_assets (fst shm_dep) \<and>
           list_all (List.member shm_assets) (snd shm_dep)) (json_context_dependencies shm_ctx) \<and>
        list_all (\<lambda>(shm_actor,shm_asset,shm_version). List.member shm_assets shm_asset)
          (json_context_write_permissions shm_ctx)) shm_contexts)"

definition shm_run where
  "shm_run shm_decoded shm_current_epoch shm_current_revision shm_policy_epoch shm_maintainer
      shm_deployment shm_source shm_target shm_flags shm_before_owners shm_before_sessions
      shm_endpoints shm_assets shm_ledger_maintainers shm_policy_maintainers shm_transfer_grant
      shm_registry shm_old_binding shm_next_binding shm_immutable shm_first shm_second =
    (let shm_core = packet_core shm_decoded in
     if wire_message_family shm_core \<noteq> Wire_Governance \<or> wire_opcode (wire_operation_body shm_core) \<noteq> 1
     then None else
     (case code_decode_governance shm_core of
       Some (Code_Governance_Handover shm_outer_session shm_cut shm_asset shm_former shm_incoming
         shm_old_session shm_new_session shm_new_epoch shm_contexts shm_left shm_right) \<Rightarrow>
         (if shm_left \<noteq> shm_first \<or> shm_right \<noteq> shm_second then None else
          let shm_context_count = length shm_contexts;
              shm_revision = shm_current_revision + shm_context_count;
              shm_proposal = \<lparr>transfer_asset = shm_asset,transfer_previous = shm_former,
                 transfer_successor = shm_incoming,transfer_expected = shm_cut,transfer_old_session = shm_old_session,
                 transfer_new_session = shm_new_session,transfer_epoch = shm_new_epoch,transfer_contexts = []\<rparr>;
              shm_code = \<lparr>rust_handover_owner = map_of shm_before_owners,
                 rust_handover_sessions = map_of shm_before_sessions,rust_handover_epoch = shm_current_epoch,
                 rust_handover_ledger = shm_immutable\<rparr>;
              shm_live_keys = remdups (shm_new_session # map fst shm_before_sessions);
              shm_bound = (case native_replace_handover_sessions shm_proposal (rust_handover_sessions shm_code) of
                 None \<Rightarrow> False | Some shm_installed \<Rightarrow>
                   shm_session_binding shm_policy_epoch shm_registry shm_live_keys shm_installed);
              shm_external = take 3 shm_flags = [1,1,1] \<and> drop 4 shm_flags = [1] \<and>
                 cut_authority_epoch shm_cut = shm_current_epoch \<and> cut_revision shm_cut = shm_current_revision \<and>
                 wire_principal shm_core = shm_former \<and> wire_source_domain shm_core = shm_source \<and>
                 wire_target_domain shm_core = shm_target \<and> wire_deployment shm_core = shm_deployment \<and>
                 shm_former \<noteq> shm_incoming \<and> List.member shm_transfer_grant shm_asset \<and>
                 List.member shm_ledger_maintainers shm_maintainer \<and> List.member shm_policy_maintainers shm_maintainer \<and>
                 shm_batch shm_new_epoch shm_endpoints shm_assets shm_contexts \<and>
                 shm_current_epoch < shm_new_epoch \<and> shm_revision < 18446744073709551616;
              shm_ready = shm_flags ! 3 = 1 \<and> shm_new_epoch = shm_policy_epoch \<and>
                 List.member (shm_registrations shm_registry shm_new_session) shm_incoming \<and>
                 \<not> List.member (shm_registrations shm_registry shm_old_session) shm_former;
              (shm_after,shm_changed) = rust_handover_step shm_external (shm_ready \<and> shm_bound) shm_proposal shm_code;
              shm_owner_keys = remdups (shm_asset # map fst shm_before_owners)
          in Some (
            [[if shm_changed then 1 else 0,
              if shm_external then 1 else 0,if shm_ready then 1 else 0,if shm_bound then 1 else 0],
             [shm_outer_session,cut_authority_epoch shm_cut,cut_revision shm_cut,shm_asset,
              shm_former,shm_incoming,shm_old_session,shm_new_session,shm_new_epoch,shm_context_count],
             [rust_handover_epoch shm_after,if shm_changed then shm_revision else shm_current_revision],
             (if shm_changed then shm_next_binding else shm_old_binding),rust_handover_ledger shm_after,
             shm_left,shm_right,encode_wire_core shm_core] @
            map (\<lambda>shm_id. shm_id # hfe_owner_row (rust_handover_owner shm_after shm_id)) shm_owner_keys @
            map (\<lambda>shm_key. hfe_session_row shm_key (rust_handover_sessions shm_after shm_key)) shm_live_keys))
     | _ \<Rightarrow> None))"

definition shm_handover where
  "shm_handover shm_input =
    (case shm_input of
       [[shm_raw,shm_exact,shm_first,shm_second,shm_old_binding,shm_next_binding,shm_immutable],
        [[shm_limit,shm_current_epoch,shm_current_revision,shm_policy_epoch,shm_maintainer,
          shm_deployment,shm_source,shm_target]],
        [shm_flags],shm_owners,shm_sessions,
        [shm_endpoints,shm_assets,shm_ledger_maintainers,shm_policy_maintainers,shm_transfer_grant],shm_registry] \<Rightarrow>
          if length shm_flags = 5 \<and> list_all (\<lambda>shm_flag. shm_flag \<le> 1) shm_flags \<and>
             length shm_old_binding = 32 \<and> length shm_next_binding = 32 \<and>
             list_all (\<lambda>shm_row. length shm_row = 2) shm_owners \<and>
             list_all (\<lambda>shm_row. length shm_row = 3) shm_sessions \<and>
             list_all (\<lambda>shm_row. shm_row \<noteq> []) shm_registry \<and>
             distinct (map hd shm_owners) \<and> distinct (map hd shm_sessions) \<and> distinct (map hd shm_registry)
          then Option.bind (shm_packet shm_limit shm_raw shm_exact) (\<lambda>shm_decoded.
            shm_run shm_decoded shm_current_epoch shm_current_revision shm_policy_epoch shm_maintainer
              shm_deployment shm_source shm_target shm_flags
              (map (\<lambda>shm_row. (shm_row ! 0,shm_row ! 1)) shm_owners)
              (map (\<lambda>shm_row. (shm_row ! 0,shm_binding (shm_row ! 1) (shm_row ! 2))) shm_sessions)
              shm_endpoints shm_assets shm_ledger_maintainers shm_policy_maintainers shm_transfer_grant
              (map (\<lambda>shm_row. (hd shm_row,tl shm_row)) shm_registry)
              shm_old_binding shm_next_binding shm_immutable shm_first shm_second)
          else None
     | _ \<Rightarrow> None)"

definition shm_read :: "nat list list list \<Rightarrow> nat list list option" where
  "shm_read shm_input =
    (case shm_input of [[shm_raw,shm_exact],[[shm_limit,shm_epoch,shm_revision,shm_outer]]] \<Rightarrow>
       Option.bind (shm_packet shm_limit shm_raw shm_exact) (\<lambda>shm_decoded.
         let shm_core = packet_core shm_decoded in
         (case code_source_nonreceipt_read_service (0::nat) shm_core of
            Some (Service_Read _ shm_proof shm_target (Current_Data (Source_Balance shm_account) shm_cut) None) \<Rightarrow>
              Some [[shm_outer,if cut_authority_epoch shm_cut = shm_epoch \<and> cut_revision shm_cut = shm_revision
                               then 1 else 0],
                [proof_session shm_proof,proof_epoch shm_proof,shm_target,
                  cut_authority_epoch shm_cut,cut_revision shm_cut,fst shm_account,snd shm_account],
                encode_wire_core shm_core,packet_signature shm_decoded]
          | _ \<Rightarrow> None))
     | _ \<Rightarrow> None)"

lemma shm_context_carrier_erasure_is_only_for_the_atomic_projection:
  "rust_handover_step shm_external shm_ready (shm_proposal\<lparr>transfer_contexts := shm_contexts\<rparr>) shm_code =
    rust_handover_step shm_external shm_ready shm_proposal shm_code"
  by (simp add: rust_handover_step_def native_replace_handover_sessions_def)

lemma shm_atomic_projection_carries_the_same_ledger:
  "rust_handover_ledger (fst (rust_handover_step shm_external shm_ready shm_proposal shm_code)) =
    rust_handover_ledger shm_code"
  by (simp add: rust_handover_step_def split: if_splits option.splits)

definition shm_u64 :: "integer \<Rightarrow> bool" where
  "shm_u64 shm_value \<longleftrightarrow> 0 \<le> shm_value \<and> shm_value < 18446744073709551616"

definition shm_handover_integer_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "shm_handover_integer_abi shm_input =
    (if list_all (list_all (list_all shm_u64)) shm_input
     then map_option (map (map integer_of_nat)) (shm_handover (map (map (map nat_of_integer)) shm_input))
     else None)"

definition shm_read_integer_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "shm_read_integer_abi shm_input =
    (if list_all (list_all (list_all shm_u64)) shm_input
     then map_option (map (map integer_of_nat)) (shm_read (map (map (map nat_of_integer)) shm_input))
     else None)"

definition shm_governance_integer_abi :: "integer list list list \<Rightarrow> integer list list option" where
  "shm_governance_integer_abi shm_input =
    (if list_all (list_all (list_all shm_u64)) shm_input
     then map_option (map (map integer_of_nat)) (shm_governance (map (map (map nat_of_integer)) shm_input))
     else None)"

thm_oracles shm_context_carrier_erasure_is_only_for_the_atomic_projection shm_atomic_projection_carries_the_same_ledger

export_code shm_governance_integer_abi shm_handover_integer_abi shm_read_integer_abi in SML
  module_name OIP_Signed_Handover_Model_ABI file_prefix "oip_signed_handover_model_abi"

end

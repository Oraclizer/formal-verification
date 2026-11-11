theory Response_Signer_Parse_Probe
  imports "OIP_Response_Egress_V061_V5.Response_Egress_V061_Packet"
begin

definition signer_probe_direct where
  "signer_probe_direct rows preimage =
    (case code_full_context_from_integer rows of None \<Rightarrow> False
     | Some context \<Rightarrow> response_v061_sign_guard context preimage)"

lemma signer_probe_direct_is_the_existing_signer_guard:
  assumes "code_full_context_from_integer rows = Some context"
  shows "signer_probe_direct rows preimage = response_v061_sign_guard context preimage"
  using assms by (simp add: signer_probe_direct_def)

definition signer_probe_bit where
  "signer_probe_bit value = (if value then 1 else (0 :: nat))"

definition signer_probe_core_fields where
  "signer_probe_core_fields core =
    [family_number (wire_message_family core), wire_opcode (wire_operation_body core),
      length (wire_blobs (wire_operation_body core)), length (wire_words (wire_operation_body core))]"

definition signer_probe_raw_original where
  "signer_probe_raw_original core =
    (case wire_blobs (wire_operation_body core) of [raw] \<Rightarrow> raw | _ \<Rightarrow> [])"

definition signer_probe_operand_fields where
  "signer_probe_operand_fields depth core =
    (case response_v061_operand depth core of Inl reason \<Rightarrow> [3, code_transport_refusal_number reason]
     | Inr operand \<Rightarrow> if operand = Response_V061_Legacy_Operand Code_Nested_Response then [1] else [2])"

definition signer_probe_status_fields where
  "signer_probe_status_fields original view =
    (let kind = response_decoded_kind view; number = response_decoded_number view;
         position = response_decoded_position view;
         status = response_v061_status original kind number position
     in [reference_response_kind_number kind, number, signer_probe_bit (position \<noteq> None),
           (case position of None \<Rightarrow> 0 | Some revision \<Rightarrow> revision),
           (case status of None \<Rightarrow> 0 | Some (Code_Known_Response _ _) \<Rightarrow> 1
             | Some (Code_Unknown_Response _ _) \<Rightarrow> 2)])"

text \<open>This is an independent enclosed-original compatibility view. A directly
supplied preimage does not supply a separately retained caller argument. The
diagnostic calls neither the runtime caller nor its earlier egress gate.\<close>

definition signer_probe_enclosed_call_fields where
  "signer_probe_enclosed_call_fields probe_depth probe_core =
    (case response_v061_parse False probe_depth probe_core of Inl probe_reason \<Rightarrow> [0, code_transport_refusal_number probe_reason]
     | Inr probe_view \<Rightarrow> let probe_original = response_decoded_original probe_view in
       case response_v061_original_caller probe_original of Inl probe_reason \<Rightarrow> [1, code_transport_refusal_number probe_reason]
       | Inr (probe_caller_principal,probe_caller_sequence) \<Rightarrow> [2,probe_caller_principal,probe_caller_sequence] @ signer_probe_status_fields probe_original probe_view)"

definition signer_probe_views where
  "signer_probe_views probe_context probe_preimage =
    (case response_fixed_unframe probe_preimage of None \<Rightarrow> replicate 8 []
     | Some probe_outer \<Rightarrow>
       let probe_original = sync_single_original probe_outer;
           probe_depth = map_option (response_config_max_nesting \<circ> full_response_config) probe_context
       in [signer_probe_core_fields probe_outer,
           (case probe_original of None \<Rightarrow> [] | Some probe_inner \<Rightarrow> signer_probe_core_fields probe_inner),
           (case probe_depth of None \<Rightarrow> [] | Some probe_fuel \<Rightarrow> signer_probe_operand_fields probe_fuel probe_outer),
           [signer_probe_bit (response_v061_signing_scope probe_outer)],
           (case probe_depth of None \<Rightarrow> [] | Some probe_fuel \<Rightarrow> signer_probe_enclosed_call_fields probe_fuel probe_outer),
           encode_wire_core probe_outer, signer_probe_raw_original probe_outer,
           (case probe_original of None \<Rightarrow> [] | Some probe_inner \<Rightarrow> encode_wire_core probe_inner)])"

definition response_signer_parse_integer :: "integer list list \<Rightarrow> integer list \<Rightarrow> integer list list option" where
  "response_signer_parse_integer probe_rows probe_bytes =
    (if \<not> code_integer_octet_values probe_bytes then None
     else let probe_preimage = map nat_of_integer probe_bytes;
              probe_context = code_full_context_from_integer probe_rows;
              probe_direct = signer_probe_direct probe_rows probe_preimage
          in Some (map (map integer_of_nat)
            ([signer_probe_bit (probe_context \<noteq> None), signer_probe_bit probe_direct] # signer_probe_views probe_context probe_preimage)))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms signer_probe_direct_is_the_existing_signer_guard})
  then () else error "Unexpected oracle in the signer guard projection"
\<close>

export_code response_signer_parse_integer
  in SML module_name OIP_Response_Signer_Parse_ABI file_prefix "oip_response_signer_parse_abi"

end

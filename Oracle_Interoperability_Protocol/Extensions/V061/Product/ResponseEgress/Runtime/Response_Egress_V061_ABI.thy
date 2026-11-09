theory Response_Egress_V061_ABI
  imports "OIP_Response_Egress_V061_V5.Response_Egress_V061_Packet"
begin

type_synonym response_v061_sender_input =
  "code_response_full_context \<times> bool \<times> bool \<times> nat option \<times> response_v061_observation option \<times> wire_bytes \<times>
     code_full_hash_table \<times> code_full_sign_table \<times> code_full_verify_table"

definition response_v061_sender_input where
  "response_v061_sender_input rows mode reply v061_present retained raw hash_rows sign_rows verify_rows =
    (if length rows < 14 \<or> length (rows ! 6) \<noteq> 9 \<or> (rows ! 6 ! 7) \<notin> {0,1} \<or> (rows ! 6 ! 8) \<notin> {0,1} \<or>
        \<not> code_integer_u64_values (mode # reply @ retained) \<or> \<not> code_integer_octet_values raw then None
     else Option.bind (code_full_context_from_integer (rows[6 := take 7 (rows ! 6)])) (\<lambda>context.
       Option.bind (if mode = 3 then (if reply = [] \<and> \<not> v061_present \<and> retained = [] then Some None else None)
         else map_option Some (response_v061_decode_observation (nat_of_integer mode) (map nat_of_integer reply)
           v061_present (map nat_of_integer retained))) (\<lambda>observed.
         map_option (\<lambda>(hashes,signatures,verifications).
           (context,rows ! 6 ! 7 = 1,rows ! 6 ! 8 = 1,code_response_list_atomicity (map nat_of_integer (rows ! 2)),
             observed,map nat_of_integer raw,hashes,signatures,verifications))
           (code_full_tables_from_integer hash_rows sign_rows verify_rows))))"

definition response_v061_selected_original where
  "response_v061_selected_original include_original context accept_sync accept_current selected_mode verify raw =
    (if include_original then response_v061_original_preflight context accept_sync accept_current selected_mode verify raw
     else response_v061_packet_caller raw)"

definition response_v061_missing_original_verification where
  "response_v061_missing_original_verification context raw verifications =
    (case sync_decode_packet raw of None \<Rightarrow> [] | Some packet \<Rightarrow>
      let channel = full_response_channel context; core = packet_core packet in
      if wire_signature_scheme core = 2 \<or> wire_signature_scheme core \<notin> negotiated_schemes (response_channel_profile channel)
      then [] else code_full_need_verify verifications (response_channel_remote_key channel)
        (envelope_signing_bytes core) (packet_signature packet))"

definition response_v061_original_plan where
  "response_v061_original_plan include_original context accept_sync accept_current selected_mode raw verifications =
    (let selected = response_v061_selected_original include_original context accept_sync accept_current selected_mode
        (code_full_probe_verify verifications) raw
     in (selected,if include_original \<and> selected = Inl Invalid_Wire_Signature then
          response_v061_missing_original_verification context raw verifications else []))"

definition response_v061_plan_after_uuid where
  "response_v061_plan_after_uuid context original atomicity words binding hashes signatures verifications rows =
    (let config = full_response_config context; channel = full_response_channel context in
     case response_fixed_parameters_from (code_full_hash hashes) config channel (full_parameters_clock context) binding of
       None \<Rightarrow> ([],rows)
     | Some parameters \<Rightarrow>
       let with_parameters = (rows[8 := response_parameter_uuid parameters])[9 :=
              [response_parameter_principal parameters,response_parameter_key parameters,response_parameter_epoch parameters,
               response_parameter_issued parameters,response_parameter_ttl parameters,response_parameter_route parameters]];
           core = response_fixed_core channel parameters atomicity words original
       in if response_parameter_issued parameters > response_channel_expires channel then ([],with_parameters)
       else case code_typed_encode_core core of None \<Rightarrow> ([],with_parameters) | Some core_bytes \<Rightarrow>
         if length core_bytes \<ge> 2^32 then ([],with_parameters)
         else let preimage = envelope_signing_bytes core; allowed = response_v061_sign_guard context preimage;
                  attempted = (((with_parameters[10 := core_bytes])[11 := preimage])[12 := [if allowed then 1 else 0]]);
                  v061_key = response_channel_local_key channel
              in if \<not> allowed then ([],attempted)
                 else case code_full_lookup_sign signatures v061_key preimage of
                   None \<Rightarrow> ([code_full_sign_query v061_key preimage],attempted)
                 | Some signature \<Rightarrow> (code_full_need_verify verifications v061_key preimage signature,attempted[13 := signature]))"

definition response_v061_plan_after_binding where
  "response_v061_plan_after_binding context original atomicity words binding hashes signatures verifications rows =
    (let config = full_response_config context; channel = full_response_channel context in
     if \<not> response_fixed_channel_current config channel then ([],rows)
     else case full_parameters_clock context of None \<Rightarrow> ([],rows) | Some issued \<Rightarrow>
       let uuid_message = response_fixed_uuid_preimage config binding issued;
           with_uuid_message = rows[6 := uuid_message]
       in case code_full_lookup_hash hashes uuid_message of
         None \<Rightarrow> ([code_full_hash_query uuid_message],with_uuid_message)
       | Some digest \<Rightarrow> response_v061_plan_after_uuid context original atomicity words binding hashes signatures verifications
           (with_uuid_message[7 := digest]))"

definition response_v061_plan_selected where
  "response_v061_plan_selected context selected_mode packet call result hashes signatures verifications =
    (let exact = encode_wire_core (packet_core packet); (number,position) = result;
         offset = (case position of None \<Rightarrow> 0 | Some revision \<Rightarrow> revision);
         base = ((replicate 14 [])[0 := [number,if position = None then 0 else 1,offset]])[3 := exact]
     in case response_v061_words call result of None \<Rightarrow> ([],base)
     | Some (kind,code,commit,words) \<Rightarrow> let with_words = base[1 := words] in
       case selected_mode of None \<Rightarrow> ([],with_words) | Some atomicity \<Rightarrow>
         let binding_message = response_fixed_binding_preimage exact atomicity words;
             with_binding = (with_words[2 := [atomicity]])[4 := binding_message]
         in case code_full_lookup_hash hashes binding_message of
           None \<Rightarrow> ([code_full_hash_query binding_message],with_binding)
         | Some binding \<Rightarrow> response_v061_plan_after_binding context exact atomicity words binding hashes signatures verifications
             (with_binding[5 := binding]))"

datatype response_v061_sender_stage = Response_V061_Plan | Response_V061_Prefix | Response_V061_Emit

definition response_v061_pack_rows where
  "response_v061_pack_rows rows = (0 :: integer,map (map integer_of_nat) rows)"

definition response_v061_execute_sender where
  "response_v061_execute_sender v061_stage include_original context accept_sync accept_current selected_mode observed raw hashes signatures verifications =
    (if observed = None \<and> \<not> include_original then (-1,[])
     else let (selected,original_queries) = response_v061_original_plan include_original context accept_sync accept_current
              selected_mode raw verifications
     in case selected of Inl reason \<Rightarrow>
          (case v061_stage of Response_V061_Plan \<Rightarrow> response_v061_pack_rows original_queries
           | Response_V061_Prefix \<Rightarrow> if original_queries = [] then (0,[]) else (-2,[])
           | Response_V061_Emit \<Rightarrow>
               if original_queries \<noteq> [] then (-2,[])
               else case response_v061_selected_original include_original context accept_sync accept_current selected_mode
                   (code_full_verify verifications) raw of
                 Inl strict_reason \<Rightarrow> (integer_of_nat (code_transport_refusal_number strict_reason),[])
               | Inr strict_selected \<Rightarrow> (-1,[]))
        | Inr (packet,call) \<Rightarrow> (case observed of None \<Rightarrow> (-1,[]) | Some observation \<Rightarrow>
            let result = response_v061_result observation;
                (queries,prefix) = response_v061_plan_selected context selected_mode packet call result hashes signatures verifications
            in case v061_stage of Response_V061_Plan \<Rightarrow> response_v061_pack_rows queries
             | Response_V061_Prefix \<Rightarrow> if queries = [] then response_v061_pack_rows prefix else (-2,[])
             | Response_V061_Emit \<Rightarrow>
                 if queries \<noteq> [] then (-2,[])
                 else case response_v061_selected_original include_original context accept_sync accept_current selected_mode
                     (code_full_verify verifications) raw of Inl reason \<Rightarrow>
                       (integer_of_nat (code_transport_refusal_number reason),[])
                   | Inr (actual,actual_call) \<Rightarrow> code_full_pack_sender context hashes
                     (response_v061_encode (code_full_hash hashes)
                       (\<lambda>v061_key preimage. code_full_sign signatures v061_key () preimage)
                       (code_full_verify verifications) context selected_mode (packet_core actual) actual_call result)))"

definition response_v061_sender_integer where
  "response_v061_sender_integer v061_stage include_original rows mode reply v061_present retained raw hash_rows sign_rows verify_rows =
    (case response_v061_sender_input rows mode reply v061_present retained raw hash_rows sign_rows verify_rows of None \<Rightarrow> (-1,[])
     | Some (context,accept_sync,accept_current,selected_mode,observed,original,hashes,signatures,verifications) \<Rightarrow>
       response_v061_execute_sender v061_stage include_original context accept_sync accept_current selected_mode
         observed original hashes signatures verifications)"

definition response_v061_egress_queries_flat where
  "response_v061_egress_queries_flat = response_v061_sender_integer Response_V061_Plan True"

definition response_v061_encode_boundary_queries_flat where
  "response_v061_encode_boundary_queries_flat = response_v061_sender_integer Response_V061_Plan False"

definition response_v061_egress_prefix_flat where
  "response_v061_egress_prefix_flat = response_v061_sender_integer Response_V061_Prefix True"

definition response_v061_encode_boundary_prefix_flat where
  "response_v061_encode_boundary_prefix_flat = response_v061_sender_integer Response_V061_Prefix False"

definition response_v061_egress_flat_oracle where
  "response_v061_egress_flat_oracle = response_v061_sender_integer Response_V061_Emit True"

definition response_v061_encode_boundary_flat_oracle where
  "response_v061_encode_boundary_flat_oracle = response_v061_sender_integer Response_V061_Emit False"

definition response_v061_client_input where
  "response_v061_client_input rows expected received verify_rows =
    (if \<not> code_integer_octet_values (expected @ received) then None
     else Option.bind (code_full_client_from_integer rows) (\<lambda>(channel,current).
       Option.bind (sync_decode_packet (map nat_of_integer expected)) (\<lambda>original.
         map_option (\<lambda>(hashes,signatures,verifications). (channel,current,original,map nat_of_integer received,verifications))
           (code_full_tables_from_integer [] [] verify_rows))))"

definition response_v061_client_queries where
  "response_v061_client_queries channel current expected raw verifications =
    (if response_v061_admit (code_full_probe_verify verifications) channel current expected raw \<noteq> Inl Invalid_Wire_Signature
     then [] else case sync_decode_packet raw of None \<Rightarrow> [] | Some packet \<Rightarrow>
       let core = packet_core packet in
       if wire_signature_scheme core = 2 \<or> wire_signature_scheme core \<notin> negotiated_schemes (response_channel_profile channel)
       then [] else code_full_need_verify verifications (response_client_public_key current)
         (envelope_signing_bytes core) (packet_signature packet))"

definition response_v061_admit_queries_flat where
  "response_v061_admit_queries_flat rows expected received verify_rows =
    (case response_v061_client_input rows expected received verify_rows of None \<Rightarrow> (-1,[])
     | Some (channel,current,original,raw,verifications) \<Rightarrow>
       response_v061_pack_rows (response_v061_client_queries channel current original raw verifications))"

definition response_v061_admit_flat_oracle where
  "response_v061_admit_flat_oracle rows expected received verify_rows =
    (case response_v061_client_input rows expected received verify_rows of None \<Rightarrow> (-1,[])
     | Some (channel,current,original,raw,verifications) \<Rightarrow>
       if response_v061_client_queries channel current original raw verifications \<noteq> [] then (-2,[])
       else code_full_pack_client (response_v061_admit (code_full_verify verifications) channel current original raw))"

definition response_v061_egress_and_admit_flat_oracle where
  "response_v061_egress_and_admit_flat_oracle rows mode reply v061_present retained original hash_rows sign_rows verify_rows client_rows client_verify_rows =
    (let (status,output) = response_v061_egress_flat_oracle rows mode reply v061_present retained original hash_rows sign_rows verify_rows
     in if status \<noteq> 0 then (status,output,-3,[] :: integer list)
        else let (client_status,client_output) = response_v061_admit_flat_oracle client_rows original (output ! 12) client_verify_rows
             in (status,output,client_status,client_output))"

definition response_v061_result_flat_oracle where
  "response_v061_result_flat_oracle mode reply v061_present retained =
    (if \<not> code_integer_u64_values (mode # reply @ retained) then (False,-1,False,0)
     else case response_v061_decode_observation (nat_of_integer mode) (map nat_of_integer reply) v061_present (map nat_of_integer retained) of
       None \<Rightarrow> (False,-1,False,0)
     | Some observation \<Rightarrow> let (number,position) = response_v061_result observation in
         (True,integer_of_nat number,position \<noteq> None,
           integer_of_nat (case position of None \<Rightarrow> 0 | Some revision \<Rightarrow> revision)))"

definition response_v061_identity_fields :: "string \<Rightarrow> integer list list" where
  "response_v061_identity_fields fingerprint = map (map integer_of_nat \<circ> code_json_ascii)
    [''1'',''intinf-response-full-v2'',''wire-response-sender-client-v2'',
     ''OIP_Wire_Response_Boundary.code_response_egress_flat_oracle'',''HOL-Library.Code_Target_Nat'',fingerprint]"

lemma response_v061_queries_wait_for_original_verification:
  assumes "response_v061_original_plan True context accept_sync accept_current selected_mode raw verifications = (Inl refusal,queries)"
  shows "response_v061_execute_sender Response_V061_Plan True context accept_sync accept_current selected_mode
       observed raw hashes signatures verifications = response_v061_pack_rows queries"
  using assms by (simp add: response_v061_execute_sender_def Let_def)

lemma response_v061_combined_only_uses_the_model_emitted_packet:
  assumes "response_v061_egress_flat_oracle rows mode reply v061_present retained original hash_rows sign_rows verify_rows = (0,output)"
    "response_v061_admit_flat_oracle client_rows original (output ! 12) client_verify_rows = (client_status,client_output)"
  shows "response_v061_egress_and_admit_flat_oracle rows mode reply v061_present retained original hash_rows sign_rows verify_rows
     client_rows client_verify_rows = (0,output,client_status,client_output)"
  using assms by (simp add: response_v061_egress_and_admit_flat_oracle_def)

lemma response_v061_result_flat_projects_sync_receipt_fields:
  "response_v061_result_flat_oracle 0 [3,0,0] True [3,0,0] = (True,29,True,0)"
  "response_v061_result_flat_oracle 0 [3,3] True [3,3] = (True,39,False,0)"
  "response_v061_result_flat_oracle 0 [3,4] True [3,4] = (True,40,False,0)"
  "response_v061_result_flat_oracle 0 [3,5] True [3,5] = (True,41,False,0)"
  "response_v061_result_flat_oracle 0 [3,0,0] True [3,0,1] = (True,50,False,0)"
  by (simp_all add: response_v061_result_flat_oracle_def response_v061_decode_observation_def response_v061_decode_sync_def
    code_integer_u64_values_def Let_def integer_of_nat_0 integer_of_nat_numeral)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms response_v061_queries_wait_for_original_verification
    response_v061_combined_only_uses_the_model_emitted_packet response_v061_result_flat_projects_sync_receipt_fields})
  then () else error "Unexpected oracle in the v0.6.1 full response ABI"
\<close>

code_identifier
  constant response_v061_egress_queries_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_queries_flat"
| constant response_v061_encode_boundary_queries_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_encode_boundary_queries_flat"
| constant response_v061_egress_prefix_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_prefix_flat"
| constant response_v061_encode_boundary_prefix_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_encode_boundary_prefix_flat"
| constant response_v061_egress_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_flat_oracle"
| constant response_v061_encode_boundary_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_encode_boundary_flat_oracle"
| constant response_v061_admit_queries_flat \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_admit_queries_flat"
| constant response_v061_admit_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_admit_flat_oracle"
| constant response_v061_egress_and_admit_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_egress_and_admit_flat_oracle"
| constant response_v061_result_flat_oracle \<rightharpoonup> (SML) "OIP_Wire_Response_Boundary.code_response_result_flat_oracle"

end

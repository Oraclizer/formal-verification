theory Wire_Product_Read
  imports Wire_Admission Identity_Receipts
begin

definition parse_wire_application_query where
  "parse_wire_application_query args =
    (case args of [tag, asset] \<Rightarrow> if tag = 1 then Some (Application_Value asset) else None
     | [tag, domain, item] \<Rightarrow>
        if tag = 2 then Some (Source_Balance (domain,item))
        else if tag = 5 then Some (Regulatory_State domain item)
        else if tag = 6 then Some (Terminal_Receipt (domain,item)) else None
     | [tag, domain, asset, holder] \<Rightarrow>
        if tag = 3 then Some (Destination_Balance (domain,asset,holder)) else None
     | [tag, source, event, destination, asset, holder] \<Rightarrow>
        if tag = 4 then Some (Root_Balance (source,event) (destination,asset,holder)) else None
     | _ \<Rightarrow> None)"

datatype parsed_wire_query =
    Wire_Read_Request session_proof identity_read_request
  | Wire_Cache_Request session_proof application_query

datatype 'token wire_read_invocation =
    Invoke_Authenticated_Read 'token session_proof nat identity_read_request
  | Invoke_Authenticated_Capture 'token session_proof nat application_query

definition decode_wire_query_body where
  "decode_wire_query_body core =
    (let body = wire_operation_body core; op = wire_opcode body; expected_epoch = wire_authority_epoch core in
      if wire_message_family core \<noteq> Wire_Query \<or> wire_blobs body \<noteq> [] then None else
      case wire_words body of [] \<Rightarrow> None
       | session # args \<Rightarrow>
          let proof = \<lparr>proof_session = session, proof_epoch = expected_epoch\<rparr> in
          if op \<in> {1,2} then
            (case args of [] \<Rightarrow> None | revision # query \<Rightarrow> map_option
               (\<lambda>q. Wire_Read_Request proof
                 (if op = 1 then Current_Data q \<lparr>cut_authority_epoch = expected_epoch, cut_revision = revision\<rparr>
                  else Historical_Data q revision)) (parse_wire_application_query query))
          else if op = 3 then map_option (\<lambda>q. Wire_Read_Request proof (Raw_Data q)) (parse_wire_application_query args)
          else if op = 4 then
            (case args of [domain,event] \<Rightarrow> Some (Wire_Read_Request proof (Operation_Status (domain,event))) | _ \<Rightarrow> None)
          else if op = 5 then (if args = [] then Some (Wire_Read_Request proof Authority_Journal) else None)
          else if op = 6 then map_option (Wire_Cache_Request proof) (parse_wire_application_query args)
          else if op = 7 then (case args of [asset] \<Rightarrow> Some (Wire_Read_Request proof (Owner_Data asset)) | _ \<Rightarrow> None)
          else None)"

definition decoded_wire_read_action where
  "decoded_wire_read_action token core =
    (case decode_wire_query_body core of None \<Rightarrow> None
     | Some (Wire_Read_Request proof request) \<Rightarrow>
         Some (Invoke_Authenticated_Read token proof (wire_target_domain core) request)
     | Some (Wire_Cache_Request proof query) \<Rightarrow>
         Some (Invoke_Authenticated_Capture token proof (wire_target_domain core) query))"

lemma an_encoded_current_query_supplies_the_actual_session_cut_and_asset:
  assumes "wire_message_family core = Wire_Query"
    "wire_opcode (wire_operation_body core) = 1"
    "wire_words (wire_operation_body core) = [session,revision,1,asset]"
    "wire_blobs (wire_operation_body core) = []"
  shows "decoded_wire_read_action token core =
    Some (Invoke_Authenticated_Read token \<lparr>proof_session = session, proof_epoch = wire_authority_epoch core\<rparr>
      (wire_target_domain core) (Current_Data (Application_Value asset)
        \<lparr>cut_authority_epoch = wire_authority_epoch core, cut_revision = revision\<rparr>))"
  using assms by (simp add: decoded_wire_read_action_def decode_wire_query_body_def parse_wire_application_query_def Let_def)

datatype wire_read_result = Wire_Data_Reply identity_read_reply | Wire_Cache_Reply "product_cache_entry option"

context source_attestation
begin

fun consume_wire_read_invocation where
  "consume_wire_read_invocation directory policy authenticate verify_read (Invoke_Authenticated_Read token proof target request) s =
    Wire_Data_Reply (read_at_identity_endpoint directory policy authenticate verify_read token proof target request s)"
| "consume_wire_read_invocation directory policy authenticate verify_read (Invoke_Authenticated_Capture token proof target query) s =
    (let reads = regulated_read_world s;
         empty_cache = replace_regulated_reads (reads\<lparr>query_cache := (\<lambda>_. None)\<rparr>) s
      in Wire_Cache_Reply (query_cache (regulated_read_world
          (capture_at_identity_endpoint directory policy authenticate verify_read token proof target query empty_cache)) query))"

definition service_action_from_wire where
  "service_action_from_wire verify attest body_allowed authority decode bytes =
    (case wire_gate verify attest body_allowed authority bytes of
       Gate_Admitted packet \<Rightarrow> decode (packet_core packet)
     | Gate_Refused reason \<Rightarrow> None)"

lemma admitted_canonical_bytes_are_the_only_input_to_the_selected_product_service:
  assumes "service_action_from_wire verify attest body_allowed authority decode bytes = Some action"
  obtains packet where "decode_wire_packet bytes = Some packet"
    "encode_wire_packet packet = bytes" "decode (packet_core packet) = Some action"
    "current_wire_scope authority (packet_core packet)"
proof -
  obtain packet where admitted: "wire_gate verify attest body_allowed authority bytes = Gate_Admitted packet"
    "decode (packet_core packet) = Some action"
    using assms by (cases "wire_gate verify attest body_allowed authority bytes")
      (auto simp: service_action_from_wire_def)
  have gate: "decode_wire_packet bytes = Some packet" "current_wire_scope authority (packet_core packet)"
    using a_wire_admission_uses_the_exact_current_domain_key_epoch_and_signature[OF admitted(1)] by blast+
  have bytes: "encode_wire_packet packet = bytes"
    using every_accepted_wire_message_has_exactly_the_received_bytes[OF gate(1)] by blast
  show thesis by (rule that[OF gate(1) bytes admitted(2) gate(2)])
qed

end

end

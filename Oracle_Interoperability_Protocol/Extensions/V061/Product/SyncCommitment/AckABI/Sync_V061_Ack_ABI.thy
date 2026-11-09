theory Sync_V061_Ack_ABI
  imports "OIP_Sync_V061_Position_Ack.Sync_V061_Ack_Link_Draft"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen"
begin

type_synonym sync_ack_abi_result = "nat list \<times> wire_bytes list"

definition sync_ack_abi_refusal :: "wire_refusal \<Rightarrow> sync_ack_abi_result" where
  "sync_ack_abi_refusal reason = ([0,code_transport_refusal_number reason],[])"

definition sync_ack_abi_view :: "sync_link_ack \<Rightarrow> sync_ack_abi_result" where
  "sync_ack_abi_view ack =
    (let (namespace,sequence) = sync_link_id ack;
         commit = (case sync_link_commit ack of None \<Rightarrow> [0,0] | Some position \<Rightarrow> [1,position])
     in ([1,namespace,sequence,reference_response_kind_number (sync_link_kind ack),sync_link_code ack] @ commit,
         [sync_link_exact_original ack]))"

definition sync_ack_abi_signed :: "sync_link_ack \<Rightarrow> code_response_status \<Rightarrow> sync_ack_abi_result" where
  "sync_ack_abi_signed ack status =
    (let (words,blobs) = sync_ack_abi_view ack;
         classification = (case status of Code_Known_Response _ _ \<Rightarrow> 1 | Code_Unknown_Response _ _ \<Rightarrow> 2)
     in (words @ [classification],blobs))"

definition sync_ack_abi_raw where
  "sync_ack_abi_raw scope fuel raw =
    (if length raw > boundary_max_frame scope then sync_ack_abi_refusal Invalid_Wire_Format
     else case sync_decode_packet raw of None \<Rightarrow> sync_ack_abi_refusal Invalid_Wire_Format
       | Some packet \<Rightarrow> case sync_link_parse_ack True fuel (packet_core packet) of
           Inl reason \<Rightarrow> sync_ack_abi_refusal reason | Inr ack \<Rightarrow> sync_ack_abi_view ack)"

definition sync_ack_abi_run where
  "sync_ack_abi_run channel scope verify input =
    (case input of (fuel,key,raw,expected) \<Rightarrow>
     let current = \<lparr>response_client_scope = scope, response_client_public_key = key, response_client_max_nesting = fuel\<rparr>;
         signed = (if length expected > boundary_max_frame scope then sync_ack_abi_refusal Invalid_Wire_Format
            else case sync_decode_packet expected of None \<Rightarrow> sync_ack_abi_refusal Invalid_Wire_Format
              | Some packet \<Rightarrow> case sync_link_admit_signed verify channel current (packet_core packet) raw of
                  Inl reason \<Rightarrow> sync_ack_abi_refusal reason | Inr (ack,status) \<Rightarrow> sync_ack_abi_signed ack status)
     in (sync_ack_abi_raw scope fuel raw,signed))"

definition sync_ack_integer_trace where
  "sync_ack_integer_trace config families atomicities schemes local_key remote_key verification inputs =
    (let n = nat_of_integer; ns = map n;
         facts = map (\<lambda>(key,data,signature). (ns key,ns data,ns signature)) verification;
         verify = (\<lambda>key data signature. (key,data,signature) \<in> set facts);
         output = (\<lambda>(words,blobs). (map integer_of_nat words,map (map integer_of_nat) blobs))
     in case ns config of [cfg_wire_version,cfg_deployment,cfg_local,cfg_remote,cfg_expires,cfg_principal,cfg_key,cfg_epoch,
       cfg_route,cfg_now,cfg_ttl,cfg_skew,cfg_frame,cfg_floor,cfg_critical] \<Rightarrow>
       let profile = \<lparr>negotiated_version = cfg_wire_version, negotiated_families = code_numeric_family_set (ns families),
             negotiated_atomicities = set (ns atomicities), negotiated_schemes = set (ns schemes)\<rparr>;
           channel = \<lparr>response_channel_profile = profile, response_channel_deployment = cfg_deployment,
             response_channel_local = cfg_local, response_channel_remote = cfg_remote, response_channel_expires = cfg_expires,
             response_channel_local_key = ns local_key, response_channel_remote_key = ns remote_key\<rparr>;
           scope = \<lparr>boundary_profile = profile, boundary_deployment = cfg_deployment, boundary_source = cfg_remote,
             boundary_target = cfg_local, boundary_principal = cfg_principal, boundary_key = cfg_key, boundary_epoch = cfg_epoch,
             boundary_route_scope = cfg_route, boundary_now = cfg_now, boundary_asset_ttl_floor = cfg_ttl, boundary_future_skew = cfg_skew,
             boundary_max_frame = cfg_frame, boundary_version_floor = cfg_floor, boundary_critical_allowed = (cfg_critical = 1),
             boundary_threshold_supported = False\<rparr>;
           steps = map (\<lambda>(fuel,boundary_key,raw,expected). (n fuel,ns boundary_key,ns raw,ns expected)) inputs
       in Some (map (\<lambda>input. case sync_ack_abi_run channel scope verify input of (raw,signed) \<Rightarrow>
              (output raw,output signed)) steps)
      | _ \<Rightarrow> None)"

export_code sync_ack_integer_trace
  in SML module_name OIP_Sync_Ack_ABI file_prefix "oip_sync_ack_abi"

end

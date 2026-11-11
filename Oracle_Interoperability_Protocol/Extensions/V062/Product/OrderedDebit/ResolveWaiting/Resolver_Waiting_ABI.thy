theory Resolver_Waiting_ABI
  imports Resolver_Waiting_Link
begin

fun rdw_make_profile :: "nat list \<Rightarrow> recovery_profile option" where
  "rdw_make_profile [rdw_deploy,rdw_format,rdw_profile] =
    Some \<lparr>recovery_deployment = rdw_deploy,recovery_format = rdw_format,recovery_authority_profile = rdw_profile\<rparr>"
| "rdw_make_profile _ = None"

fun rdw_make_address :: "nat list \<Rightarrow> wire_bytes \<Rightarrow> rdw_address option" where
  "rdw_make_address [rdw_deploy,rdw_format,rdw_profile,rdw_sequence,rdw_offset,rdw_count] rdw_digest =
    (if length rdw_digest = 32 then
      map_option (\<lambda>rdw_p. \<lparr>rdw_address_profile = rdw_p,rdw_address_sequence = rdw_sequence,
        rdw_address_offset = rdw_offset,rdw_address_length = rdw_count,rdw_address_hash = rdw_digest\<rparr>)
        (rdw_make_profile [rdw_deploy,rdw_format,rdw_profile])
     else None)"
| "rdw_make_address _ _ = None"

fun rdw_parse_fields :: "nat list list \<Rightarrow> rdw_header option" where
  "rdw_parse_fields [[rdw_deploy,rdw_format,rdw_profile,rdw_sequence,rdw_token],rdw_parent_fields,rdw_parent_hash] =
    (if rdw_token \<noteq> 0 then None else
      Option.bind (rdw_make_profile [rdw_deploy,rdw_format,rdw_profile]) (\<lambda>rdw_p.
       if rdw_parent_fields = [] \<and> rdw_parent_hash = [] then
         Some \<lparr>rdw_header_profile = rdw_p,rdw_header_sequence = rdw_sequence,rdw_header_parent = None\<rparr>
       else map_option (\<lambda>rdw_parent.
         \<lparr>rdw_header_profile = rdw_p,rdw_header_sequence = rdw_sequence,rdw_header_parent = Some rdw_parent\<rparr>)
         (rdw_make_address rdw_parent_fields rdw_parent_hash)))"
| "rdw_parse_fields _ = None"

definition rdw_address_words where
  "rdw_address_words rdw_addr =
    (let rdw_p = rdw_address_profile rdw_addr in
      [recovery_deployment rdw_p,recovery_format rdw_p,recovery_authority_profile rdw_p,
       rdw_address_sequence rdw_addr,rdw_address_offset rdw_addr,rdw_address_length rdw_addr])"

fun rdw_collect :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "rdw_collect rdw_f [] = Some []"
| "rdw_collect rdw_f (rdw_x # rdw_xs) =
     Option.bind (rdw_f rdw_x) (\<lambda>rdw_y. map_option (Cons rdw_y) (rdw_collect rdw_f rdw_xs))"

fun rdw_id :: "nat list \<Rightarrow> client_call_id option" where
  "rdw_id [rdw_ns,rdw_sequence] = Some (rdw_ns,rdw_sequence)"
| "rdw_id _ = None"

fun rdw_work :: "nat list \<Rightarrow> (source_key \<times> nat) option" where
  "rdw_work [rdw_domain_word,rdw_event,rdw_g] = Some ((rdw_domain_word,rdw_event),rdw_g)"
| "rdw_work _ = None"

fun rdw_parse_transport :: "nat list list \<Rightarrow> authenticated_message_id option" where
  "rdw_parse_transport [[rdw_dep,rdw_src,rdw_p],rdw_uuid] =
     (if length rdw_uuid = 16 then Some (rdw_dep,rdw_src,rdw_p,rdw_uuid) else None)"
| "rdw_parse_transport _ = None"

fun rdw_parse_transport_binding where
  "rdw_parse_transport_binding [rdw_key,rdw_uuid,rdw_raw] =
     map_option (\<lambda>rdw_id_key. (rdw_id_key,rdw_raw)) (rdw_parse_transport [rdw_key,rdw_uuid])"
| "rdw_parse_transport_binding _ = None"

fun rdw_parse_disposition :: "nat list \<Rightarrow> reference_disposition option" where
  "rdw_parse_disposition [rdw_tag] =
    (if rdw_tag = 1 then Some Ref_Pending
     else if rdw_tag = 2 then Some Ref_Applied
     else if rdw_tag = 3 then Some Ref_Explicit_Rejection
     else if rdw_tag = 4 then Some Ref_Retained_Refusal
     else None)"
| "rdw_parse_disposition _ = None"

fun rdw_parse_decision where
  "rdw_parse_decision [rdw_key,rdw_call,rdw_work_fields,rdw_status,rdw_bytes] =
     (case (rdw_id rdw_key,rdw_id rdw_call,rdw_work rdw_work_fields,rdw_parse_disposition rdw_status) of
       (Some rdw_k,Some rdw_i,Some (rdw_o,rdw_gen),Some rdw_d) \<Rightarrow>
         Some (rdw_k,(\<lparr>source_debit_id = rdw_i,source_debit_origin = rdw_o,
            source_debit_generation = rdw_gen,source_debit_packet = rdw_bytes\<rparr>,rdw_d))
      | _ \<Rightarrow> None)"
| "rdw_parse_decision _ = None"

fun rdw_parse_latest where
  "rdw_parse_latest [rdw_work_fields,rdw_call] =
     (case (rdw_work rdw_work_fields,rdw_id rdw_call) of
       (Some rdw_w,Some rdw_i) \<Rightarrow> Some (rdw_w,rdw_i) | _ \<Rightarrow> None)"
| "rdw_parse_latest _ = None"

fun rdw_parse_cut where
  "rdw_parse_cut [rdw_ce,rdw_cr] = Some \<lparr>cut_authority_epoch = rdw_ce,cut_revision = rdw_cr\<rparr>"
| "rdw_parse_cut _ = None"

fun rdw_parse_versions :: "nat list \<Rightarrow> (nat \<times> nat) list option" where
  "rdw_parse_versions [] = Some []"
| "rdw_parse_versions (rdw_asset # rdw_v # rdw_rest) =
     map_option (Cons (rdw_asset,rdw_v)) (rdw_parse_versions rdw_rest)"
| "rdw_parse_versions _ = None"

fun rdw_parse_binding where
  "rdw_parse_binding [rdw_dom,rdw_event,rdw_asset,rdw_owner,rdw_dst,rdw_recipient,rdw_amount] =
     Some \<lparr>source_binding_origin = (rdw_dom,rdw_event),source_binding_asset = rdw_asset,
       source_binding_owner = rdw_owner,source_binding_destination = rdw_dst,
       source_binding_recipient = rdw_recipient,source_binding_amount = rdw_amount\<rparr>"
| "rdw_parse_binding _ = None"

fun rdw_parse_credential where
  "rdw_parse_credential [] = Some None"
| "rdw_parse_credential [rdw_asset,rdw_dom,rdw_event,rdw_owner,rdw_g,rdw_e] =
     Some (Some \<lparr>credential_token = \<lparr>token_asset = rdw_asset,token_owner = rdw_owner,token_generation = rdw_g\<rparr>,
        credential_epoch = rdw_e,credential_origin = (rdw_dom,rdw_event)\<rparr>)"
| "rdw_parse_credential _ = None"

definition rdw_parse_saved_command :: "nat \<Rightarrow> nat \<Rightarrow> ordinary_wire_command option" where
  "rdw_parse_saved_command rdw_tag rdw_arg =
    (if rdw_tag = 1 then Some (Wire_Reserve rdw_arg)
     else if rdw_tag = 2 then Some (Wire_Dispatch rdw_arg) else None)"

fun rdw_parse_saved_outcome :: "nat list \<Rightarrow> code_source_outcome option" where
  "rdw_parse_saved_outcome [rdw_tag,rdw_position] =
    (if rdw_tag = 1 then Some \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Reserved_Reply,
         source_outcome_commit = Some rdw_position\<rparr>
     else if rdw_tag = 2 then Some \<lparr>source_outcome_reply = Code_Source_Accepted Code_Source_Dispatched_Reply,
         source_outcome_commit = Some rdw_position\<rparr>
     else None)"
| "rdw_parse_saved_outcome _ = None"

fun rdw_parse_saved where
  "rdw_parse_saved [rdw_key,[rdw_msg,rdw_oe,rdw_endpoint,rdw_caller,rdw_s,rdw_ce,rdw_cr,rdw_cmd,rdw_arg],
     rdw_binding_words,rdw_credential_words,rdw_version_words,rdw_outcome_words] =
     (case (rdw_id rdw_key,rdw_parse_cut [rdw_ce,rdw_cr],rdw_parse_saved_command rdw_cmd rdw_arg,
           rdw_parse_binding rdw_binding_words,rdw_parse_credential rdw_credential_words,
           rdw_parse_versions rdw_version_words,rdw_parse_saved_outcome rdw_outcome_words) of
       (Some rdw_i,Some rdw_product_cut,Some rdw_command,Some rdw_binding,Some rdw_cred,Some rdw_versions,Some rdw_outcome) \<Rightarrow>
         Some (rdw_i,(\<lparr>source_payload_message = rdw_msg,source_payload_origin_epoch = rdw_oe,
           source_payload_endpoint = rdw_endpoint,source_payload_caller = rdw_caller,source_payload_session = rdw_s,
           source_payload_cut = rdw_product_cut,source_payload_binding = rdw_binding,source_payload_credential = rdw_cred,
           source_payload_versions = rdw_versions,source_payload_command = rdw_command\<rparr>,rdw_outcome))
      | _ \<Rightarrow> None)"
| "rdw_parse_saved _ = None"

fun rdw_parse_identity where
  "rdw_parse_identity [rdw_pr,rdw_do,rdw_oc,rdw_ra] =
     Some \<lparr>identity_principal = rdw_pr,identity_domain = rdw_do,identity_ocid = rdw_oc,identity_rai = rdw_ra\<rparr>"
| "rdw_parse_identity _ = None"

fun rdw_parse_execute where
  "rdw_parse_execute [] = Some None"
| "rdw_parse_execute (rdw_one # rdw_rest) = map_option Some (rdw_parse_identity (rdw_one # rdw_rest))"

fun rdw_parse_auth where
  "rdw_parse_auth [[rdw_s,rdw_e,rdw_dep,rdw_src,rdw_dst,rdw_pr,rdw_clock,rdw_host,rdw_limit],
     rdw_receipt_words,rdw_execute_words,rdw_key] =
     (case (rdw_parse_identity rdw_receipt_words,rdw_parse_execute rdw_execute_words) of
       (Some rdw_ri,Some rdw_ei) \<Rightarrow> Some \<lparr>rdw_receipt_identity = rdw_ri,rdw_execute_identity = rdw_ei,
         rdw_session = rdw_s,rdw_epoch = rdw_e,rdw_deployment = rdw_dep,rdw_domain = rdw_src,rdw_target = rdw_dst,
         rdw_principal = rdw_pr,rdw_signed_clock = rdw_clock,rdw_host_clock = rdw_host,rdw_frame_limit = rdw_limit,
         rdw_public_key = rdw_key\<rparr>
      | _ \<Rightarrow> None)"
| "rdw_parse_auth _ = None"

fun rdw_parse_wire where
  "rdw_parse_wire [rdw_pkt,rdw_core,rdw_psha,rdw_csha,rdw_msg,rdw_sig] =
     Some \<lparr>rdw_packet_bytes = rdw_pkt,rdw_core_bytes = rdw_core,rdw_packet_sha = rdw_psha,
       rdw_core_sha = rdw_csha,rdw_preimage = rdw_msg,rdw_signature = rdw_sig\<rparr>"
| "rdw_parse_wire _ = None"

fun rdw_parse_hash where
  "rdw_parse_hash [rdw_raw,rdw_sha] = (if length rdw_sha = 32 then Some (rdw_raw,rdw_sha) else None)"
| "rdw_parse_hash _ = None"

fun rdw_parse_close :: "nat list \<Rightarrow> bool option option" where
  "rdw_parse_close [] = Some None"
| "rdw_parse_close [rdw_tag] =
     (if rdw_tag = 0 then Some (Some False) else if rdw_tag = 1 then Some (Some True) else None)"
| "rdw_parse_close _ = None"

fun rdw_disposition_words :: "(code_source_wire_error + reference_disposition option) \<Rightarrow> nat" where
  "rdw_disposition_words (Inr None) = 0"
| "rdw_disposition_words (Inr (Some Ref_Pending)) = 1"
| "rdw_disposition_words (Inr (Some Ref_Applied)) = 2"
| "rdw_disposition_words (Inr (Some Ref_Explicit_Rejection)) = 3"
| "rdw_disposition_words (Inr (Some Ref_Retained_Refusal)) = 4"
| "rdw_disposition_words (Inl rdw_error) = 5"

fun rdw_receipt_word :: "code_source_receipt option \<Rightarrow> nat" where
  "rdw_receipt_word (Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting)) = 1"
| "rdw_receipt_word (Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Rejected)) = 2"
| "rdw_receipt_word (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected rdw_result))) = 3"
| "rdw_receipt_word _ = 0"

fun rdw_arrival_word :: "code_arrival \<Rightarrow> nat" where
  "rdw_arrival_word Code_First = 1"
| "rdw_arrival_word Code_Identical = 2"
| "rdw_arrival_word Code_Replay_Conflict = 3"

definition rdw_request_words where
  "rdw_request_words rdw_request =
    (let rdw_call = source_debit_id rdw_request; rdw_o = source_debit_origin rdw_request in
      [fst rdw_call,snd rdw_call,fst rdw_o,snd rdw_o,source_debit_generation rdw_request])"

fun rdw_tail_words where
  "rdw_tail_words (Code_Source_Resolved Code_Source_Resolution_Unresolved,rdw_attempt) =
      [1,0] @ (case rdw_attempt of None \<Rightarrow> [] | Some rdw_request \<Rightarrow> rdw_request_words rdw_request)"
| "rdw_tail_words (Code_Source_Resolved Code_Source_Resolution_Rejected,rdw_attempt) =
      [2,0] @ (case rdw_attempt of None \<Rightarrow> [] | Some rdw_request \<Rightarrow> rdw_request_words rdw_request)"
| "rdw_tail_words (Code_Source_Resolved (Code_Source_Resolution_Published rdw_result),rdw_attempt) =
      [3,0] @ (case rdw_attempt of None \<Rightarrow> [] | Some rdw_request \<Rightarrow> rdw_request_words rdw_request)"
| "rdw_tail_words (Code_Source_Resolve_Error rdw_error,rdw_attempt) =
      [if rdw_error = Code_Source_Wire_Recovery Code_Source_Recovery_Hold then 5 else 4,code_source_error_number rdw_error]
      @ (case rdw_attempt of None \<Rightarrow> [] | Some rdw_request \<Rightarrow> rdw_request_words rdw_request)"

definition rdw_cut_words where
  "rdw_cut_words rdw_product_cut = [cut_authority_epoch rdw_product_cut,cut_revision rdw_product_cut]"

definition rdw_binding_words where
  "rdw_binding_words rdw_b = [fst (source_binding_origin rdw_b),snd (source_binding_origin rdw_b),source_binding_asset rdw_b,
    source_binding_owner rdw_b,source_binding_destination rdw_b,source_binding_recipient rdw_b,source_binding_amount rdw_b]"

fun rdw_credential_words where
  "rdw_credential_words None = []"
| "rdw_credential_words (Some rdw_cred) =
     (let rdw_t = credential_token rdw_cred; rdw_o = credential_origin rdw_cred in
       [token_asset rdw_t,fst rdw_o,snd rdw_o,token_owner rdw_t,token_generation rdw_t,credential_epoch rdw_cred])"

definition rdw_payload_rows where
  "rdw_payload_rows rdw_payload =
    [[source_payload_message rdw_payload,source_payload_origin_epoch rdw_payload,source_payload_endpoint rdw_payload,
      source_payload_caller rdw_payload,source_payload_session rdw_payload] @ rdw_cut_words (source_payload_cut rdw_payload),
     rdw_binding_words (source_payload_binding rdw_payload),
     rdw_credential_words (source_payload_credential rdw_payload),
     concat (map (\<lambda>(rdw_a,rdw_v). [rdw_a,rdw_v]) (source_payload_versions rdw_payload))]"

definition rdw_run_case where
  "rdw_run_case rdw_hash rdw_crypto rdw_snapshot rdw_wire rdw_auth rdw_close =
    (if \<not> rdw_selected_ok rdw_hash rdw_snapshot then [[0]]
     else case decode_wire_packet (rdw_packet_bytes rdw_wire) of None \<Rightarrow> [[1]]
       | Some rdw_packet \<Rightarrow> (case rdw_decode_original rdw_packet rdw_wire of None \<Rightarrow> [[1]]
         | Some (rdw_request,rdw_payload) \<Rightarrow>
           if \<not> rdw_wire_admitted rdw_hash rdw_crypto rdw_snapshot rdw_packet rdw_wire rdw_auth rdw_payload then [[2]]
           else let rdw_obs = rdw_observation rdw_snapshot;
                    rdw_core = packet_core rdw_packet;
                    rdw_key = authenticated_wire_message_id rdw_core;
                    rdw_disp = code_source_resolution_disposition rdw_obs rdw_request;
                    rdw_retained = rdw_receipt rdw_snapshot (source_debit_id rdw_request) rdw_payload;
                    rdw_arrival = code_compare_binding (map_of (rdw_transport_bindings rdw_snapshot) rdw_key) (encode_wire_core rdw_core);
                    rdw_base = [[3,rdw_disposition_words rdw_disp,rdw_receipt_word rdw_retained,rdw_arrival_word rdw_arrival],
                      [fst (source_control_stored rdw_obs)],rdw_address_words (rdw_head rdw_snapshot),
                      rdw_request_words rdw_request,
                      [wire_deployment rdw_core,wire_source_domain rdw_core,wire_principal rdw_core],wire_uuid rdw_core,
                      [rdw_host_clock rdw_auth,wire_sent_seconds rdw_core],rdw_cut_words (rdw_cut rdw_snapshot)]
                      @ rdw_payload_rows rdw_payload
                in case rdw_close of None \<Rightarrow> rdw_base
                 | Some rdw_wants_close \<Rightarrow>
                     if rdw_wants_close \<and> rdw_disp = Inr None then [[2]]
                     else rdw_base @ concat (map (\<lambda>rdw_current.
                       map (\<lambda>rdw_replace. rdw_tail_words
                         (rdw_tail rdw_snapshot rdw_packet rdw_request rdw_payload rdw_auth
                            rdw_wants_close rdw_current rdw_replace))
                         [None,Some False,Some True]) [None,Some (source_control_stored rdw_obs)])))"

definition rdw_nat_abi :: "nat list list list list \<Rightarrow> nat list list" where
  "rdw_nat_abi rdw_input =
    (case rdw_input of
       [[[rdw_control_raw,rdw_control_canon,rdw_control_digest,rdw_raw_record,rdw_record_canon]],
        [[[rdw_mod,rdw_writer,rdw_expected,rdw_size],rdw_profile,rdw_address,rdw_head_digest,
         rdw_header,rdw_parent,rdw_parent_digest,rdw_selected_cut]],
        [[rdw_revoked,rdw_close_words]],rdw_cancelled,rdw_decisions,rdw_latest,rdw_calls,
        rdw_transport,[rdw_wire_rows],[rdw_auth_rows],rdw_hash_rows,rdw_crypto_facts,[rdw_claimed]] \<Rightarrow>
        (case (rdw_make_profile rdw_profile,rdw_make_address rdw_address rdw_head_digest,
           rdw_parse_fields [rdw_header,rdw_parent,rdw_parent_digest],rdw_parse_cut rdw_selected_cut,rdw_parse_close rdw_close_words,
           rdw_collect rdw_parse_transport rdw_cancelled,rdw_collect rdw_parse_decision rdw_decisions,
           rdw_collect rdw_parse_latest rdw_latest,rdw_collect rdw_parse_saved rdw_calls,
           rdw_collect rdw_parse_transport_binding rdw_transport,rdw_parse_wire rdw_wire_rows,rdw_parse_auth rdw_auth_rows,
           rdw_collect rdw_parse_hash rdw_hash_rows,rdw_collect rdw_id rdw_claimed) of
           (Some rdw_cfg,Some rdw_hd,Some rdw_hdr,Some rdw_product_cut,Some rdw_close_arg,Some rdw_cancels,Some rdw_decs,
            Some rdw_latest_ids,Some rdw_retained,Some rdw_seen,Some rdw_wire,Some rdw_auth,Some rdw_hashes,Some rdw_claims) \<Rightarrow>
           let rdw_obs = \<lparr>source_control_stored = (rdw_mod,rdw_control_raw),source_control_revoked = rdw_revoked,
             source_control_cancelled = rdw_cancels,source_control_decisions = rdw_decs,source_control_latest = rdw_latest_ids\<rparr>;
               rdw_snapshot = \<lparr>rdw_observation = rdw_obs,rdw_head = rdw_hd,rdw_control_profile = rdw_cfg,
             rdw_control_writer = rdw_writer,rdw_expected_writer = rdw_expected,rdw_control_canonical = rdw_control_canon,
             rdw_control_sha = rdw_control_digest,rdw_file_size = rdw_size,rdw_record_bytes = rdw_raw_record,
             rdw_record_canonical = rdw_record_canon,rdw_record_header = rdw_hdr,rdw_cut = rdw_product_cut,
             rdw_ordinary_calls = rdw_retained,rdw_transport_bindings = rdw_seen,rdw_other_claims = rdw_claims\<rparr>
           in rdw_run_case (map_of rdw_hashes) (\<lambda>rdw_k rdw_msg rdw_s. List.member rdw_crypto_facts [rdw_k,rdw_msg,rdw_s])
             rdw_snapshot rdw_wire rdw_auth rdw_close_arg
         | _ \<Rightarrow> [[0]])
     | _ \<Rightarrow> [[0]])"

definition rdw_integer_abi :: "integer list list list list \<Rightarrow> integer list list" where
  "rdw_integer_abi rdw_input =
     (if list_all (list_all (list_all (list_all (\<lambda>rdw_i. 0 \<le> rdw_i \<and> rdw_i < 18446744073709551616)))) rdw_input
      then map (map integer_of_nat) (rdw_nat_abi (map (map (map (map nat_of_integer))) rdw_input))
      else [[0]])"

export_code rdw_integer_abi in SML
  module_name OIP_Resolver_Waiting_ABI file_prefix "oip_resolver_waiting_abi"

end

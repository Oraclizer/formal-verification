theory Resolver_Unseen_Close_Link
  imports "OIP_Resolver_Waiting_Model_Link.Resolver_Waiting_ABI"
begin

text \<open>Unseen close uses the same exact original, ordered observation and
  ordinary receipt lookup as the Waiting resolver. The additional input is
  the typed reservation map projected from the exact selected record.
  The adapter supplies canonical JSON interpretation. The model checks the
  actual reservation slice, selects the row by decoded origin, and computes
  the credential gate. The replacement result is a separate condition.\<close>

type_synonym unseen_reservations = "(source_key \<times> code_source_receipt_reservation) list"

fun unseen_reservation_slice :: "nat list list \<Rightarrow> wire_bytes \<Rightarrow> bool" where
  "unseen_reservation_slice [[unseen_offset],unseen_raw] unseen_record =
    (unseen_raw \<noteq> [] \<and> unseen_offset + length unseen_raw \<le> length unseen_record \<and>
     take (length unseen_raw) (drop unseen_offset unseen_record) = unseen_raw)"
| "unseen_reservation_slice _ _ = False"

lemma unseen_projection_uses_the_exact_reservation_slice:
  assumes "unseen_reservation_slice [[unseen_offset],unseen_raw] unseen_record"
  shows "unseen_offset + length unseen_raw \<le> length unseen_record"
    "take (length unseen_raw) (drop unseen_offset unseen_record) = unseen_raw"
  using assms by simp_all

fun unseen_parse_reservation :: "nat list list \<Rightarrow> (source_key \<times> code_source_receipt_reservation) option" where
  "unseen_parse_reservation [[unseen_domain,unseen_event],unseen_binding_words,
     [unseen_holder,unseen_generation,unseen_deadline,unseen_active],unseen_version_words] =
    (case (rdw_parse_binding unseen_binding_words,rdw_parse_versions unseen_version_words) of
       (Some unseen_b,Some unseen_vs) \<Rightarrow>
         if source_binding_origin unseen_b = (unseen_domain,unseen_event) \<and> unseen_active \<le> 1
         then Some ((unseen_domain,unseen_event),\<lparr>source_reservation_binding = unseen_b,
           source_reservation_holder = unseen_holder,source_reservation_generation = unseen_generation,
           source_reservation_deadline = unseen_deadline,source_reservation_active = (unseen_active = 1),
           source_reservation_versions = unseen_vs\<rparr>)
         else None
     | _ \<Rightarrow> None)"
| "unseen_parse_reservation _ = None"

definition unseen_resolve_tail where
  "unseen_resolve_tail unseen_snapshot unseen_packet unseen_request unseen_payload unseen_auth
     unseen_rows unseen_current unseen_replacement =
    (let unseen_core = packet_core unseen_packet;
         unseen_key = authenticated_wire_message_id unseen_core;
         unseen_stored = map_of unseen_rows (source_debit_origin unseen_request)
     in code_source_resolve_debit_tail (rdw_observation unseen_snapshot) unseen_request unseen_key (encode_wire_core unseen_core)
       (map_of (rdw_transport_bindings unseen_snapshot) unseen_key)
       (rdw_receipt unseen_snapshot (source_debit_id unseen_request) unseen_payload) True
       (rdw_execute_identity unseen_auth) (identity_principal (rdw_receipt_identity unseen_auth)) (rdw_epoch unseen_auth)
       unseen_payload unseen_stored unseen_current unseen_replacement)"

lemma unseen_close_refuses_a_missing_or_mismatched_credential:
  assumes unseen_absent: "code_source_resolution_disposition unseen_observed unseen_request = Inr None"
    and unseen_bad: "\<not> code_source_debit_receipt_credential unseen_actor unseen_epoch unseen_payload unseen_stored"
  shows "code_source_close_resolution unseen_observed unseen_request unseen_execute
       (code_source_debit_receipt_credential unseen_actor unseen_epoch unseen_payload unseen_stored) unseen_replacement =
     (Code_Source_Resolve_Error Code_Source_Wire_Product_Rejected,None)"
  using assms by (simp add: code_source_close_resolution_def)

lemma unseen_close_with_exact_credential_and_no_latest_only_succeeds_after_replacement:
  assumes unseen_absent: "code_source_resolution_disposition unseen_observed unseen_request = Inr None"
    and unseen_work: "map_of (source_control_latest unseen_observed) (code_source_debit_work unseen_request) = None"
    and unseen_exec: "unseen_execute \<noteq> None"
    and unseen_credential: "code_source_debit_receipt_credential unseen_actor unseen_epoch unseen_payload unseen_stored"
  shows "code_source_close_resolution unseen_observed unseen_request unseen_execute
       (code_source_debit_receipt_credential unseen_actor unseen_epoch unseen_payload unseen_stored) unseen_replacement =
    (if unseen_replacement = Some True then (Code_Source_Resolved Code_Source_Resolution_Rejected,Some unseen_request)
     else (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),Some unseen_request))"
  using assms
  by (cases unseen_replacement) (auto simp: code_source_close_resolution_def code_source_reject_debit_step_def split: bool.splits)

definition unseen_run_case where
  "unseen_run_case unseen_hash unseen_crypto unseen_snapshot unseen_wire unseen_auth unseen_close unseen_slice unseen_rows =
    (if \<not> rdw_selected_ok unseen_hash unseen_snapshot \<or>
        \<not> unseen_reservation_slice unseen_slice (rdw_record_bytes unseen_snapshot) then [[0]]
     else case decode_wire_packet (rdw_packet_bytes unseen_wire) of None \<Rightarrow> [[1]]
       | Some unseen_packet \<Rightarrow> (case rdw_decode_original unseen_packet unseen_wire of None \<Rightarrow> [[1]]
         | Some (unseen_request,unseen_payload) \<Rightarrow>
           if \<not> rdw_wire_admitted unseen_hash unseen_crypto unseen_snapshot unseen_packet unseen_wire unseen_auth unseen_payload
           then [[2]]
           else let unseen_obs = rdw_observation unseen_snapshot;
                    unseen_core = packet_core unseen_packet;
                    unseen_key = authenticated_wire_message_id unseen_core;
                    unseen_disp = code_source_resolution_disposition unseen_obs unseen_request;
                    unseen_retained = rdw_receipt unseen_snapshot (source_debit_id unseen_request) unseen_payload;
                    unseen_arrival = code_compare_binding (map_of (rdw_transport_bindings unseen_snapshot) unseen_key)
                        (encode_wire_core unseen_core);
                    unseen_base = [[3,rdw_disposition_words unseen_disp,rdw_receipt_word unseen_retained,rdw_arrival_word unseen_arrival],
                      [fst (source_control_stored unseen_obs)],rdw_address_words (rdw_head unseen_snapshot),
                      rdw_request_words unseen_request,
                      [wire_deployment unseen_core,wire_source_domain unseen_core,wire_principal unseen_core],wire_uuid unseen_core,
                      [rdw_host_clock unseen_auth,wire_sent_seconds unseen_core],rdw_cut_words (rdw_cut unseen_snapshot)]
                      @ rdw_payload_rows unseen_payload
                in if unseen_close = Some True \<and> unseen_disp = Inr None
                   then unseen_base @ concat (map (\<lambda>unseen_current.
                       map (\<lambda>unseen_replace. rdw_tail_words
                         (unseen_resolve_tail unseen_snapshot unseen_packet unseen_request unseen_payload unseen_auth unseen_rows
                            unseen_current unseen_replace))
                         [None,Some False,Some True]) [None,Some (source_control_stored unseen_obs)])
                   else [[4]]))"

definition unseen_nat_abi ::
  "nat list list list list \<Rightarrow> nat list list \<Rightarrow> nat list list list \<Rightarrow> nat list list" where
  "unseen_nat_abi unseen_input unseen_slice unseen_rows =
    (case unseen_input of
       [[[unseen_control_raw,unseen_control_canon,unseen_control_digest,unseen_raw_record,unseen_record_canon]],
        [[[unseen_mod,unseen_writer,unseen_expected,unseen_size],unseen_profile,unseen_address,unseen_head_digest,
         unseen_header,unseen_parent,unseen_parent_digest,unseen_cut]],
        [[unseen_revoked,unseen_close_words]],unseen_cancelled,unseen_decisions,unseen_latest,unseen_calls,
        unseen_transport,[unseen_wire_rows],[unseen_auth_rows],unseen_hash_rows,unseen_crypto_facts,[unseen_claimed]] \<Rightarrow>
        (case (rdw_make_profile unseen_profile,rdw_make_address unseen_address unseen_head_digest,
           rdw_parse_fields [unseen_header,unseen_parent,unseen_parent_digest],rdw_parse_cut unseen_cut,rdw_parse_close unseen_close_words,
           rdw_collect rdw_parse_transport unseen_cancelled,rdw_collect rdw_parse_decision unseen_decisions,
           rdw_collect rdw_parse_latest unseen_latest,rdw_collect rdw_parse_saved unseen_calls,
           rdw_collect rdw_parse_transport_binding unseen_transport,rdw_parse_wire unseen_wire_rows,rdw_parse_auth unseen_auth_rows,
           rdw_collect rdw_parse_hash unseen_hash_rows,rdw_collect rdw_id unseen_claimed,rdw_collect unseen_parse_reservation unseen_rows) of
           (Some unseen_cfg,Some unseen_hd,Some unseen_hdr,Some unseen_product_cut,Some unseen_close_arg,
            Some unseen_cancels,Some unseen_decs,Some unseen_latest_ids,Some unseen_retained,Some unseen_seen,
            Some unseen_wire,Some unseen_auth,Some unseen_hashes,Some unseen_claims,Some unseen_reservations) \<Rightarrow>
           let unseen_obs = \<lparr>source_control_stored = (unseen_mod,unseen_control_raw),source_control_revoked = unseen_revoked,
             source_control_cancelled = unseen_cancels,source_control_decisions = unseen_decs,source_control_latest = unseen_latest_ids\<rparr>;
               unseen_snapshot = \<lparr>rdw_observation = unseen_obs,rdw_head = unseen_hd,rdw_control_profile = unseen_cfg,
             rdw_control_writer = unseen_writer,rdw_expected_writer = unseen_expected,rdw_control_canonical = unseen_control_canon,
             rdw_control_sha = unseen_control_digest,rdw_file_size = unseen_size,rdw_record_bytes = unseen_raw_record,
             rdw_record_canonical = unseen_record_canon,rdw_record_header = unseen_hdr,rdw_cut = unseen_product_cut,
             rdw_ordinary_calls = unseen_retained,rdw_transport_bindings = unseen_seen,rdw_other_claims = unseen_claims\<rparr>
           in unseen_run_case (map_of unseen_hashes)
                (\<lambda>unseen_k unseen_msg unseen_s. List.member unseen_crypto_facts [unseen_k,unseen_msg,unseen_s])
                unseen_snapshot unseen_wire unseen_auth unseen_close_arg unseen_slice unseen_reservations
         | _ \<Rightarrow> [[0]])
     | _ \<Rightarrow> [[0]])"

definition unseen_integer_word :: "integer \<Rightarrow> bool" where
  "unseen_integer_word unseen_n \<longleftrightarrow> 0 \<le> unseen_n \<and> unseen_n < 18446744073709551616"

definition unseen_integer_abi ::
  "integer list list list list \<Rightarrow> integer list list \<Rightarrow> integer list list list \<Rightarrow> integer list list" where
  "unseen_integer_abi unseen_input unseen_slice unseen_rows =
    (if list_all (list_all (list_all (list_all unseen_integer_word))) unseen_input \<and>
        list_all (list_all unseen_integer_word) unseen_slice \<and>
        list_all (list_all (list_all unseen_integer_word)) unseen_rows
      then map (map integer_of_nat)
        (unseen_nat_abi (map (map (map (map nat_of_integer))) unseen_input)
          (map (map nat_of_integer) unseen_slice) (map (map (map nat_of_integer)) unseen_rows))
      else [[0]])"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms unseen_projection_uses_the_exact_reservation_slice
     unseen_close_refuses_a_missing_or_mismatched_credential
     unseen_close_with_exact_credential_and_no_latest_only_succeeds_after_replacement})
  then () else error "Unexpected oracle in unseen Debit close link"
\<close>

export_code unseen_integer_abi in SML
  module_name OIP_Resolver_Unseen_Close_ABI file_prefix "oip_resolver_unseen_close_abi"

end

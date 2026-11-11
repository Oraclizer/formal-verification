theory Resolver_Waiting_Link
  imports "OIP_Message_Code.Wire_Code_Reference_Admission"
    "OIP_Message_Code.Wire_Code_Debit_Resolution"
    "HOL-Library.Code_Target_Nat"
    "OIP_Completion_Gates.Completion_Gates"
begin

text \<open>Conditional resolver projection for an already attached local endpoint.
  The exact selected slice and control value carry externally decoded typed views.
  The primitive inputs are canonical re-encodings, digests, and a strict signature
  fact for the original packet. The recorded current receipt and execution
  identities are premises. Full journal I/O and retained transition validation
  precede the projection. The before-worker row is an observation only.\<close>

record rdw_address =
  rdw_address_profile :: recovery_profile
  rdw_address_sequence :: nat
  rdw_address_offset :: nat
  rdw_address_length :: nat
  rdw_address_hash :: wire_bytes

record rdw_header =
  rdw_header_profile :: recovery_profile
  rdw_header_sequence :: nat
  rdw_header_parent :: "rdw_address option"

definition rdw_span_ends_by :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "rdw_span_ends_by rdw_offset rdw_length rdw_upper \<longleftrightarrow>
    rdw_offset + rdw_length \<le> rdw_upper \<and> rdw_upper < 2^64"

fun rdw_parent_ok :: "rdw_address \<Rightarrow> rdw_address option \<Rightarrow> bool" where
  "rdw_parent_ok rdw_selected_address None = (rdw_address_sequence rdw_selected_address = 0)"
| "rdw_parent_ok rdw_selected_address (Some rdw_parent) =
    (rdw_address_profile rdw_parent = rdw_address_profile rdw_selected_address \<and>
     Suc (rdw_address_sequence rdw_parent) = rdw_address_sequence rdw_selected_address \<and>
     rdw_address_sequence rdw_selected_address < 2^64 \<and>
     rdw_span_ends_by (rdw_address_offset rdw_parent) (rdw_address_length rdw_parent)
        (rdw_address_offset rdw_selected_address))"

record rdw_selected =
  rdw_observation :: code_source_control_observation
  rdw_head :: rdw_address
  rdw_control_profile :: recovery_profile
  rdw_control_writer :: nat
  rdw_expected_writer :: nat
  rdw_control_canonical :: wire_bytes
  rdw_control_sha :: wire_bytes
  rdw_file_size :: nat
  rdw_record_bytes :: wire_bytes
  rdw_record_canonical :: wire_bytes
  rdw_record_header :: rdw_header
  rdw_cut :: product_cut
  rdw_ordinary_calls :: "(client_call_id \<times> (code_source_call_payload \<times> code_source_outcome)) list"
  rdw_transport_bindings :: "(authenticated_message_id \<times> wire_bytes) list"
  rdw_other_claims :: "client_call_id list"

definition rdw_selected_ok where
  "rdw_selected_ok rdw_hash rdw_snapshot \<longleftrightarrow>
    (let rdw_loaded = source_control_stored (rdw_observation rdw_snapshot);
         rdw_addr = rdw_head rdw_snapshot; rdw_raw = rdw_record_bytes rdw_snapshot
     in 0 < fst rdw_loaded \<and>
        snd rdw_loaded = rdw_control_canonical rdw_snapshot \<and>
        rdw_hash (snd rdw_loaded) = Some (rdw_control_sha rdw_snapshot) \<and>
        rdw_control_profile rdw_snapshot = rdw_address_profile rdw_addr \<and>
        rdw_control_writer rdw_snapshot = rdw_expected_writer rdw_snapshot \<and>
        0 < rdw_address_length rdw_addr \<and> length rdw_raw = rdw_address_length rdw_addr \<and>
        rdw_span_ends_by (rdw_address_offset rdw_addr) (rdw_address_length rdw_addr) (rdw_file_size rdw_snapshot) \<and>
        rdw_hash rdw_raw = Some (rdw_address_hash rdw_addr) \<and>
        rdw_record_canonical rdw_snapshot = rdw_raw \<and>
        rdw_header_profile (rdw_record_header rdw_snapshot) = rdw_address_profile rdw_addr \<and>
        rdw_header_sequence (rdw_record_header rdw_snapshot) = rdw_address_sequence rdw_addr \<and>
        rdw_parent_ok rdw_addr (rdw_header_parent (rdw_record_header rdw_snapshot)))"

lemma rdw_selected_pass_binds_the_exact_control_and_record_bytes:
  assumes "rdw_selected_ok rdw_hash rdw_snapshot"
  shows "snd (source_control_stored (rdw_observation rdw_snapshot)) = rdw_control_canonical rdw_snapshot"
    "rdw_hash (snd (source_control_stored (rdw_observation rdw_snapshot))) = Some (rdw_control_sha rdw_snapshot)"
    "rdw_hash (rdw_record_bytes rdw_snapshot) = Some (rdw_address_hash (rdw_head rdw_snapshot))"
    "rdw_record_canonical rdw_snapshot = rdw_record_bytes rdw_snapshot"
  using assms unfolding rdw_selected_ok_def Let_def
  by blast+

record rdw_wire_input =
  rdw_packet_bytes :: wire_bytes
  rdw_core_bytes :: wire_bytes
  rdw_packet_sha :: wire_bytes
  rdw_core_sha :: wire_bytes
  rdw_preimage :: wire_bytes
  rdw_signature :: wire_bytes

record rdw_authorization =
  rdw_receipt_identity :: registered_identity
  rdw_execute_identity :: "registered_identity option"
  rdw_session :: nat
  rdw_epoch :: nat
  rdw_deployment :: nat
  rdw_domain :: nat
  rdw_target :: nat
  rdw_principal :: nat
  rdw_signed_clock :: nat
  rdw_host_clock :: nat
  rdw_frame_limit :: nat
  rdw_public_key :: wire_bytes

definition rdw_original_request where
  "rdw_original_request rdw_original =
    \<lparr>source_debit_id = original_call rdw_original,source_debit_origin = original_origin rdw_original,
      source_debit_generation = original_generation rdw_original,source_debit_packet = original_packet rdw_original\<rparr>"

definition rdw_decode_original where
  "rdw_decode_original rdw_packet rdw_wire =
    (let rdw_core = packet_core rdw_packet in
      case code_decode_original_debit (rdw_packet_bytes rdw_wire) rdw_core of
        None \<Rightarrow> None
      | Some rdw_original \<Rightarrow>
          (case code_decode_ordinary rdw_core of
             Code_Ordinary_Ready rdw_native rdw_credential rdw_versions (Wire_Debit rdw_generation) \<Rightarrow>
               Some (rdw_original_request rdw_original,
                 code_source_payload_from_native rdw_core rdw_native rdw_credential rdw_versions (Wire_Debit rdw_generation))
           | _ \<Rightarrow> None))"

lemma rdw_materialized_request_keeps_the_original_packet:
  assumes "rdw_decode_original rdw_packet rdw_wire = Some (rdw_request,rdw_payload)"
  shows "source_debit_packet rdw_request = rdw_packet_bytes rdw_wire"
proof -
  obtain rdw_original where rdw_decoded:
    "code_decode_original_debit (rdw_packet_bytes rdw_wire) (packet_core rdw_packet) = Some rdw_original"
    and rdw_request: "rdw_request = rdw_original_request rdw_original"
    using assms by (auto simp: rdw_decode_original_def Let_def
      split: option.splits code_ordinary_result.splits ordinary_wire_command.splits)
  have "original_packet rdw_original = rdw_packet_bytes rdw_wire"
    using a_decoded_original_debit_keeps_the_native_id_origin_and_generation[OF rdw_decoded] by blast
  then show ?thesis by (simp add: rdw_request rdw_original_request_def)
qed

definition rdw_wire_admitted where
  "rdw_wire_admitted rdw_hash rdw_crypto rdw_snapshot rdw_packet rdw_wire rdw_auth rdw_payload \<longleftrightarrow>
    (let rdw_core = packet_core rdw_packet; rdw_actor = rdw_receipt_identity rdw_auth
     in encode_wire_core rdw_core = rdw_core_bytes rdw_wire \<and>
        rdw_hash (rdw_packet_bytes rdw_wire) = Some (rdw_packet_sha rdw_wire) \<and>
        rdw_hash (rdw_core_bytes rdw_wire) = Some (rdw_core_sha rdw_wire) \<and>
        envelope_signing_bytes rdw_core = rdw_preimage rdw_wire \<and>
        packet_signature rdw_packet = rdw_signature rdw_wire \<and> wire_signature_scheme rdw_core = 1 \<and>
        rdw_crypto (rdw_public_key rdw_auth) (rdw_preimage rdw_wire) (rdw_signature rdw_wire) \<and>
        wire_sent_seconds rdw_core = rdw_signed_clock rdw_auth \<and>
        length (rdw_packet_bytes rdw_wire) \<le> rdw_frame_limit rdw_auth \<and>
        wire_deployment rdw_core = rdw_deployment rdw_auth \<and>
        wire_source_domain rdw_core = rdw_domain rdw_auth \<and>
        wire_target_domain rdw_core = rdw_target rdw_auth \<and>
        wire_principal rdw_core = rdw_principal rdw_auth \<and>
        identity_principal rdw_actor = rdw_principal rdw_auth \<and> identity_domain rdw_actor = rdw_domain rdw_auth \<and>
        source_payload_session rdw_payload = rdw_session rdw_auth \<and>
        rdw_epoch rdw_auth = cut_authority_epoch (rdw_cut rdw_snapshot))"

fun rdw_collection :: "code_source_outcome cg_reply \<Rightarrow> code_source_collection" where
  "rdw_collection CG_Waiting = Code_Source_Collection_Waiting"
| "rdw_collection CG_Rejected = Code_Source_Collection_Rejected"
| "rdw_collection (CG_Collected rdw_result) = Code_Source_Collected rdw_result"

definition rdw_nonfinal_saved where
  "rdw_nonfinal_saved rdw_saved \<longleftrightarrow>
    source_outcome_reply rdw_saved = Code_Source_Accepted Code_Source_Reserved_Reply \<or>
    source_outcome_reply rdw_saved = Code_Source_Accepted Code_Source_Dispatched_Reply"

definition rdw_receipt where
  "rdw_receipt rdw_snapshot rdw_id rdw_payload =
    (if List.member (rdw_other_claims rdw_snapshot) rdw_id then None
     else Some (Code_Source_Ordinary_Receipt (rdw_collection (fst
       (cg_collect_view (map_option (\<lambda>(rdw_saved,rdw_result).
         (rdw_saved = rdw_payload, rdw_saved = rdw_payload \<and> rdw_nonfinal_saved rdw_result, rdw_result))
         (map_of (rdw_ordinary_calls rdw_snapshot) rdw_id)))))))"

lemma rdw_absent_ordinary_call_yields_waiting:
  assumes "\<not> List.member (rdw_other_claims rdw_snapshot) rdw_id"
    "map_of (rdw_ordinary_calls rdw_snapshot) rdw_id = None"
  shows "rdw_receipt rdw_snapshot rdw_id rdw_payload = Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting)"
  using assms by (simp add: rdw_receipt_def)

lemma rdw_saved_ordinary_payload_mismatch_precedes_readiness:
  assumes "\<not> List.member (rdw_other_claims rdw_snapshot) rdw_id"
    "map_of (rdw_ordinary_calls rdw_snapshot) rdw_id = Some (rdw_saved,rdw_result)"
    "rdw_saved \<noteq> rdw_payload"
  shows "rdw_receipt rdw_snapshot rdw_id rdw_payload = Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Rejected)"
  using assms by (simp add: rdw_receipt_def)

definition rdw_tail where
  "rdw_tail rdw_snapshot rdw_packet rdw_request rdw_payload rdw_auth rdw_close rdw_current rdw_replacement =
    (let rdw_core = packet_core rdw_packet; rdw_key = authenticated_wire_message_id rdw_core in
      code_source_resolve_debit_tail (rdw_observation rdw_snapshot) rdw_request rdw_key (encode_wire_core rdw_core)
        (map_of (rdw_transport_bindings rdw_snapshot) rdw_key)
        (rdw_receipt rdw_snapshot (source_debit_id rdw_request) rdw_payload) rdw_close
        (rdw_execute_identity rdw_auth) (identity_principal (rdw_receipt_identity rdw_auth)) (rdw_epoch rdw_auth)
        rdw_payload None rdw_current rdw_replacement)"

text \<open>The exported close is the Pending path, where the unseen-work
  reservation branch is unconsumed. CAS False or unknown still exposes the
  attempted exact request. The selected record in this fixture has only
  ordinary nonfinal Reserve and Dispatch calls. A selected Waiting receipt
  with Published or Refused control is covered by the logical tail below and
  has no same-input product observation in this run.\<close>

lemma rdw_pending_close_returns_rejection_only_after_a_positive_replacement:
  assumes rdw_exec: "rdw_exec_identity \<noteq> None"
    and rdw_pending: "code_source_resolution_disposition rdw_observed rdw_request = Inr (Some Ref_Pending)"
  shows "code_source_close_resolution rdw_observed rdw_request rdw_exec_identity rdw_unseen rdw_replacement =
    (if rdw_replacement = Some True then (Code_Source_Resolved Code_Source_Resolution_Rejected,Some rdw_request)
     else (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),Some rdw_request))"
  using rdw_exec rdw_pending
  by (cases rdw_replacement) (auto simp: code_source_close_resolution_def code_source_reject_debit_step_def split: bool.splits)

lemma rdw_waiting_published_or_refused_is_hold:
  assumes rdw_principal: "code_source_resolution_principal_refusal rdw_observed rdw_actor = None"
    and rdw_disposition: "code_source_resolution_disposition rdw_observed rdw_request = Inr (Some rdw_status)"
    and rdw_done: "rdw_status = Ref_Applied \<or> rdw_status = Ref_Retained_Refusal"
    and rdw_pending: "code_source_pending_transport_refusal rdw_key (source_debit_packet rdw_request)
      (source_control_decisions rdw_observed) = None"
    and rdw_first: "rdw_prior = None \<or> rdw_prior = Some rdw_core"
  shows "code_source_resolve_debit_tail rdw_observed rdw_request rdw_key rdw_core rdw_prior
    (Some (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting)) rdw_close rdw_exec_identity
    rdw_actor rdw_auth_epoch rdw_payload rdw_reservation rdw_current rdw_replacement =
      (Code_Source_Resolve_Error (Code_Source_Wire_Recovery Code_Source_Recovery_Hold),None)"
  using assms by (auto simp: code_source_resolve_debit_tail_def code_compare_binding_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms rdw_selected_pass_binds_the_exact_control_and_record_bytes
       rdw_materialized_request_keeps_the_original_packet rdw_absent_ordinary_call_yields_waiting
       rdw_saved_ordinary_payload_mismatch_precedes_readiness
       rdw_pending_close_returns_rejection_only_after_a_positive_replacement
       rdw_waiting_published_or_refused_is_hold})
  then () else error "Unexpected oracle in exact resolver waiting link"
\<close>

end

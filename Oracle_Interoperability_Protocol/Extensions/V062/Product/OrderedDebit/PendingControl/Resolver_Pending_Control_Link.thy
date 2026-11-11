theory Resolver_Pending_Control_Link
  imports "OIP_Resolver_Waiting_Model_Link.Resolver_Waiting_ABI"
begin

text \<open>The selected control comes from the original Pending observation.
  Canonical JSON and its finite tables are supplied by the input projection.
  Each candidate is decoded from its own exact packet. The exported values
  are OrderedCut disposition, transport and work observations and the close
  control step. Current authorization and physical publication are separate.\<close>

definition ordered_pending_latest_eligibility where
  "ordered_pending_latest_eligibility pending_obs pending_request =
    (case map_of (source_control_latest pending_obs) (code_source_debit_work pending_request) of
       None \<Rightarrow> Some True
     | Some pending_previous \<Rightarrow>
         map_option (\<lambda>(pending_saved,pending_status).
           fst pending_previous = fst (source_debit_id pending_request) \<and>
           pending_status \<in> {Ref_Explicit_Rejection,Ref_Retained_Refusal})
           (map_of (source_control_decisions pending_obs) pending_previous))"

definition ordered_pending_check_debit where
  "ordered_pending_check_debit pending_obs pending_request =
    (case code_source_resolution_disposition pending_obs pending_request of
       Inl pending_error \<Rightarrow> Inl pending_error
     | Inr (Some Ref_Explicit_Rejection) \<Rightarrow> Inl Code_Source_Wire_Product_Rejected
     | Inr (Some pending_status) \<Rightarrow> Inr (Some pending_status)
     | Inr None \<Rightarrow>
       (case ordered_pending_latest_eligibility pending_obs pending_request of
          None \<Rightarrow> Inl (Code_Source_Wire_Recovery Code_Source_Recovery_Hold)
        | Some pending_allowed \<Rightarrow> if pending_allowed then Inr None else Inl Code_Source_Wire_Unresolved))"

lemma ordered_pending_latest_eligibility_matches_the_reference_work_gate:
  assumes pending_latest:
    "control_latest pending_reference (reference_work_key pending_original) =
     map_of (source_control_latest pending_obs) (code_source_debit_work pending_request)"
    and pending_namespace: "fst (original_call pending_original) = fst (source_debit_id pending_request)"
    and pending_status:
    "\<And>pending_previous. map_option snd (control_decisions pending_reference pending_previous) =
      map_option snd (map_of (source_control_decisions pending_obs) pending_previous)"
  shows "(ordered_pending_latest_eligibility pending_obs pending_request = Some True) =
         reference_work_can_start pending_original pending_reference"
proof (cases "map_of (source_control_latest pending_obs) (code_source_debit_work pending_request)")
  case None
  then show ?thesis by (simp add: ordered_pending_latest_eligibility_def reference_work_can_start_def pending_latest)
next
  case (Some pending_previous)
  note pending_lookup = Some
  show ?thesis
    using pending_status[of pending_previous]
    by (cases "control_decisions pending_reference pending_previous";
        cases "map_of (source_control_decisions pending_obs) pending_previous")
       (auto simp: ordered_pending_latest_eligibility_def reference_work_can_start_def pending_latest pending_lookup
          pending_namespace split: prod.splits)
qed

lemma ordered_pending_latest_blocks_a_new_debit_at_the_same_work:
  assumes pending_new: "code_source_resolution_disposition pending_obs pending_request = Inr None"
    and pending_latest: "map_of (source_control_latest pending_obs) (code_source_debit_work pending_request) = Some pending_previous"
    and pending_saved: "map_of (source_control_decisions pending_obs) pending_previous = Some (pending_old,Ref_Pending)"
  shows "ordered_pending_check_debit pending_obs pending_request = Inl Code_Source_Wire_Unresolved"
  using assms by (simp add: ordered_pending_check_debit_def ordered_pending_latest_eligibility_def)

lemma ordered_pending_occupied_latest_refuses_an_authorized_unseen_close:
  assumes pending_new: "code_source_resolution_disposition pending_obs pending_request = Inr None"
    and pending_occupied: "map_of (source_control_latest pending_obs) (code_source_debit_work pending_request) = Some pending_previous"
    and pending_execute: "pending_identity \<noteq> None"
  shows "code_source_close_resolution pending_obs pending_request pending_identity True pending_replacement =
         (Code_Source_Resolve_Error Code_Source_Wire_Unresolved,None)"
  using assms by (simp add: code_source_close_resolution_def code_source_reject_debit_step_def)

definition ordered_pending_pre_tail where
  "ordered_pending_pre_tail pending_obs pending_request pending_key =
    (case code_source_resolution_disposition pending_obs pending_request of
       Inl pending_error \<Rightarrow> Some pending_error
     | Inr _ \<Rightarrow> code_source_pending_transport_refusal pending_key (source_debit_packet pending_request)
          (source_control_decisions pending_obs))"

lemma ordered_pending_pre_tail_error_short_circuits_the_resolver:
  assumes pending_principal: "code_source_resolution_principal_refusal pending_obs pending_actor = None"
    and pending_error: "ordered_pending_pre_tail pending_obs pending_request pending_key = Some pending_reason"
  shows "code_source_resolve_debit_tail pending_obs pending_request pending_key pending_core pending_prior pending_receipt pending_close
         pending_identity pending_actor pending_epoch pending_payload pending_reservation pending_current pending_replacement =
         (Code_Source_Resolve_Error pending_reason,None)"
  using assms by (cases "code_source_resolution_disposition pending_obs pending_request")
    (auto simp: ordered_pending_pre_tail_def code_source_resolve_debit_tail_def split: option.splits)

definition ordered_pending_parse_original where
  "ordered_pending_parse_original pending_packet =
    Option.bind (decode_wire_packet pending_packet) (\<lambda>pending_frame.
      map_option (\<lambda>pending_original. (pending_frame,rdw_original_request pending_original))
        (code_decode_original_debit pending_packet (packet_core pending_frame)))"

fun ordered_pending_exact_decision where
  "ordered_pending_exact_decision (pending_id,(pending_request,pending_status)) =
    (pending_id = source_debit_id pending_request \<and>
     (case ordered_pending_parse_original (source_debit_packet pending_request) of None \<Rightarrow> False
      | Some (pending_packet,pending_decoded) \<Rightarrow> pending_decoded = pending_request))"

definition ordered_pending_control_well_formed where
  "ordered_pending_control_well_formed pending_obs \<longleftrightarrow>
    (let pending_decisions = source_control_decisions pending_obs;
         pending_latest = source_control_latest pending_obs
     in distinct (map fst pending_decisions) \<and> distinct (map fst pending_latest) \<and>
        list_all ordered_pending_exact_decision pending_decisions \<and>
        list_all (\<lambda>(pending_work,pending_id).
          case map_of pending_decisions pending_id of None \<Rightarrow> False
          | Some (pending_request,pending_status) \<Rightarrow> code_source_debit_work pending_request = pending_work)
          pending_latest)"

fun ordered_pending_error_words :: "code_source_wire_error option \<Rightarrow> nat list" where
  "ordered_pending_error_words None = [0]"
| "ordered_pending_error_words (Some Code_Source_Wire_Unresolved) = [1,50]"
| "ordered_pending_error_words (Some (Code_Source_Wire_Recovery Code_Source_Recovery_Hold)) = [2,50]"
| "ordered_pending_error_words (Some pending_error) = [3,code_source_error_number pending_error]"

fun ordered_pending_result_words :: "(code_source_wire_error + reference_disposition option) \<Rightarrow> nat list" where
  "ordered_pending_result_words (Inr pending_status) = [rdw_disposition_words (Inr pending_status)]"
| "ordered_pending_result_words (Inl pending_error) = 5 # ordered_pending_error_words (Some pending_error)"

fun ordered_pending_close_words :: "code_source_close_control_step \<Rightarrow> nat list" where
  "ordered_pending_close_words Code_Source_Close_Already_Rejected = [1]"
| "ordered_pending_close_words Code_Source_Close_Replace = [2]"
| "ordered_pending_close_words (Code_Source_Close_Refused pending_error) = 3 # ordered_pending_error_words (Some pending_error)"

definition ordered_pending_latest_words where
  "ordered_pending_latest_words pending_obs pending_request =
    (case map_of (source_control_latest pending_obs) (code_source_debit_work pending_request) of
       None \<Rightarrow> [0]
     | Some (pending_namespace,pending_sequence) \<Rightarrow>
         (case map_of (source_control_decisions pending_obs) (pending_namespace,pending_sequence) of None \<Rightarrow> [0]
          | Some (pending_prior,pending_status) \<Rightarrow>
            [1,pending_namespace,pending_sequence,rdw_disposition_words (Inr (Some pending_status))]))"

fun ordered_pending_case ::
  "(wire_bytes \<Rightarrow> wire_bytes option) \<Rightarrow> code_source_control_observation \<Rightarrow>
   nat list list \<Rightarrow> nat list list" where
  "ordered_pending_case pending_hash pending_obs [pending_raw,pending_core_bytes,pending_packet_sha,pending_core_sha] =
    (if pending_hash pending_raw \<noteq> Some pending_packet_sha \<or> pending_hash pending_core_bytes \<noteq> Some pending_core_sha
     then [[0]]
     else case ordered_pending_parse_original pending_raw of None \<Rightarrow> [[0]]
       | Some (pending_frame,pending_request) \<Rightarrow>
         let pending_core = packet_core pending_frame;
             pending_key = authenticated_wire_message_id pending_core
         in if encode_wire_core pending_core \<noteq> pending_core_bytes then [[0]]
            else [rdw_request_words pending_request,
               [wire_deployment pending_core,wire_source_domain pending_core,wire_principal pending_core],wire_uuid pending_core,
               ordered_pending_result_words (code_source_resolution_disposition pending_obs pending_request),
               ordered_pending_error_words (code_source_pending_transport_refusal pending_key pending_raw (source_control_decisions pending_obs)),
               ordered_pending_error_words (ordered_pending_pre_tail pending_obs pending_request pending_key),
               ordered_pending_latest_words pending_obs pending_request,
               ordered_pending_result_words (ordered_pending_check_debit pending_obs pending_request),
               ordered_pending_close_words (code_source_reject_debit_step pending_obs pending_request)])"
| "ordered_pending_case pending_hash pending_obs _ = [[0]]"

definition ordered_pending_nat_abi ::
  "nat list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list \<Rightarrow>
   nat list list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list \<Rightarrow> nat list list list" where
  "ordered_pending_nat_abi pending_header pending_cancelled pending_decisions pending_latest pending_hashes pending_candidates =
    (case pending_header of [[pending_revision],pending_raw,pending_canon,pending_sha,pending_revoked] \<Rightarrow>
      (case (rdw_collect rdw_parse_transport pending_cancelled,rdw_collect rdw_parse_decision pending_decisions,
             rdw_collect rdw_parse_latest pending_latest,rdw_collect rdw_parse_hash pending_hashes) of
         (Some pending_cancels,Some pending_decs,Some pending_latest_rows,Some pending_digest_rows) \<Rightarrow>
           let pending_hash = map_of pending_digest_rows;
               pending_obs = \<lparr>source_control_stored = (pending_revision,pending_raw),source_control_revoked = pending_revoked,
                  source_control_cancelled = pending_cancels,source_control_decisions = pending_decs,
                  source_control_latest = pending_latest_rows\<rparr>
           in if 0 < pending_revision \<and> pending_raw = pending_canon \<and> pending_hash pending_raw = Some pending_sha
                   \<and> ordered_pending_control_well_formed pending_obs
              then map (ordered_pending_case pending_hash pending_obs) pending_candidates
              else [[[0]]]
       | _ \<Rightarrow> [[[0]]])
     | _ \<Rightarrow> [[[0]]])"

definition ordered_pending_integer_word :: "integer \<Rightarrow> bool" where
  "ordered_pending_integer_word pending_n \<longleftrightarrow> 0 \<le> pending_n \<and> pending_n < 18446744073709551616"

definition ordered_pending_integer_abi ::
  "integer list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list \<Rightarrow>
   integer list list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list \<Rightarrow> integer list list list" where
  "ordered_pending_integer_abi pending_header pending_cancelled pending_decisions pending_latest pending_hashes pending_candidates =
    (if list_all (list_all ordered_pending_integer_word) pending_header \<and>
        list_all (list_all (list_all (list_all ordered_pending_integer_word)))
          [pending_cancelled,pending_decisions,pending_latest,pending_hashes,pending_candidates]
     then map (map (map integer_of_nat))
       (ordered_pending_nat_abi (map (map nat_of_integer) pending_header)
          (map (map (map nat_of_integer)) pending_cancelled) (map (map (map nat_of_integer)) pending_decisions)
          (map (map (map nat_of_integer)) pending_latest) (map (map (map nat_of_integer)) pending_hashes)
          (map (map (map nat_of_integer)) pending_candidates))
     else [[[0]]])"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ordered_pending_latest_eligibility_matches_the_reference_work_gate
     ordered_pending_latest_blocks_a_new_debit_at_the_same_work
     ordered_pending_occupied_latest_refuses_an_authorized_unseen_close
     ordered_pending_pre_tail_error_short_circuits_the_resolver})
  then () else error "Unexpected oracle in exact Pending control link"
\<close>

export_code ordered_pending_integer_abi in SML
  module_name OIP_Resolver_Pending_Control_ABI file_prefix "oip_resolver_pending_control_abi"

end

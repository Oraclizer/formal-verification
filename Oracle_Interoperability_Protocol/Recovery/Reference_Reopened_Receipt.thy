theory Reference_Reopened_Receipt
  imports Reference_Recovery_Code "OIP_Product.Recovery_Simulation"
begin

record ('bytes, 'answer) native_receipt_row =
  native_receipt_request :: 'bytes
  native_receipt_answer :: 'answer
  native_receipt_release :: "(source_key \<times> nat) option"

record ('bytes, 'answer) native_receipt_image =
  native_receipt_rows :: "client_call_id \<Rightarrow> ('bytes, 'answer) native_receipt_row option"
  native_receipt_published :: "source_key set"
  native_receipt_locks :: "nat \<Rightarrow> source_key option"
  native_receipt_online :: bool

datatype 'answer native_receipt_reply = Native_Receipt_Refused | Native_Receipt_Waiting | Native_Receipt_Collected 'answer

fun project_native_receipt where
  "project_native_receipt decode Native_Receipt_Refused = Collection_Rejected"
| "project_native_receipt decode Native_Receipt_Waiting = Collection_Waiting"
| "project_native_receipt decode (Native_Receipt_Collected answer) = Collected (decode answer)"

definition native_receipt_ready where
  "native_receipt_ready code row \<longleftrightarrow>
    (case native_receipt_release row of None \<Rightarrow> True
    | Some (origin,asset) \<Rightarrow> origin \<in> native_receipt_published code \<and> native_receipt_locks code asset \<noteq> Some origin)"

definition read_native_receipt where
  "read_native_receipt access call_id request code =
    (code, if \<not> access then Native_Receipt_Refused
      else if \<not> native_receipt_online code then Native_Receipt_Waiting
      else case native_receipt_rows code call_id of None \<Rightarrow> Native_Receipt_Waiting
        | Some row \<Rightarrow> if native_receipt_request row \<noteq> request then Native_Receipt_Refused
          else if native_receipt_ready code row then Native_Receipt_Collected (native_receipt_answer row)
          else Native_Receipt_Waiting)"

definition native_row_matches_outcome where
  "native_row_matches_outcome encode decode row entry \<longleftrightarrow>
     (let payload = result_payload entry; envelope = payload_envelope payload in
       native_receipt_request row = encode payload \<and>
       decode (native_receipt_answer row) = result_outcome entry \<and>
       native_receipt_release row = map_option (\<lambda>origin. (origin, envelope_asset envelope))
         (final_effect_key (envelope_command envelope) (result_outcome entry)))"

definition native_receipts_match_outcomes where
  "native_receipts_match_outcomes encode decode code model \<longleftrightarrow>
    (let calls = product_calls (outcome_source model); core = call_authority_state calls in
       native_receipt_online code = (call_local_status calls = Endpoint_Up) \<and>
       native_receipt_published code = core_published core \<and>
       native_receipt_locks code = asset_owner (machine_state (core_parent core)) \<and>
       (\<forall>call_id. rel_option (native_row_matches_outcome encode decode)
         (native_receipt_rows code call_id) (outcome_entries model call_id)))"

theorem the_native_exact_receipt_reads_the_related_durable_result_without_a_write:
  assumes image: "native_receipts_match_outcomes encode decode code model"
    and exact: "inj encode"
  shows "let (after, reply) = read_native_receipt (result_access_bound verified caller call_id payload model)
       call_id (encode payload) code
    in after = code \<and> native_receipts_match_outcomes encode decode after model \<and>
       project_native_receipt decode reply = observe_collection verified caller call_id payload model"
proof -
  have all_rows: "\<forall>identifier. rel_option (native_row_matches_outcome encode decode)
         (native_receipt_rows code identifier) (outcome_entries model identifier)"
    using image by (simp only: native_receipts_match_outcomes_def Let_def; blast)
  have entries: "rel_option (native_row_matches_outcome encode decode)
         (native_receipt_rows code call_id) (outcome_entries model call_id)"
    by (rule all_rows[rule_format])
  have online: "native_receipt_online code = (call_local_status (product_calls (outcome_source model)) = Endpoint_Up)"
    using image by (simp only: native_receipts_match_outcomes_def Let_def; blast)
  have ready: "native_receipt_ready code row = result_completion_ready entry model"
    if row: "native_row_matches_outcome encode decode row entry" for row entry
    using image row by (auto simp: native_receipts_match_outcomes_def native_row_matches_outcome_def
      native_receipt_ready_def result_completion_ready_def Let_def split: option.splits)
  show ?thesis using image entries exact online
    by (cases "native_receipt_rows code call_id"; cases "outcome_entries model call_id")
       (auto simp: native_row_matches_outcome_def read_native_receipt_def
         observe_collection_def Let_def ready inj_eq split: if_splits)
qed

lemma dropping_only_exact_request_equality_changes_the_same_ready_native_receipt:
  assumes row: "native_receipt_rows code call_id = Some saved" "native_receipt_ready code saved"
    and live: "native_receipt_online code" and different: "native_receipt_request saved \<noteq> changed"
  shows "read_native_receipt True call_id changed code = (code,Native_Receipt_Refused)"
    "read_native_receipt True call_id (native_receipt_request saved) code =
       (code,Native_Receipt_Collected (native_receipt_answer saved))"
  using assms by (simp_all add: read_native_receipt_def)

theorem exact_native_reopen_and_the_following_receipt_match_the_same_model_cut:
  fixes native :: "('hash, 'image) native_journal_view"
    and disk :: "'hash placed_digest recovery_store"
  assumes opened: "native_reopen_view attached required witness profile native = Some exact_image"
    and journal: "journal_views_related (\<lambda>image stored. native_receipts_match_outcomes encode decode (view image)
        (current_product_outcomes (reopen_retained_product (attachment_connection attachment) (image_records stored)))) native disk"
    and addressed: "\<And>address stored. native_current native = Some address \<Longrightarrow>
       flushed_records disk (model_head_of address) = Some stored \<Longrightarrow>
       head_for_record digest stored = model_head_of address"
    and authenticated: "attachment_profile attachment = profile"
    and exact: "inj encode"
  obtains restored where "reopen_from_authenticated_head digest profile (Some attachment) disk = Some restored"
    "\<And>verified caller call_id payload. let model = current_product_outcomes restored;
         code = view exact_image; (after,reply) = read_native_receipt
            (result_access_bound verified caller call_id payload model) call_id (encode payload) code
       in after = code \<and> native_receipts_match_outcomes encode decode after model \<and>
          project_native_receipt decode reply = observe_collection verified caller call_id payload model"
proof -
  let ?receipts = "\<lambda>image durable. native_receipts_match_outcomes encode decode (view image)
       (current_product_outcomes (reopen_retained_product (attachment_connection attachment) durable))"
  show thesis
  proof (rule every_exact_native_reopen_selects_related_model_records[where relates="?receipts"])
    show "native_reopen_view attached required witness profile native = Some exact_image" by (rule opened)
    show "journal_views_related (\<lambda>image stored. ?receipts image (image_records stored)) native disk" by (rule journal)
    show "\<And>address stored. native_current native = Some address \<Longrightarrow>
        flushed_records disk (model_head_of address) = Some stored \<Longrightarrow>
        head_for_record digest stored = model_head_of address" by (rule addressed)
    show "attachment_profile attachment = profile" by (rule authenticated)
  next
    fix stored
    assume related: "native_receipts_match_outcomes encode decode (view exact_image)
       (current_product_outcomes (reopen_retained_product (attachment_connection attachment) (image_records stored)))"
    assume restored: "reopen_from_authenticated_head digest profile (Some attachment) disk =
        Some (reopen_retained_product (attachment_connection attachment) (image_records stored))"
    show thesis
    proof (rule that[OF restored])
      fix verified caller call_id payload
      let ?model = "current_product_outcomes (reopen_retained_product (attachment_connection attachment) (image_records stored))"
      show "let model = ?model; code = view exact_image; (after,reply) = read_native_receipt
            (result_access_bound verified caller call_id payload model) call_id (encode payload) code
          in after = code \<and> native_receipts_match_outcomes encode decode after model \<and>
             project_native_receipt decode reply = observe_collection verified caller call_id payload model"
        using the_native_exact_receipt_reads_the_related_durable_result_without_a_write[OF related exact,
            where verified=verified and caller=caller and call_id=call_id and payload=payload]
        by (simp only: Let_def)
    qed
  qed
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_native_exact_receipt_reads_the_related_durable_result_without_a_write
    dropping_only_exact_request_equality_changes_the_same_ready_native_receipt
    exact_native_reopen_and_the_following_receipt_match_the_same_model_cut})
  then () else error "Unexpected oracle in reopened native receipt correspondence"
\<close>

end

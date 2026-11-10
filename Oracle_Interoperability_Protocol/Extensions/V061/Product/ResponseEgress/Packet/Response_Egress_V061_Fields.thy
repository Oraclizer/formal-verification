theory Response_Egress_V061_Fields
  imports "OIP_Response_Egress_V061_Operands.Response_Egress_V061_Operands"
    "OIP_Sync_V061_Position_Boundary.Sync_V061_Reference_Boundary"
    "OIP_Reference_Write_Profile.Reference_Write_Profile"
begin

definition response_v061_accepts where
  "response_v061_accepts accept_sync accept_current family operation \<longleftrightarrow>
    reference_accepts_write family operation \<or>
    (accept_sync \<and> (family,operation) = (Wire_State_Sync,7)) \<or>
    (accept_current \<and> (family,operation) = (Wire_Query,9))"

lemma response_v061_old_admission_changes_only_for_write:
  assumes "(family,operation) \<notin> {(Wire_Lock,7),(Wire_State_Sync,7),(Wire_Query,9)}"
  shows "response_v061_accepts accept_sync accept_current family operation = code_reference_accepts family operation"
  using assms by (auto simp: response_v061_accepts_def reference_accepts_write_def)

lemma response_v061_write_uses_the_old_ordinary_layout:
  "response_v061_accepts accept_sync accept_current Wire_Lock 7"
  "decode_ordinary_tail Wire_Lock 7 [generation,amount] = Some (Wire_Write generation amount)"
  by (simp_all add: response_v061_accepts_def reference_accepts_write_def decode_ordinary_tail_def)

datatype response_v061_observation =
    Response_V061_Legacy response_fixed_observation
  | Response_V061_Sync sync_outcome "sync_outcome option"

fun response_v061_sync_result :: "sync_outcome \<Rightarrow> nat \<times> nat option" where
  "response_v061_sync_result (Sync_Committed position) = (29,Some position)"
| "response_v061_sync_result (Sync_Uncommitted Sync_Busy) = (2,None)"
| "response_v061_sync_result (Sync_Uncommitted Sync_Unavailable) = (3,None)"
| "response_v061_sync_result (Sync_Uncommitted Sync_Mismatch) = (39,None)"
| "response_v061_sync_result (Sync_Uncommitted Sync_Stale) = (40,None)"
| "response_v061_sync_result (Sync_Uncommitted Sync_Proof_Rejected) = (41,None)"

fun response_v061_result where
  "response_v061_result (Response_V061_Legacy prior) = response_fixed_result prior"
| "response_v061_result (Response_V061_Sync observed retained) =
    (if retained = Some observed then response_v061_sync_result observed else (50,None))"

definition response_v061_decode_sync where
  "response_v061_decode_sync row =
    (case row of [tag,branch,position] \<Rightarrow>
       if tag = 3 \<and> branch = 0 then Some (Sync_Committed position) else None
     | [tag,branch] \<Rightarrow>
       if tag \<noteq> 3 then None else
       if branch = 1 then Some (Sync_Uncommitted Sync_Busy) else
       if branch = 2 then Some (Sync_Uncommitted Sync_Unavailable) else
       if branch = 3 then Some (Sync_Uncommitted Sync_Mismatch) else
       if branch = 4 then Some (Sync_Uncommitted Sync_Stale) else
       if branch = 5 then Some (Sync_Uncommitted Sync_Proof_Rejected) else None
     | _ \<Rightarrow> None)"

definition response_v061_decode_observation where
  "response_v061_decode_observation mode reply v061_present retained =
    (if mode = 0 \<and> reply \<noteq> [] \<and> hd reply = 3 \<and> reply \<noteq> [3] then
       Option.bind (response_v061_decode_sync reply) (\<lambda>observed.
         if \<not> v061_present then (if retained = [] then Some (Response_V061_Sync observed None) else None)
         else case response_v061_decode_sync retained of Some saved \<Rightarrow> Some (Response_V061_Sync observed (Some saved))
          | None \<Rightarrow> map_option (\<lambda>_. Response_V061_Sync observed None) (code_rbound_receipt retained))
     else if mode = 0 \<and> v061_present \<and> retained \<noteq> [] \<and> hd retained = 3 then
       Option.bind (response_v061_decode_sync retained) (\<lambda>_.
         map_option Response_V061_Legacy (code_rbound_observation mode reply False []))
     else if mode = 1 \<and> take 2 reply = [1,3] \<and> \<not> v061_present \<and> retained = [] then
       map_option (\<lambda>_. Response_V061_Legacy (Response_Fixed_Resolved Code_Source_Resolution_Unresolved))
         (response_v061_decode_sync (tl reply))
     else map_option Response_V061_Legacy (code_rbound_observation mode reply v061_present retained))"

definition response_v061_words where
  "response_v061_words call result = (case result of (number,position) \<Rightarrow>
    case map_of sync_response_allocations number of None \<Rightarrow> response_fixed_words call result
     | Some (kind,needs_commit,targets) \<Rightarrow>
       if needs_commit \<noteq> (position \<noteq> None) then None
       else Some (kind,number,position,[fst call,snd call,reference_response_kind_number kind,number] @
         (case position of None \<Rightarrow> [0] | Some revision \<Rightarrow> [1,revision])))"

lemma response_v061_legacy_words_are_byte_inputs_of_the_old_encoder:
  "\<not> sync_added_status number \<Longrightarrow>
    response_v061_words call (number,position) = response_fixed_words call (number,position)"
  by (simp add: response_v061_words_def sync_response_lookup_is_exact sync_added_status_def)

lemma response_v061_new_words_keep_the_result_commit_position:
  "response_v061_words (v061_principal,v061_sequence) (29,Some position) =
    Some (Recorded_Result,29,Some position,[v061_principal,v061_sequence,1,29,1,position])"
  "response_v061_words call (29,None) = None"
  "number \<in> {39,40,41} \<Longrightarrow> response_v061_words (v061_principal,v061_sequence) (number,None) =
    Some (Recorded_Result,number,None,[v061_principal,v061_sequence,1,number,0])"
  "number \<in> {39,40,41} \<Longrightarrow> response_v061_words call (number,Some position) = None"
  by (auto simp: response_v061_words_def sync_response_lookup_is_exact)

lemma response_v061_sync_conversion_requires_exact_retained_outcome:
  "response_v061_result (Response_V061_Sync outcome (Some outcome)) = response_v061_sync_result outcome"
  "retained \<noteq> Some outcome \<Longrightarrow> response_v061_result (Response_V061_Sync outcome retained) = (50,None)"
  by simp_all

definition response_v061_sync_product_observation where
  "response_v061_sync_product_observation core next result = (case result of
     Sync_Reference_Outcome outcome \<Rightarrow>
       Response_V061_Sync outcome (Option.bind (sync_read_operands core) (\<lambda>request.
         Option.bind (sync_outcome_table next (sync_call request)) (\<lambda>(exact,saved).
           if exact = encode_wire_core core then Some saved else None)))
   | Sync_Product_Refusal \<Rightarrow> Response_V061_Legacy (Response_Fixed_Error Code_Source_Wire_Product_Rejected)
   | Sync_Transport_Refusal reason \<Rightarrow>
       Response_V061_Legacy (Response_Fixed_Error (Code_Source_Wire_Validation reason)))"

lemma response_v061_sync_product_readback_binds_the_same_exact_original:
  assumes "sync_reference_product transport gate verify core state = (next,Sync_Reference_Outcome outcome)"
  obtains request where "sync_read_operands core = Some request"
    "sync_outcome_table next (sync_call request) = Some (encode_wire_core core,outcome)"
  using assms by (auto simp: sync_reference_product_def sync_commit_record_def sync_write_outcome_def Let_def
    split: option.splits if_splits prod.splits sync_fresh_decision.splits)

theorem response_v061_sync_product_projects_the_selected_outcome:
  assumes "sync_reference_product transport gate verify core state = (next,Sync_Reference_Outcome outcome)"
  shows "response_v061_result (response_v061_sync_product_observation core next (Sync_Reference_Outcome outcome)) =
    response_v061_sync_result outcome"
proof -
  obtain request where parsed: "sync_read_operands core = Some request"
    and retained: "sync_outcome_table next (sync_call request) = Some (encode_wire_core core,outcome)"
    by (rule response_v061_sync_product_readback_binds_the_same_exact_original[OF assms]) blast
  show ?thesis using parsed retained by (simp add: response_v061_sync_product_observation_def)
qed

lemma response_v061_write_keeps_code_20_and_its_old_layout:
  "response_v061_words (v061_principal,v061_sequence) (20,Some position) =
    Some (Recorded_Result,20,Some position,[v061_principal,v061_sequence,1,20,1,position])"
  "response_v061_status original Recorded_Result 20 (Some position) = Some (Code_Known_Response Recorded_Result 20)"
    if "sync_operation original = (Wire_Lock,7)"
  using that by (simp_all add: response_v061_legacy_words_are_byte_inputs_of_the_old_encoder sync_added_status_def
    response_fixed_words_def response_fixed_descriptor_def code_response_words_def reference_result_codes_def
    response_v061_status_def response_extended_status_def response_extended_compatible_def sync_response_lookup_is_exact
    code_decode_response_status_def code_response_compatible_def reference_response_compatible_def
    code_known_response_number_def reference_result_targets_def Let_def sync_operation_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms response_v061_old_admission_changes_only_for_write
    response_v061_write_uses_the_old_ordinary_layout response_v061_legacy_words_are_byte_inputs_of_the_old_encoder
    response_v061_new_words_keep_the_result_commit_position response_v061_sync_conversion_requires_exact_retained_outcome
    response_v061_sync_product_readback_binds_the_same_exact_original response_v061_sync_product_projects_the_selected_outcome
    response_v061_write_keeps_code_20_and_its_old_layout})
  then () else error "Unexpected oracle in the v0.6.1 response fields"
\<close>

end

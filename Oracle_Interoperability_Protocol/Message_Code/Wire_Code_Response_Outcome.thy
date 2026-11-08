theory Wire_Code_Response_Outcome
  imports Wire_Code_Oracle_Transport "OIP_Product.Identity_Receipts"
begin

datatype code_source_accepted_reply =
    Code_Source_Rejected_Reply | Code_Source_Busy_Reply
  | Code_Source_Reserved_Reply | Code_Source_Dispatched_Reply | Code_Source_Debited_Reply
  | Code_Source_Closed_Reply | Code_Source_Preempted_Reply | Code_Source_Time_Reply
  | Code_Source_Recorded_Reply | Code_Source_Credited_Reply | Code_Source_Reconciled_Reply
  | Code_Source_Refunded_Reply | Code_Source_Data_Reply | Code_Source_Evidence_Reply | Code_Source_Published_Reply

datatype code_source_outcome_reply =
    Code_Source_Accepted code_source_accepted_reply
  | Code_Source_Duplicate_Decision | Code_Source_Duplicate_Confirmed | Code_Source_Duplicate_Reversed
  | Code_Source_Outcome_Rejected | Code_Source_Outcome_Busy | Code_Source_Outcome_Unavailable

record code_source_outcome =
  source_outcome_reply :: code_source_outcome_reply
  source_outcome_commit :: "nat option"

fun code_source_accepted_number :: "code_source_accepted_reply \<Rightarrow> nat" where
  "code_source_accepted_number Code_Source_Rejected_Reply = 1"
| "code_source_accepted_number Code_Source_Busy_Reply = 2"
| "code_source_accepted_number Code_Source_Reserved_Reply = 10"
| "code_source_accepted_number Code_Source_Dispatched_Reply = 11"
| "code_source_accepted_number Code_Source_Debited_Reply = 12"
| "code_source_accepted_number Code_Source_Closed_Reply = 13"
| "code_source_accepted_number Code_Source_Preempted_Reply = 14"
| "code_source_accepted_number Code_Source_Time_Reply = 15"
| "code_source_accepted_number Code_Source_Recorded_Reply = 16"
| "code_source_accepted_number Code_Source_Credited_Reply = 17"
| "code_source_accepted_number Code_Source_Reconciled_Reply = 18"
| "code_source_accepted_number Code_Source_Refunded_Reply = 19"
| "code_source_accepted_number Code_Source_Data_Reply = 20"
| "code_source_accepted_number Code_Source_Evidence_Reply = 21"
| "code_source_accepted_number Code_Source_Published_Reply = 22"

fun code_source_ordinary_number :: "code_source_outcome_reply \<Rightarrow> nat" where
  "code_source_ordinary_number (Code_Source_Accepted reply) = code_source_accepted_number reply"
| "code_source_ordinary_number Code_Source_Duplicate_Decision = 23"
| "code_source_ordinary_number Code_Source_Duplicate_Confirmed = 24"
| "code_source_ordinary_number Code_Source_Duplicate_Reversed = 25"
| "code_source_ordinary_number Code_Source_Outcome_Rejected = 1"
| "code_source_ordinary_number Code_Source_Outcome_Busy = 2"
| "code_source_ordinary_number Code_Source_Outcome_Unavailable = 3"

definition code_source_ordinary_result :: "code_source_outcome \<Rightarrow> (nat \<times> nat option)" where
  "code_source_ordinary_result observed =
    (code_source_ordinary_number (source_outcome_reply observed),source_outcome_commit observed)"

definition code_source_outcome_commit_matches :: "code_source_outcome \<Rightarrow> bool" where
  "code_source_outcome_commit_matches observed \<longleftrightarrow>
    ((source_outcome_commit observed \<noteq> None) =
      (code_source_ordinary_number (source_outcome_reply observed) \<in> {10..25}))"

lemma every_source_accepted_result_has_a_known_recorded_code:
  "code_source_accepted_number reply \<in> {1,2,3} \<union> {10..25}"
  by (cases reply) simp_all

lemma every_source_ordinary_result_has_a_known_recorded_code:
  "code_source_ordinary_number reply \<in> {1,2,3} \<union> {10..25}"
proof (cases reply)
  case (Code_Source_Accepted accepted)
  then show ?thesis by (cases accepted) simp_all
next
  case Code_Source_Duplicate_Decision
  then show ?thesis by simp
next
  case Code_Source_Duplicate_Confirmed
  then show ?thesis by simp
next
  case Code_Source_Duplicate_Reversed
  then show ?thesis by simp
next
  case Code_Source_Outcome_Rejected
  then show ?thesis by simp
next
  case Code_Source_Outcome_Busy
  then show ?thesis by simp
next
  case Code_Source_Outcome_Unavailable
  then show ?thesis by simp
qed

theorem a_source_ordinary_result_keeps_its_exact_commit_annotation:
  "snd (code_source_ordinary_result observed) = source_outcome_commit observed"
  by (simp add: code_source_ordinary_result_def)

theorem a_well_annotated_source_ordinary_result_uses_the_existing_recorded_table:
  assumes "code_source_outcome_commit_matches observed"
  shows "fst (code_source_ordinary_result observed) \<in>
    reference_result_codes Recorded_Result (snd (code_source_ordinary_result observed) \<noteq> None)"
  using assms every_source_ordinary_result_has_a_known_recorded_code[of "source_outcome_reply observed"]
  by (auto simp: code_source_ordinary_result_def code_source_outcome_commit_matches_def reference_result_codes_def; arith)

datatype code_source_legal_reply =
    Code_Source_Legal_Emitted nat | Code_Source_Legal_Applied nat
  | Code_Source_Legal_Blocked legal_refusal | Code_Source_Legal_Busy | Code_Source_Legal_Unavailable

fun code_source_legal_refusal_number :: "legal_refusal \<Rightarrow> nat" where
  "code_source_legal_refusal_number Invalid_Legal_Authority = 30"
| "code_source_legal_refusal_number Invalid_Legal_State = 31"
| "code_source_legal_refusal_number Invalid_Legal_Binding = 32"
| "code_source_legal_refusal_number Missing_Prior_Freeze = 33"
| "code_source_legal_refusal_number Missing_Prior_Seizure = 34"
| "code_source_legal_refusal_number Appeal_Still_Open = 35"
| "code_source_legal_refusal_number Appeal_Deadline_Mismatch = 36"
| "code_source_legal_refusal_number Missing_Confiscation_Destination = 37"
| "code_source_legal_refusal_number Conflicting_Legal_Order = 38"

fun code_source_legal_result :: "code_source_legal_reply \<Rightarrow> (nat \<times> nat option)" where
  "code_source_legal_result (Code_Source_Legal_Emitted position) = (26,Some position)"
| "code_source_legal_result (Code_Source_Legal_Applied position) = (27,Some position)"
| "code_source_legal_result (Code_Source_Legal_Blocked reason) = (code_source_legal_refusal_number reason,None)"
| "code_source_legal_result Code_Source_Legal_Busy = (2,None)"
| "code_source_legal_result Code_Source_Legal_Unavailable = (3,None)"

lemma a_source_legal_refusal_has_an_existing_uncommitted_result:
  "code_source_legal_refusal_number reason \<in> reference_result_codes Recorded_Result False"
  by (cases reason) (simp_all add: reference_result_codes_def)

theorem every_source_legal_result_has_the_existing_kind_and_commit_presence:
  "fst (code_source_legal_result reply) \<in>
    reference_result_codes Recorded_Result (snd (code_source_legal_result reply) \<noteq> None)"
proof (cases reply)
  case (Code_Source_Legal_Emitted position)
  then show ?thesis by (simp add: reference_result_codes_def)
next
  case (Code_Source_Legal_Applied position)
  then show ?thesis by (simp add: reference_result_codes_def)
next
  case (Code_Source_Legal_Blocked reason)
  then show ?thesis using a_source_legal_refusal_has_an_existing_uncommitted_result[of reason] by simp
next
  case Code_Source_Legal_Busy
  then show ?thesis by (simp add: reference_result_codes_def)
next
  case Code_Source_Legal_Unavailable
  then show ?thesis by (simp add: reference_result_codes_def)
qed

datatype code_source_spend_reply =
    Code_Source_Spend_Executed nat | Code_Source_Spend_Rejected | Code_Source_Spend_Busy | Code_Source_Spend_Unavailable

fun code_source_spend_result :: "code_source_spend_reply \<Rightarrow> (nat \<times> nat option)" where
  "code_source_spend_result (Code_Source_Spend_Executed position) = (28,Some position)"
| "code_source_spend_result Code_Source_Spend_Rejected = (1,None)"
| "code_source_spend_result Code_Source_Spend_Busy = (2,None)"
| "code_source_spend_result Code_Source_Spend_Unavailable = (3,None)"

theorem every_source_spend_result_has_the_existing_kind_and_commit_presence:
  "fst (code_source_spend_result reply) \<in>
    reference_result_codes Recorded_Result (snd (code_source_spend_result reply) \<noteq> None)"
  by (cases reply) (simp_all add: reference_result_codes_def)

datatype code_source_collection =
    Code_Source_Collected code_source_outcome | Code_Source_Collection_Waiting | Code_Source_Collection_Rejected

datatype code_source_receipt =
    Code_Source_Ordinary_Receipt code_source_collection
  | Code_Source_Legal_Receipt code_source_legal_reply
  | Code_Source_Spend_Receipt code_source_spend_reply

datatype code_source_action_reply =
    Code_Source_Ordinary_Collected code_source_outcome
  | Code_Source_Ordinary_Waiting | Code_Source_Ordinary_Busy | Code_Source_Ordinary_Unavailable | Code_Source_Ordinary_Rejected
  | Code_Source_Legal_Action code_source_legal_reply
  | Code_Source_Spend_Action code_source_spend_reply
  | Code_Source_Other_Action

fun code_source_without_matching_receipt :: "code_source_action_reply \<Rightarrow> (nat \<times> nat option)" where
  "code_source_without_matching_receipt Code_Source_Ordinary_Busy = (55,None)"
| "code_source_without_matching_receipt Code_Source_Ordinary_Unavailable = (56,None)"
| "code_source_without_matching_receipt (Code_Source_Legal_Action Code_Source_Legal_Busy) = (55,None)"
| "code_source_without_matching_receipt (Code_Source_Legal_Action Code_Source_Legal_Unavailable) = (56,None)"
| "code_source_without_matching_receipt (Code_Source_Spend_Action Code_Source_Spend_Busy) = (55,None)"
| "code_source_without_matching_receipt (Code_Source_Spend_Action Code_Source_Spend_Unavailable) = (56,None)"
| "code_source_without_matching_receipt (Code_Source_Legal_Action (Code_Source_Legal_Emitted position)) = (50,None)"
| "code_source_without_matching_receipt (Code_Source_Legal_Action (Code_Source_Legal_Applied position)) = (50,None)"
| "code_source_without_matching_receipt (Code_Source_Spend_Action (Code_Source_Spend_Executed position)) = (50,None)"
| "code_source_without_matching_receipt (Code_Source_Ordinary_Collected observed) = (50,None)"
| "code_source_without_matching_receipt Code_Source_Ordinary_Waiting = (50,None)"
| "code_source_without_matching_receipt reply = (77,None)"

fun code_source_from_received :: "code_source_action_reply \<Rightarrow> code_source_receipt option \<Rightarrow> (nat \<times> nat option)" where
  "code_source_from_received (Code_Source_Ordinary_Collected reply)
      (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected stored))) =
    (if reply = stored then code_source_ordinary_result stored
     else code_source_without_matching_receipt (Code_Source_Ordinary_Collected reply))"
| "code_source_from_received (Code_Source_Legal_Action reply) (Some (Code_Source_Legal_Receipt stored)) =
    (if reply = stored then code_source_legal_result stored
     else code_source_without_matching_receipt (Code_Source_Legal_Action reply))"
| "code_source_from_received (Code_Source_Spend_Action reply) (Some (Code_Source_Spend_Receipt stored)) =
    (if reply = stored then code_source_spend_result stored
     else code_source_without_matching_receipt (Code_Source_Spend_Action reply))"
| "code_source_from_received reply retained = code_source_without_matching_receipt reply"

lemma an_exact_ordinary_receipt_precedes_the_unresolved_fallback:
  "code_source_from_received (Code_Source_Ordinary_Collected observed)
      (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected observed))) = code_source_ordinary_result observed"
  by simp

lemma a_mismatched_ordinary_receipt_cannot_substitute_its_outcome:
  "observed \<noteq> stored \<Longrightarrow>
    code_source_from_received (Code_Source_Ordinary_Collected observed)
      (Some (Code_Source_Ordinary_Receipt (Code_Source_Collected stored))) = (50,None)"
  by simp

lemma a_matching_legal_busy_receipt_is_recorded_but_an_unretained_busy_is_delivery:
  "code_source_from_received (Code_Source_Legal_Action Code_Source_Legal_Busy)
      (Some (Code_Source_Legal_Receipt Code_Source_Legal_Busy)) = (2,None)"
  "code_source_from_received (Code_Source_Legal_Action Code_Source_Legal_Busy) None = (55,None)"
  by simp_all

datatype code_source_resolution =
    Code_Source_Resolution_Rejected | Code_Source_Resolution_Published code_source_receipt | Code_Source_Resolution_Unresolved

fun code_source_from_resolution :: "code_source_resolution \<Rightarrow> (nat \<times> nat option)" where
  "code_source_from_resolution Code_Source_Resolution_Rejected = (4,None)"
| "code_source_from_resolution (Code_Source_Resolution_Published
      (Code_Source_Ordinary_Receipt (Code_Source_Collected observed))) = code_source_ordinary_result observed"
| "code_source_from_resolution resolution = (50,None)"

datatype code_source_recovery_error =
    Code_Source_Publication_Unsupported | Code_Source_Publication_Deadline
  | Code_Source_Publication_TTL | Code_Source_Publication_Cancelled
  | Code_Source_Recovery_Endpoint_Rejected | Code_Source_Recovery_Endpoint_Unavailable
  | Code_Source_Recovery_Hold | Code_Source_Recovery_Other nat

datatype code_source_wire_error =
    Code_Source_Wire_Validation wire_refusal
  | Code_Source_Wire_Product_Rejected | Code_Source_Wire_Cancelled | Code_Source_Wire_Deadline
  | Code_Source_Wire_Response_Lost | Code_Source_Wire_Unresolved
  | Code_Source_Wire_Recovery code_source_recovery_error

fun code_source_error_number :: "code_source_wire_error \<Rightarrow> nat" where
  "code_source_error_number (Code_Source_Wire_Validation reason) = code_transport_refusal_number reason"
| "code_source_error_number Code_Source_Wire_Product_Rejected = 77"
| "code_source_error_number Code_Source_Wire_Cancelled = 53"
| "code_source_error_number Code_Source_Wire_Deadline = 52"
| "code_source_error_number Code_Source_Wire_Response_Lost = 51"
| "code_source_error_number Code_Source_Wire_Unresolved = 50"
| "code_source_error_number (Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Rejected) = 77"
| "code_source_error_number (Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Unavailable) = 56"
| "code_source_error_number (Code_Source_Wire_Recovery other) = 50"

definition code_source_error_result where
  "code_source_error_result error = (code_source_error_number error,None::nat option)"

lemma every_source_wire_validation_error_has_a_known_uncommitted_status:
  "code_transport_refusal_number reason \<in>
    reference_result_codes Delivery_Refusal False \<union> reference_result_codes Validation_Refusal False"
  by (cases reason) (simp_all add: reference_result_codes_def)

theorem every_source_error_response_is_known_and_uncommitted:
  "code_source_error_number error \<in>
    reference_result_codes Delivery_Refusal False \<union> reference_result_codes Validation_Refusal False"
  "snd (code_source_error_result error) = None"
proof -
  show "code_source_error_number error \<in>
      reference_result_codes Delivery_Refusal False \<union> reference_result_codes Validation_Refusal False"
  proof (cases error)
    case (Code_Source_Wire_Validation reason)
    then show ?thesis using every_source_wire_validation_error_has_a_known_uncommitted_status[of reason] by simp
  next
    case Code_Source_Wire_Product_Rejected
    then show ?thesis by (simp add: reference_result_codes_def)
  next
    case Code_Source_Wire_Cancelled
    then show ?thesis by (simp add: reference_result_codes_def)
  next
    case Code_Source_Wire_Deadline
    then show ?thesis by (simp add: reference_result_codes_def)
  next
    case Code_Source_Wire_Response_Lost
    then show ?thesis by (simp add: reference_result_codes_def)
  next
    case Code_Source_Wire_Unresolved
    then show ?thesis by (simp add: reference_result_codes_def)
  next
    case (Code_Source_Wire_Recovery recovery)
    then show ?thesis by (cases recovery) (simp_all add: reference_result_codes_def)
  qed
  show "snd (code_source_error_result error) = None" by (simp add: code_source_error_result_def)
qed

definition code_source_outcome_projection :: "code_source_outcome \<Rightarrow> product_outcome option" where
  "code_source_outcome_projection observed =
    (case source_outcome_reply observed of
       Code_Source_Accepted Code_Source_Debited_Reply \<Rightarrow> Some (Authority_Reply (Protocol_Response Source_Debited))
     | Code_Source_Accepted Code_Source_Rejected_Reply \<Rightarrow> Some Authority_Rejected
     | Code_Source_Accepted Code_Source_Busy_Reply \<Rightarrow> Some Authority_Busy
     | Code_Source_Outcome_Rejected \<Rightarrow> Some Authority_Rejected
     | Code_Source_Outcome_Busy \<Rightarrow> Some Authority_Busy
     | Code_Source_Outcome_Unavailable \<Rightarrow> Some Authority_Unavailable
     | _ \<Rightarrow> None)"

definition code_source_debit_commit_annotation :: "code_source_outcome \<Rightarrow> product_call_payload \<Rightarrow> bool" where
  "code_source_debit_commit_annotation observed payload \<longleftrightarrow>
    source_outcome_reply observed = Code_Source_Accepted Code_Source_Debited_Reply \<and>
    source_outcome_commit observed = Some (cut_revision (envelope_cut (payload_envelope payload)))"

theorem an_annotated_source_debit_has_the_exact_existing_payload_position:
  assumes "code_source_debit_commit_annotation observed payload"
  shows "code_source_outcome_projection observed = Some (Authority_Reply (Protocol_Response Source_Debited))"
    "code_source_ordinary_result observed = (12,Some (cut_revision (envelope_cut (payload_envelope payload))))"
  using assms by (auto simp: code_source_debit_commit_annotation_def code_source_outcome_projection_def code_source_ordinary_result_def)

text \<open>
  Source: authority.rs Outcome/CommitRef and response.rs ResponseResult.
  These are fresh source observation types: the frozen product_outcome does
  not contain duplicate-result variants or a commit-position observation.
  The projection above is explicitly partial. A commit annotation preserves
  supplied source data; no theorem here establishes that a supplied position
  is the actual retained commit. The product/trace consumer and actual Rust
  retained-receipt evidence must establish that separate relation.
  The legal source variants retain Emitted/Applied and Busy/Unavailable;
  they are not silently equated with Legal_Checked in the old product model.
\<close>

end

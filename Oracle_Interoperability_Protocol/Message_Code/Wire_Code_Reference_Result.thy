theory Wire_Code_Reference_Result
  imports Wire_Code_Response_Outcome Wire_Code_Reference_Publication
begin

fun code_source_transaction_error :: "code_source_recovery_error \<Rightarrow> code_source_wire_error option \<Rightarrow> code_source_wire_error" where
  "code_source_transaction_error Code_Source_Publication_Unsupported saved = Code_Source_Wire_Recovery Code_Source_Recovery_Hold"
| "code_source_transaction_error Code_Source_Publication_Deadline saved = Code_Source_Wire_Deadline"
| "code_source_transaction_error Code_Source_Publication_TTL saved = Code_Source_Wire_Validation Wire_TTL_Expired"
| "code_source_transaction_error Code_Source_Publication_Cancelled saved = Code_Source_Wire_Cancelled"
| "code_source_transaction_error recovery saved =
    (case saved of Some error \<Rightarrow> error | None \<Rightarrow> Code_Source_Wire_Recovery recovery)"

datatype 'reply code_source_transaction =
    Code_Source_Transaction_Recovery code_source_recovery_error
  | Code_Source_Transaction_Error code_source_wire_error
  | Code_Source_Transaction_Done 'reply

fun code_source_finish_received_transaction :: "code_source_wire_error option \<Rightarrow> bool \<Rightarrow> 'reply code_source_transaction \<Rightarrow> (code_source_wire_error + 'reply)" where
  "code_source_finish_received_transaction saved response_lost (Code_Source_Transaction_Recovery recovery) =
    Inl (code_source_transaction_error recovery saved)"
| "code_source_finish_received_transaction saved response_lost (Code_Source_Transaction_Error error) = Inl error"
| "code_source_finish_received_transaction saved response_lost (Code_Source_Transaction_Done reply) =
    (if response_lost then Inl Code_Source_Wire_Response_Lost else Inr reply)"

lemma source_publication_refusal_classes_precede_a_saved_guard_error:
  "code_source_transaction_error Code_Source_Publication_Unsupported saved = Code_Source_Wire_Recovery Code_Source_Recovery_Hold"
  "code_source_transaction_error Code_Source_Publication_Deadline saved = Code_Source_Wire_Deadline"
  "code_source_transaction_error Code_Source_Publication_TTL saved = Code_Source_Wire_Validation Wire_TTL_Expired"
  "code_source_transaction_error Code_Source_Publication_Cancelled saved = Code_Source_Wire_Cancelled"
  by simp_all

lemma a_saved_guard_refusal_survives_an_unclassified_transaction_hold:
  "code_source_transaction_error Code_Source_Recovery_Hold (Some error) = error"
  by simp

lemma a_product_error_precedes_the_postcommit_response_lost_flag:
  "code_source_finish_received_transaction saved response_lost (Code_Source_Transaction_Error error) = Inl error"
  by simp

lemma a_lost_response_is_classified_only_after_a_successful_transaction:
  "code_source_finish_received_transaction saved True (Code_Source_Transaction_Done reply) = Inl Code_Source_Wire_Response_Lost"
  "code_source_finish_received_transaction saved False (Code_Source_Transaction_Done reply) = Inr reply"
  by simp_all

definition code_finish_wire_result ::
  "code_source_wire_error option \<Rightarrow> bool \<Rightarrow>
    ('head reference_product_image \<times> 'reply code_source_transaction) \<Rightarrow>
    ('head reference_product_image \<times> (code_source_wire_error + 'reply))" where
  "code_finish_wire_result saved response_lost transaction =
    (let (committed,result) = transaction in
     (committed,code_source_finish_received_transaction saved response_lost result))"

theorem source_result_classification_preserves_the_transaction_selected_state:
  "fst (code_finish_wire_result saved response_lost transaction) = fst transaction"
  by (simp add: code_finish_wire_result_def Let_def split: prod.splits)

lemma a_publication_deadline_becomes_delivery_status_fifty_two:
  "code_source_error_result (code_source_transaction_error Code_Source_Publication_Deadline saved) = (52,None)"
  by (simp add: code_source_error_result_def)

lemma a_saved_product_refusal_is_not_replaced_by_an_unsigned_generic_hold:
  "code_source_error_result (code_source_transaction_error Code_Source_Recovery_Hold
      (Some Code_Source_Wire_Product_Rejected)) = (77,None)"
  by (simp add: code_source_error_result_def)

text \<open>
  Source: wire.rs receive_wire_result, its outer RecoveryError mapping,
  inner Result propagation and post-transaction response_lost check.
  The transaction argument is an actual selected-state/result observation;
  this classifier does not assume that an arbitrary candidate was committed.
  The existing product publication consumer must establish that provenance.
  Outcome-to-code conversion is separate from transaction state transition.
\<close>

end

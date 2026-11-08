theory Reference_Secondary_Provider
  imports "Reference_Queue_Consumption"
begin

definition reference_delivered_ack where
  "reference_delivered_ack receiver verify_ack ack \<longleftrightarrow>
    receiver (ack_settlement_key ack) = Some ack \<and> verify_ack ack"

lemma a_receiver_record_for_another_result_cannot_verify_the_ack:
  assumes "receiver (ack_settlement_key ack) \<noteq> Some ack"
  shows "\<not> reference_delivered_ack receiver verify_ack ack"
  using assms by (simp add: reference_delivered_ack_def)

context source_attestation
begin

theorem a_verified_receiver_record_completes_only_the_exact_secondary_job:
  assumes service: "service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered
    (reference_delivered_ack receiver verify_ack) authenticated connection
    (Service_Maintenance (Exact_Acknowledge ack)) supplied before = (after, Some reply)"
    and job: "settlement_jobs (reference_queue_at connection before) (ack_settlement_key ack) = Some job"
    and exact: "exact_secondary_ack ack job" and attempts: "secondary_attempts job > 0"
    and accepted: "receiver (ack_settlement_key ack) = Some ack" "verify_ack ack"
  shows "retained_secondary (reference_product after) (ack_settlement_key ack) =
      Some (job\<lparr>secondary_state := Secondary_Completed\<rparr>)"
    "retained_source (reference_product after) = retained_source (reference_product before)"
proof -
  have verified: "reference_delivered_ack receiver verify_ack ack"
    using accepted by (simp add: reference_delivered_ack_def)
  show "retained_secondary (reference_product after) (ack_settlement_key ack) =
      Some (job\<lparr>secondary_state := Secondary_Completed\<rparr>)"
    "retained_source (reference_product after) = retained_source (reference_product before)"
    by (rule the_actual_reference_service_completes_only_the_verified_ack_job[OF service job exact verified attempts])+
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms a_receiver_record_for_another_result_cannot_verify_the_ack
      source_attestation.a_verified_receiver_record_completes_only_the_exact_secondary_job})
  then () else error "Unexpected oracle in reference secondary provider"
\<close>

end

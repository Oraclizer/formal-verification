theory Recovery_Simulation
  imports Recovery_Service
begin

section \<open>Equality of replies and retained effects for the exposed action language\<close>

context source_attestation
begin

lemma equal_retained_records_give_the_same_served_step:
  assumes "capture_retained_product s = capture_retained_product t"
  shows "serve_durable_projection directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection action s =
    serve_durable_projection directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection action t"
  using assms by (simp add: serve_durable_projection_def)

fun run_served_trace where
  "run_served_trace directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack [] s =
    (capture_retained_product s, [])"
| "run_served_trace directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
    ((connection, action) # rest) s =
    (let result = serve_durable_projection directory policy read_policy authenticate verify verify_read endorse approve
          legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
          connection action s;
         later = run_served_trace directory policy read_policy authenticate verify verify_read endorse approve
          legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
          rest (fst result)
     in (fst later, snd result # snd later))"

lemma equal_retained_records_preserve_all_future_service_replies_and_effects:
  assumes "capture_retained_product s = capture_retained_product t"
  shows "run_served_trace directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack actions s =
    run_served_trace directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack actions t"
proof (cases actions)
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons first later)
  obtain connection action where first: "first = (connection, action)" by (cases first)
  show ?thesis
    unfolding Cons first
    using equal_retained_records_give_the_same_served_step[OF assms, of directory policy read_policy authenticate verify verify_read
      endorse approve legal_grant order_verified spend_grant spend_verified read_permitted permitted verified
      maintainers registered verified_ack connection action]
    by (simp only: run_served_trace.simps Let_def)
qed

theorem authenticated_records_only_recovery_is_a_forward_simulation:
  assumes anchor: "committed_head disk = Some (head_for_record digest record)"
    and flushed: "flushed_records disk (head_for_record digest record) = Some record"
    and attachment: "attachment_profile current = image_profile record"
    and recorded: "image_records record = capture_retained_product live"
  obtains restored where "reopen_from_authenticated_head digest (image_profile record) (Some current) disk = Some restored"
    "capture_retained_product restored = capture_retained_product live"
    "run_served_trace directory policy read_policy authenticate verify verify_read endorse approve
       legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack actions restored =
     run_served_trace directory policy read_policy authenticate verify verify_read endorse approve
       legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack actions live"
proof -
  let ?restored = "reopen_retained_product (attachment_connection current) (image_records record)"
  have open_result: "reopen_from_authenticated_head digest (image_profile record) (Some current) disk = Some ?restored"
    by (rule independently_anchored_records_construct_a_fresh_endpoint[OF anchor flushed attachment])
  have projection: "capture_retained_product ?restored = capture_retained_product live"
    using recorded by (simp add: product_round_trip_preserves_the_durable_projection)
  show thesis
    by (rule that[OF open_result projection equal_retained_records_preserve_all_future_service_replies_and_effects[OF projection]])
qed

end

end

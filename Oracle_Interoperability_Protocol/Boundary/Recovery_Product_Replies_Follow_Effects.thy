theory Recovery_Product_Replies_Follow_Effects
  imports Recovery_Scheduled_Product_Reply_Pairs
begin

context source_attestation
begin

theorem scheduled_product_replies_follow_their_retained_effects:
  "replies_follow_effects (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack)"
  unfolding replies_follow_effects_def
proof (intro allI impI)
  fix connection_a action_a connection_b action_b R
  assume changed: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection_a action_a R) \<noteq> R"
  assume same: "fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection_a action_a R) =
    fst (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection_b action_b R)"
  show "snd (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection_a action_a R) =
    snd (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack connection_b action_b R)"
    by (rule equal_changed_scheduled_product_images_determine_the_reply[OF refl refl changed same])
qed

end

text \<open>This is the unweakened global property for the frozen scheduled retained step.
  No reachable-state, equal-action, equal-connection, digest, witness or response-order premise
  is added. It is not a theorem about signed wire-envelope bytes or an identification with the
  live preparation step. Source existence is not a kernel completion receipt.\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.scheduled_product_replies_follow_their_retained_effects})
  then () else error "Unexpected oracle in full scheduled product replies-follow-effects"
\<close>

end

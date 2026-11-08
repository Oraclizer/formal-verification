theory Recovery_Request_Provenance_Product
  imports Recovery_Request_Provenance_Run
begin

text \<open>This instance uses the scheduled retained-state step, not an implicit identification
  with live_product_service_step or compiled code. The source-attestation locale is inherited by
  the financial contract. Address injectivity and reply determinacy are not state-provenance premises.\<close>

context source_attestation
begin

theorem a_reopened_product_image_has_request_provenance_and_keeps_the_reservation_contract:
  fixes execute :: "authority_connection \<Rightarrow> 'token retained_service_action \<Rightarrow>
    retained_product \<Rightarrow> retained_product \<times> scheduled_service_reply"
    and directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
  defines "execute \<equiv> schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack"
  assumes run: "s = fold (boundary_step execute digest profile) events
      (genesis_system digest profile (initial_promotable_product balances regulatory contexts durable target provider))"
    and reopened: "witnessed_reopen digest profile attachment (sys_disk s) (sys_witness s) = Some (h, R)"
  shows "\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
      R = run_product_action_word execute word
        (initial_promotable_product balances regulatory contexts durable target provider)"
    and "reservation_contract balances (core_parent (retained_core (retained_source R)))"
    and "product_source_mass (core_parent (retained_core (retained_source R))) account = int (balances account)"
proof -
  obtain word where requested: "requested_subsequence word (actual_ask_word events)"
    and image: "R = run_product_action_word execute word
      (initial_promotable_product balances regulatory contexts durable target provider)"
    using every_retained_image_has_an_actual_ask_subsequence_witness(1)[OF run reopened] by blast
  show "\<exists>word. requested_subsequence word (actual_ask_word events) \<and>
      R = run_product_action_word execute word
        (initial_promotable_product balances regulatory contexts durable target provider)"
    using requested image by blast
  show contract: "reservation_contract balances (core_parent (retained_core (retained_source R)))"
    unfolding image execute_def by (rule every_actual_product_word_preserves_the_public_source_reservation_contract)
  show "product_source_mass (core_parent (retained_core (retained_source R))) account = int (balances account)"
    by (rule a_public_reservation_contract_conserves_the_product_source_pool[OF contract])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      source_attestation.a_reopened_product_image_has_request_provenance_and_keeps_the_reservation_contract})
  then () else error "Unexpected oracle in request-provenance product instance"
\<close>

end

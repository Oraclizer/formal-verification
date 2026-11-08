theory Promotion_Source_Pool_Examples
  imports "../Promotion_Source_Pool" Identity_Examples
begin

context source_attestation
begin

abbreviation after_the_pool_case_handover where
  "after_the_pool_case_handover \<equiv>
    handover_product_owner identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
      (\<lambda>_ _. True) 7 8 99 {99} {0,2} handover_case_proposal handover_case_world"

lemma pool_case_handover_is_authorized:
  "handover_is_authorized identity_case_directory (\<lambda>_ _ _ _ _. True) identity_case_directory
    (\<lambda>_ _. True) 7 8 99 {99} {0,2} handover_case_proposal (identity_source handover_case_world)"
  unfolding identity_case_has_the_actual_source by (rule handover_case_is_admitted)

lemma real_pending_source_pool_and_its_old_prefix_survive_handover:
  "source_units (authoritative_reservation_state (identity_source after_the_pool_case_handover)) (0,17) = 5 \<and>
    authority_prefix_snapshot 0 (read_authority (regulated_read_world after_the_pool_case_handover)) =
    authority_prefix_snapshot 0 (read_authority (regulated_read_world handover_case_world))"
proof -
  have five: "source_units (authoritative_reservation_state (identity_source handover_case_world)) (0,17) = 5"
    unfolding identity_case_has_the_actual_source
    using source_debit_puts_five_into_pending
    by (simp add: authoritative_reservation_state_def handover_case_defs)
  have same: "source_units (authoritative_reservation_state (identity_source after_the_pool_case_handover)) (0,17) = 5"
    using registry_owner_handover_does_not_rebind_the_authoritative_source_pool[OF pool_case_handover_is_authorized, of "(0,17)"] five
    by (simp add: Let_def)
  have old: "authority_prefix_snapshot 0 (read_authority (regulated_read_world after_the_pool_case_handover)) =
    authority_prefix_snapshot 0 (read_authority (regulated_read_world handover_case_world))"
    by (rule the_named_authority_prefix_survives_registry_owner_handover[OF pool_case_handover_is_authorized]) simp
  show ?thesis using same old by simp
qed

end

lemma rebinding_to_the_current_owner_changes_a_value_without_moving_funds:
  "let balances = (\<lambda>_. 0)(7 := (10::nat));
       previous_owner = (7::nat); successor = 8
   in balances previous_owner = 10 \<and> balances successor = 0 \<and> balances previous_owner \<noteq> balances successor"
  by (simp add: Let_def)

end

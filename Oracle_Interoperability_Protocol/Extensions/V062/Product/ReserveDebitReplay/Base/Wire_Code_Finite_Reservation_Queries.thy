theory Wire_Code_Finite_Reservation_Queries
  imports Wire_Code_Finite_Financial_State
begin

definition code_finite_binding_registered :: "code_finite_financial_state \<Rightarrow> transfer_binding \<Rightarrow> bool" where
  "code_finite_binding_registered financial binding =
    (case map_of (finite_reservations financial) (binding_key binding) of
       None \<Rightarrow> False | Some stored \<Rightarrow> reservation_binding stored = binding)"

definition code_finite_owns_recorded :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> code_finite_financial_state \<Rightarrow> bool" where
  "code_finite_owns_recorded authority_view request generation versions financial =
    (current_use_allowed (lock_authority authority_view) request \<and>
      (case map_of (finite_reservations financial) (binding_key (request_binding request)) of None \<Rightarrow> False
       | Some stored \<Rightarrow> reservation_binding stored = request_binding request \<and>
         reservation_worker stored = request_caller request \<and> reservation_generation stored = generation \<and>
         finite_clock financial < reservation_deadline stored \<and> active_reservation_phase (reservation_phase stored) \<and>
         list_all (\<lambda>asset. map_of (finite_asset_owners financial) asset = Some (binding_key (request_binding request)) \<and>
           versions asset = code_finite_nat_default (finite_asset_versions financial) asset) (reservation_footprint stored)))"

definition code_finite_owns_current :: "lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<Rightarrow> nat) \<Rightarrow> code_finite_financial_state \<Rightarrow> bool" where
  "code_finite_owns_current authority_view request generation versions financial =
    (code_finite_owns_recorded authority_view request generation versions financial \<and>
      (case map_of (finite_reservations financial) (binding_key (request_binding request)) of None \<Rightarrow> True
       | Some stored \<Rightarrow> set (reservation_footprint stored) = set (required_footprint authority_view (request_binding request))))"

lemma finite_registration_query_is_the_exact_existing_registered_binding_test:
  "code_finite_binding_registered financial binding = binding_is_registered (code_interpret_finite_financial financial) binding"
  by (cases "map_of (finite_reservations financial) (binding_key binding)")
     (auto simp: code_finite_binding_registered_def binding_is_registered_def code_interpret_finite_financial_def)

lemma finite_recorded_ownership_is_the_exact_existing_current_claim:
  "code_finite_owns_recorded authority_view request generation versions financial =
    owns_recorded_reservation authority_view request generation versions (code_interpret_finite_financial financial)"
  by (cases "map_of (finite_reservations financial) (binding_key (request_binding request))")
     (auto simp: code_finite_owns_recorded_def owns_recorded_reservation_def code_interpret_finite_financial_def list_all_iff)

lemma finite_current_ownership_is_the_exact_existing_current_footprint_test:
  "code_finite_owns_current authority_view request generation versions financial =
    owns_current_reservation authority_view request generation versions (code_interpret_finite_financial financial)"
  by (cases "map_of (finite_reservations financial) (binding_key (request_binding request))")
     (auto simp: code_finite_owns_current_def owns_current_reservation_def
       finite_recorded_ownership_is_the_exact_existing_current_claim code_interpret_finite_financial_def)

lemma the_finite_ownership_query_rejects_an_absent_reservation:
  assumes "map_of (finite_reservations financial) (binding_key (request_binding request)) = None"
  shows "\<not> code_finite_owns_current authority_view request generation versions financial"
  using assms by (simp add: code_finite_owns_current_def code_finite_owns_recorded_def)

text \<open>
  The two unbounded old quantifiers over a uniquely selected reservation
  become option cases. The footprint quantifier becomes list_all over that
  actual finite footprint. Nothing is strengthened to an extra successful
  ownership premise. The equalities include absence and default-zero asset
  versions, and keep current_use/lease/generation/active/footprint checks.
\<close>

end

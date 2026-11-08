theory Wire_Service_Window
  imports Wire_Product_Execution
begin

record delivery_window =
  delivery_cancelled :: bool
  delivery_service_deadline :: "nat option"

definition delivery_window_open where
  "delivery_window_open now window \<longleftrightarrow>
    \<not> delivery_cancelled window \<and>
    (case delivery_service_deadline window of None \<Rightarrow> True | Some deadline \<Rightarrow> now \<le> deadline)"

context source_attestation
begin

definition consume_wire_before_service_deadline where
  "consume_wire_before_service_deadline window verify_signature source_verified body_allowed authority decode run bytes cache retained =
    (if delivery_window_open (boundary_now authority) window
     then consume_wire_in_current_product verify_signature source_verified body_allowed authority decode run bytes cache retained
     else (cache, retained, None))"

lemma precommit_cancellation_cannot_create_a_wire_binding_or_product_effect:
  assumes "delivery_cancelled window"
  shows "consume_wire_before_service_deadline window verify_signature source_verified body_allowed authority decode run bytes cache retained =
    (cache, retained, None)"
  using assms by (simp add: consume_wire_before_service_deadline_def delivery_window_open_def)

lemma service_deadline_expiration_leaves_the_exact_current_state:
  assumes "delivery_service_deadline window = Some deadline" "deadline < boundary_now authority"
  shows "consume_wire_before_service_deadline window verify_signature source_verified body_allowed authority decode run bytes cache retained =
    (cache, retained, None)"
  using assms by (simp add: consume_wire_before_service_deadline_def delivery_window_open_def)

end

end

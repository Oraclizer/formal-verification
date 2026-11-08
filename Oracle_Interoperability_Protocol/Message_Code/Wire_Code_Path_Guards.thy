theory Wire_Code_Path_Guards
  imports Wire_Code_Admission "OIP_Product.Wire_Service_Window"
begin

datatype code_path_refusal =
    Code_Path_Validation wire_refusal
  | Code_Path_Cancelled
  | Code_Path_Deadline_Expired
  | Code_Path_Unresolved
  | Code_Path_Product_Rejected
  | Code_Path_Response_Lost

definition code_matches_signed_packet where
  "code_matches_signed_packet bytes credential_signature \<longleftrightarrow> bytes = credential_signature"

lemma the_dispatcher_packet_identity_test_is_not_a_cryptographic_signature_test:
  "code_matches_signed_packet packet packet"
  by (simp add: code_matches_signed_packet_def)

definition code_gate_delivery where
  "code_gate_delivery window now strict =
    (if delivery_cancelled window then Some Code_Path_Cancelled
     else if strict \<and> (case delivery_service_deadline window of None \<Rightarrow> False
        | Some deadline \<Rightarrow> now > deadline)
     then Some Code_Path_Deadline_Expired else None)"

lemma the_nonordered_delivery_guard_has_the_existing_service_window:
  "code_gate_delivery window now True = None \<longleftrightarrow> delivery_window_open now window"
  by (cases "delivery_service_deadline window")
    (auto simp: code_gate_delivery_def delivery_window_open_def)

lemma the_ordered_delivery_guard_does_not_recheck_the_service_deadline:
  "\<not> delivery_cancelled window \<Longrightarrow> code_gate_delivery window now False = None"
  by (simp add: code_gate_delivery_def)

lemma explicit_cancellation_precedes_a_service_deadline_refusal:
  "delivery_cancelled window \<Longrightarrow> code_gate_delivery window now strict = Some Code_Path_Cancelled"
  by (simp add: code_gate_delivery_def)

record code_channel_guard =
  guard_channel_version :: nat
  guard_channel_deployment :: nat
  guard_channel_local :: nat
  guard_channel_remote :: nat
  guard_channel_expires :: nat
  guard_channel_peer_key :: wire_bytes
  guard_channel_current :: bool

definition code_boundary_at where
  "code_boundary_at selected channel deployment (current_cut::product_cut) admitted_at legacy_configured =
    (case selected of None \<Rightarrow> Inl (Code_Path_Validation Invalid_Wire_Source)
     | Some (scope,public_key) \<Rightarrow>
       if \<not> guard_channel_current channel \<or> public_key \<noteq> guard_channel_peer_key channel \<or>
          guard_channel_deployment channel \<noteq> deployment \<or> boundary_deployment scope \<noteq> deployment \<or>
          (case admitted_at of None \<Rightarrow> boundary_now scope | Some time \<Rightarrow> time) > guard_channel_expires channel \<or>
          boundary_source scope \<noteq> guard_channel_remote channel \<or>
          boundary_target scope \<noteq> guard_channel_local channel \<or>
          boundary_epoch scope \<noteq> cut_authority_epoch current_cut
       then Inl (Code_Path_Validation Invalid_Wire_Source)
       else if guard_channel_version channel = 5 \<and> \<not> legacy_configured
       then Inl (Code_Path_Validation Unsupported_Wire_Version)
       else Inr (scope,public_key))"

theorem every_source_boundary_uses_the_channel_peer_key_and_exact_live_cut:
  assumes "code_boundary_at selected channel deployment current_cut admitted_at legacy_configured = Inr (scope,public_key)"
  shows "public_key = guard_channel_peer_key channel"
    "boundary_epoch scope = cut_authority_epoch current_cut"
    "boundary_source scope = guard_channel_remote channel"
    "boundary_target scope = guard_channel_local channel"
    "boundary_deployment scope = deployment"
    "guard_channel_deployment channel = deployment"
    "guard_channel_current channel"
    "(case admitted_at of None \<Rightarrow> boundary_now scope | Some time \<Rightarrow> time) \<le> guard_channel_expires channel"
  using assms
  by (auto simp: code_boundary_at_def split: option.splits prod.splits if_splits)

lemma the_two_source_signature_checks_use_identical_key_bytes_after_boundary_admission:
  assumes "code_boundary_at selected channel deployment current_cut admitted_at legacy_configured = Inr (scope,public_key)"
  shows "verify public_key message signature = verify (guard_channel_peer_key channel) message signature"
  using every_source_boundary_uses_the_channel_peer_key_and_exact_live_cut(1)[OF assms] by simp

lemma a_different_selected_key_is_a_source_refusal_before_any_product_consumer:
  assumes "public_key \<noteq> guard_channel_peer_key channel"
  shows "code_boundary_at (Some (scope,public_key)) channel deployment current_cut admitted_at legacy_configured =
    Inl (Code_Path_Validation Invalid_Wire_Source)"
  using assms by (simp add: code_boundary_at_def)

lemma ordered_publication_can_reuse_its_admission_time_without_retesting_a_later_clock:
  assumes "guard_channel_current channel" "public_key = guard_channel_peer_key channel"
    "guard_channel_deployment channel = deployment" "boundary_deployment scope = deployment"
    "time \<le> guard_channel_expires channel" "boundary_source scope = guard_channel_remote channel"
    "boundary_target scope = guard_channel_local channel" "boundary_epoch scope = cut_authority_epoch current_cut"
    "guard_channel_version channel \<noteq> 5"
  shows "code_boundary_at (Some (scope,public_key)) channel deployment current_cut (Some time) legacy_configured =
    Inr (scope,public_key)"
  using assms by (simp add: code_boundary_at_def)

end

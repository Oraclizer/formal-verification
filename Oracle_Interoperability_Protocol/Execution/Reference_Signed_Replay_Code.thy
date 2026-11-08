theory Reference_Signed_Replay_Code
  imports Reference_Signed_Replay_Data Reference_Read_Code "OIP_Reference_Profile.Reference_Product_Image"
begin

record ('raw, 'head) rust_replay_image =
  rust_replay_bindings :: wire_dedup_store
  rust_replay_selected_head :: "'head option"
  rust_replay_order :: nat
  rust_replay_product :: 'raw

definition rust_replay_check where
  "rust_replay_check exact_check admission head code =
    (case admission of Gate_Refused reason \<Rightarrow> (code,Wire_Rejected reason)
     | Gate_Admitted packet \<Rightarrow> let core = packet_core packet; exact = encode_wire_core core;
          key = authenticated_wire_message_id core in
       case rust_replay_bindings code key of None \<Rightarrow>
         (code\<lparr>rust_replay_bindings := (rust_replay_bindings code)(key := Some exact),
           rust_replay_selected_head := Some head, rust_replay_order := Suc (rust_replay_order code)\<rparr>,Wire_First packet)
       | Some before \<Rightarrow> if \<not> exact_check \<or> before = exact then (code,Wire_Identical packet)
         else (code,Wire_Rejected Conflicting_Wire_Replay))"

definition rust_replay_image_matches where
  "rust_replay_image_matches relate code frame \<longleftrightarrow>
    rust_replay_bindings code = image_transport frame \<and> rust_replay_selected_head code = control_head (image_ordered_control frame) \<and>
    rust_replay_order code = control_revision (image_ordered_control frame) \<and> relate (rust_replay_product code) (image_authority frame)"

definition commit_reference_query_binding where
  "commit_reference_query_binding before after candidate frame =
    (if after = before then frame
     else frame\<lparr>image_transport := after, image_ordered_control := (image_ordered_control frame)\<lparr>
       control_head := Some candidate, control_revision := Suc (control_revision (image_ordered_control frame))\<rparr>\<rparr>)"

theorem the_rust_exact_replay_guard_matches_the_reference_wire_state_head_and_response:
  assumes state: "rust_replay_image_matches relate code frame"
  shows "let native = rust_replay_check True (wire_gate verify attest body_allowed scope bytes) head code;
       model = receive_canonical_wire verify attest body_allowed scope bytes (image_transport frame)
    in rust_replay_image_matches relate (fst native)
        (commit_reference_query_binding (image_transport frame) (fst model) head frame) \<and> snd native = snd model"
proof -
  have bindings: "rust_replay_bindings code = image_transport frame"
    using state by (simp add: rust_replay_image_matches_def)
  show ?thesis
  proof (cases "wire_gate verify attest body_allowed scope bytes")
    case (Gate_Refused reason)
    show ?thesis using state
      by (simp only: Let_def rust_replay_check_def receive_canonical_wire_def Gate_Refused)
         (simp add: commit_reference_query_binding_def)
  next
    case (Gate_Admitted packet)
    let ?key = "authenticated_wire_message_id (packet_core packet)"
    let ?exact = "encode_wire_core (packet_core packet)"
    show ?thesis
    proof (cases "image_transport frame ?key")
      case None
      have changed: "(image_transport frame)(?key := Some ?exact) \<noteq> image_transport frame"
      proof
        assume "(image_transport frame)(?key := Some ?exact) = image_transport frame"
        then have "Some ?exact = image_transport frame ?key" by (metis fun_upd_same)
        with None show False by simp
      qed
      show ?thesis using state
        by (simp only: Let_def rust_replay_check_def receive_canonical_wire_def Gate_Admitted)
           (simp add: bindings None changed commit_reference_query_binding_def rust_replay_image_matches_def Let_def)
    next
      case (Some prior)
      show ?thesis using state
        by (simp only: Let_def rust_replay_check_def receive_canonical_wire_def Gate_Admitted)
           (simp add: bindings Some commit_reference_query_binding_def Let_def split: if_splits)
    qed
  qed
qed

definition current_query_from_replay where
  "current_query_from_replay token arrival =
    (let invocation = case arrival of Wire_First packet \<Rightarrow> decoded_wire_read_action token (packet_core packet)
           | Wire_Identical packet \<Rightarrow> decoded_wire_read_action token (packet_core packet)
           | Wire_Rejected _ \<Rightarrow> None in
      case invocation of Some (Invoke_Authenticated_Read _ session target (Current_Data query expected)) \<Rightarrow>
        Some (session,target,query,expected)
      | _ \<Rightarrow> None)"

theorem a_selected_signed_current_query_uses_the_same_cut_and_value_on_both_sides:
  fixes native model verify attest body_allowed scope bytes head
  assumes transport: "rust_replay_image_matches relate code frame"
    and history: "native_read_history_related epoch revision prefixes (image_read_history frame)"
  defines "native \<equiv> rust_replay_check True (wire_gate verify attest body_allowed scope bytes) head code"
    and "model \<equiv> receive_canonical_wire verify attest body_allowed scope bytes (image_transport frame)"
  shows "current_query_from_replay token (snd native) = current_query_from_replay token (snd model)"
    "current_query_from_replay token (snd native) = Some (session,target,query,expected) \<Longrightarrow>
      native_current_read_value (allowed session target query expected) (stored_query query) expected epoch revision prefixes =
      current_reference_observation (allowed session target query expected) (stored_query query) expected (image_read_history frame)"
proof -
  show "current_query_from_replay token (snd native) = current_query_from_replay token (snd model)"
    using the_rust_exact_replay_guard_matches_the_reference_wire_state_head_and_response
      [OF transport, where verify=verify and attest=attest and body_allowed=body_allowed and scope=scope and bytes=bytes and head=head]
    by (simp add: native_def model_def Let_def)
  show "current_query_from_replay token (snd native) = Some (session,target,query,expected) \<Longrightarrow>
      native_current_read_value (allowed session target query expected) (stored_query query) expected epoch revision prefixes =
      current_reference_observation (allowed session target query expected) (stored_query query) expected (image_read_history frame)"
    by (rule the_native_cut_and_its_selected_prefixes_give_the_same_model_values(1)[OF history])
qed

definition replay_scope :: wire_boundary where
  "replay_scope = \<lparr>boundary_profile = \<lparr>negotiated_version = 6, negotiated_families = {Wire_Query},
      negotiated_atomicities = {3}, negotiated_schemes = {1}\<rparr>,
     boundary_deployment = 7, boundary_source = 0, boundary_target = 2, boundary_principal = 7, boundary_key = 9,
     boundary_epoch = 9, boundary_route_scope = 1, boundary_now = 105, boundary_asset_ttl_floor = 0,
     boundary_future_skew = 0, boundary_max_frame = 4096, boundary_version_floor = 6,
     boundary_critical_allowed = False, boundary_threshold_supported = False\<rparr>"

definition replay_fixture_verifier where
  "replay_fixture_verifier core signing signature \<longleftrightarrow>
    signing = envelope_signing_bytes core \<and> (core = replay_first_core \<and> signature = replay_first_signature \<or>
       core = replay_changed_core \<and> signature = replay_changed_signature)"

definition admit_replay where
  "admit_replay bytes =
     wire_gate replay_fixture_verifier (\<lambda>_. True) (\<lambda>_ core. decode_wire_query_body core \<noteq> None) replay_scope bytes"

lemma both_exact_signed_queries_are_individually_admissible_at_the_delivery_boundary:
  "admit_replay replay_first_bytes = Gate_Admitted replay_first_packet"
  "admit_replay replay_changed_bytes = Gate_Admitted replay_changed_packet"
proof -
  have sizes: "length replay_first_bytes \<le> 4096" "length replay_changed_bytes \<le> 4096"
    by (simp_all add: replay_first_bytes_def replay_changed_bytes_def)
  show "admit_replay replay_first_bytes = Gate_Admitted replay_first_packet"
    "admit_replay replay_changed_bytes = Gate_Admitted replay_changed_packet"
    using sizes by (simp_all add: admit_replay_def wire_gate_def replay_scope_def replay_fixture_verifier_def current_wire_scope_def wire_expiry_def
      effective_wire_ttl_def replay_first_decodes_the_exact_signed_packet replay_changed_decodes_the_exact_signed_packet
      replay_first_core_def replay_changed_core_def decode_wire_query_body_def parse_wire_application_query_def Let_def)
qed

lemma the_live_replay_inputs_have_one_wire_key_and_different_exact_core_bytes:
  "authenticated_wire_message_id replay_first_core = authenticated_wire_message_id replay_changed_core"
  "encode_wire_core replay_first_core \<noteq> encode_wire_core replay_changed_core"
proof -
  show "authenticated_wire_message_id replay_first_core = authenticated_wire_message_id replay_changed_core"
    by (simp add: authenticated_wire_message_id_def replay_first_core_def replay_changed_core_def)
  show "encode_wire_core replay_first_core \<noteq> encode_wire_core replay_changed_core"
    unfolding replay_first_encodes_the_exact_core replay_changed_encodes_the_exact_core
    by (simp add: replay_first_core_bytes_def replay_changed_core_bytes_def)
qed

lemma the_same_two_actual_packets_detect_removing_the_exact_core_comparison:
  fixes initial selected ledger
  defines "initial \<equiv> \<lparr>rust_replay_bindings = (\<lambda>_. None), rust_replay_selected_head = Some 0,
      rust_replay_order = 0, rust_replay_product = ledger\<rparr>"
    and "selected \<equiv> fst (rust_replay_check True (admit_replay replay_first_bytes) 1 initial)"
  shows "snd (rust_replay_check True (admit_replay replay_first_bytes) 1 initial) = Wire_First replay_first_packet"
    "rust_replay_selected_head selected = Some 1 \<and> rust_replay_product selected = ledger"
    "rust_replay_check True (admit_replay replay_changed_bytes) 2 selected = (selected,Wire_Rejected Conflicting_Wire_Replay)"
    "rust_replay_check False (admit_replay replay_changed_bytes) 2 selected = (selected,Wire_Identical replay_changed_packet)"
    "rust_replay_check True (admit_replay replay_first_bytes) 2 selected = (selected,Wire_Identical replay_first_packet)"
  by (simp_all add: initial_def selected_def both_exact_signed_queries_are_individually_admissible_at_the_delivery_boundary
    rust_replay_check_def Let_def the_live_replay_inputs_have_one_wire_key_and_different_exact_core_bytes)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_rust_exact_replay_guard_matches_the_reference_wire_state_head_and_response
      a_selected_signed_current_query_uses_the_same_cut_and_value_on_both_sides
      both_exact_signed_queries_are_individually_admissible_at_the_delivery_boundary
      the_same_two_actual_packets_detect_removing_the_exact_core_comparison})
  then () else error "Unexpected oracle in signed replay code correspondence"
\<close>

end

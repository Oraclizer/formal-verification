theory Reference_Exact_Guard_Consumers
  imports "OIP_Reference_Profile.Reference_Exact_Guard_Packets" "OIP_Reference_Profile.Reference_Scheduled_ACK_Wire" Reference_Queue_Code
begin

definition same_slot_fixture_ack :: product_secondary_ack where
  "same_slot_fixture_ack = \<lparr>ack_settlement_key = ((0,17),3),
     ack_publication = \<lparr>publication_origin = (0,17), publication_decision =
       \<lparr>origin_binding = \<lparr>binding_key = (0,17), binding_asset = 17, binding_amount = 5,
          binding_destination = 2, binding_recipient = 3, binding_source_epoch = 9,
          binding_operation = Destination_Credit, binding_separator = 0\<rparr>,
         origin_kind = Confirmed_Decision, origin_epoch = 9, origin_commit_position = 3\<rparr>\<rparr>, ack_target = 99\<rparr>"

definition guard_ack_image :: "(nat rust_queue_image, product_cut) rust_schedule_image" where
  "guard_ack_image = \<lparr>rust_schedule_payload =
       \<lparr>rust_queue_primary = 5, rust_queue_receiver = 99,
         rust_queue_rows = (\<lambda>_. None)(((0,17),3) := Some
           \<lparr>rust_secondary_commitment = ack_publication same_slot_fixture_ack, rust_secondary_receiver = 99,
             rust_secondary_tries = 1, rust_secondary_phase = Secondary_In_Flight\<rparr>)\<rparr>,
       rust_schedule_store = (\<lambda>_. None), rust_schedule_cut = \<lparr>cut_authority_epoch = 9, cut_revision = 7\<rparr>\<rparr>"

definition read_guard_ack where
  "read_guard_ack bytes = (case decode_wire_packet bytes of None \<Rightarrow> None | Some packet \<Rightarrow>
       let core = packet_core packet in
       case select_native_scheduled_ack 7 same_slot_fixture_ack core of None \<Rightarrow> None | Some operand \<Rightarrow>
         Some (operand,authenticated_wire_message_id core,encode_wire_core core))"

definition run_guard_ack where
  "run_guard_ack key exact code = rust_schedule_consume
      (\<lambda>queue. Inl (rust_acknowledge_row (\<lambda>_. True) same_slot_fixture_ack queue)) key exact () code"

lemma the_two_exact_ack_envelopes_select_one_product_slot_and_distinct_wire_keys:
  obtains operand left_key right_key
  where
    "read_guard_ack guard_ack_left_packet_bytes = Some (operand,left_key,guard_ack_left_core_bytes)"
    "read_guard_ack guard_ack_right_packet_bytes = Some (operand,right_key,guard_ack_right_core_bytes)"
    "left_key \<noteq> right_key" "scheduled_ack_key operand = ((0,17),3)"
proof -
  let ?operand = "\<lparr>scheduled_ack_key = ((0,17),3), scheduled_ack_target = 99, scheduled_ack_asset = 17,
     scheduled_ack_owner = 7, scheduled_ack_destination = 2, scheduled_ack_recipient = 3, scheduled_ack_amount = 5,
     scheduled_ack_epoch = 9, scheduled_ack_kind = Confirmed_Decision\<rparr>"
  have exact_left: "select_native_scheduled_ack 7 same_slot_fixture_ack guard_ack_left_core = Some ?operand"
    and exact_right: "select_native_scheduled_ack 7 same_slot_fixture_ack guard_ack_right_core = Some ?operand"
    by (simp_all add: select_native_scheduled_ack_def scheduled_ack_matches_publication_def parse_native_scheduled_ack_def
      same_slot_fixture_ack_def guard_ack_left_core_def guard_ack_left_body_def
      guard_ack_right_core_def guard_ack_right_body_def settlement_key_def wire_octets_def Let_def)
  have distinct: "authenticated_wire_message_id guard_ack_left_core \<noteq> authenticated_wire_message_id guard_ack_right_core"
    by (simp add: authenticated_wire_message_id_def guard_ack_left_core_def guard_ack_right_core_def)
  show thesis by (rule that[of ?operand "authenticated_wire_message_id guard_ack_left_core"
      "authenticated_wire_message_id guard_ack_right_core"])
    (simp_all add: read_guard_ack_def guard_ack_left_decodes_from_the_full_native_envelope
      guard_ack_right_decodes_from_the_full_native_envelope guard_ack_left_exact_core_encoding guard_ack_right_exact_core_encoding
      exact_left exact_right distinct Let_def)
qed

lemma the_same_two_ack_envelopes_serialize_and_exchange_if_compatibility_is_removed:
  fixes left_key right_key normal swapped
  defines "left_key \<equiv> authenticated_wire_message_id guard_ack_left_core"
    and "right_key \<equiv> authenticated_wire_message_id guard_ack_right_core"
    and "normal \<equiv> rust_schedule_pair False (run_guard_ack left_key guard_ack_left_core_bytes)
      (run_guard_ack right_key guard_ack_right_core_bytes) guard_ack_image"
    and "swapped \<equiv> rust_schedule_pair True (run_guard_ack left_key guard_ack_left_core_bytes)
      (run_guard_ack right_key guard_ack_right_core_bytes) guard_ack_image"
  shows "normal = swapped"
    "(case normal of (state,first,second) \<Rightarrow>
        rust_try_adjacent_exchange (\<lambda>r. r = Rust_Scheduled True True) True
          (native_schedule_compatible (Native_Schedule_ACK same_slot_fixture_ack) (Native_Schedule_ACK same_slot_fixture_ack))
          normal swapped = Rust_Serialized state first second)"
    "(case normal of (state,first,second) \<Rightarrow>
        rust_try_adjacent_exchange (\<lambda>r. r = Rust_Scheduled True True) True True normal swapped = Rust_Exchanged state first second)"
proof -
  have distinct: "left_key \<noteq> right_key"
    by (simp add: left_key_def right_key_def authenticated_wire_message_id_def guard_ack_left_core_def guard_ack_right_core_def)
  show same: "normal = swapped" using distinct
    by (simp add: normal_def swapped_def rust_schedule_pair_def run_guard_ack_def rust_schedule_consume_def rust_acknowledge_row_def
      guard_ack_image_def same_slot_fixture_ack_def settlement_key_def fun_upd_twist Let_def)
  show "(case normal of (state,first,second) \<Rightarrow>
        rust_try_adjacent_exchange (\<lambda>r. r = Rust_Scheduled True True) True
          (native_schedule_compatible (Native_Schedule_ACK same_slot_fixture_ack) (Native_Schedule_ACK same_slot_fixture_ack))
          normal swapped = Rust_Serialized state first second)"
    by (cases normal) (simp add: native_schedule_compatible_def rust_try_adjacent_exchange_def Let_def split: prod.splits)
  show "(case normal of (state,first,second) \<Rightarrow>
        rust_try_adjacent_exchange (\<lambda>r. r = Rust_Scheduled True True) True True normal swapped = Rust_Exchanged state first second)"
    using distinct unfolding same[symmetric]
    by (simp add: normal_def rust_schedule_pair_def run_guard_ack_def rust_schedule_consume_def rust_acknowledge_row_def
      rust_try_adjacent_exchange_def guard_ack_image_def same_slot_fixture_ack_def settlement_key_def Let_def)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_two_exact_ack_envelopes_select_one_product_slot_and_distinct_wire_keys
    the_same_two_ack_envelopes_serialize_and_exchange_if_compatibility_is_removed})
  then () else error "Unexpected oracle in exact guard consumer comparison"
\<close>

end

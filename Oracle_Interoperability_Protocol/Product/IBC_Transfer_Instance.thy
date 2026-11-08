theory IBC_Transfer_Instance
  imports IBC_Transfer_Evidence EAB_Resolution_Instance
begin

section \<open>ICS-020 source commitment and application outcome\<close>

type_synonym ibc_send_path = "nat \<times> nat \<times> nat"

definition ibc_source_path where
  "ibc_source_path packet = (ibc_source_chain packet, ibc_source_port packet, ibc_source_channel packet)"

record ibc_sender_state =
  ibc_commitment :: "ibc_packet option"
  ibc_pending_liability :: nat
  ibc_sender_units :: nat
  ibc_acknowledged_destination_units :: nat
  ibc_next_ack :: nat
  ibc_sender_channel_open :: bool
  ibc_next_send :: "ibc_send_path \<Rightarrow> nat"

datatype ibc_sender_effect =
    IBC_No_Commit | IBC_Clear_Success
  | IBC_Unescrow_Refund nat nat nat
  | IBC_Remint_Refund nat nat nat

definition ibc_valid_liability where
  "ibc_valid_liability state \<longleftrightarrow>
    ibc_pending_liability state = (case ibc_commitment state of None \<Rightarrow> 0 | Some packet \<Rightarrow> ibc_amount packet)"

definition ibc_start_transfer where
  "ibc_start_transfer packet state =
    (if ibc_commitment state = None \<and> ibc_sender_channel_open state \<and> ibc_amount packet > 0 \<and>
        ibc_amount packet \<le> ibc_sender_units state \<and>
        ibc_deadline_fields_valid packet \<and>
        ibc_sequence packet = ibc_next_send state (ibc_source_path packet) \<and>
        0 < ibc_sequence packet \<and> Suc (ibc_sequence packet) < 2^64
     then state\<lparr>ibc_commitment := Some packet, ibc_pending_liability := ibc_amount packet,
        ibc_sender_units := ibc_sender_units state - ibc_amount packet,
        ibc_next_send := (ibc_next_send state)(ibc_source_path packet := Suc (ibc_sequence packet))\<rparr>
     else state)"

lemma starting_an_ibc_transfer_establishes_the_exact_pending_liability:
  "ibc_valid_liability state \<Longrightarrow> ibc_valid_liability (ibc_start_transfer packet state)"
  by (simp add: ibc_start_transfer_def ibc_valid_liability_def)

definition ibc_source_view where
  "ibc_source_view state =
    \<lparr>unresolved_binding = ibc_commitment state, unresolved_units = ibc_pending_liability state,
     active_origin_units = ibc_sender_units state,
     active_destination_units = ibc_acknowledged_destination_units state\<rparr>"

fun ibc_ack_admissible where
  "ibc_ack_admissible order state (IBC_Acknowledgement packet ack) =
    (ibc_sender_channel_open state \<and>
      (order \<noteq> IBC_Unordered \<longrightarrow> ibc_next_ack state = ibc_sequence packet))"
| "ibc_ack_admissible order state (IBC_Elapsed_Proof packet facts) = True"
| "ibc_ack_admissible order state (IBC_Closed_Proof packet facts) = True"

definition ibc_source_authentication where
  "ibc_source_authentication verify channel_bound bank_ready profile order state evidence \<longleftrightarrow>
    channel_bound \<and> (profile \<noteq> IBC_Go_10 \<or> order \<noteq> IBC_Ordered_Allow_Timeout) \<and>
    verify evidence \<and> ibc_ack_admissible order state evidence \<and>
    (case ibc_evidence_kind profile order evidence of Some (_, Resolve_Return) \<Rightarrow> bank_ready | _ \<Rightarrow> True)"

fun ibc_commit_terminal_metadata where
  "ibc_commit_terminal_metadata profile order (IBC_Acknowledgement packet ack) state =
    (if order = IBC_Unordered then state else state\<lparr>ibc_next_ack := Suc (ibc_next_ack state)\<rparr>)"
| "ibc_commit_terminal_metadata profile order (IBC_Elapsed_Proof packet facts) state =
    (case order of IBC_Unordered \<Rightarrow> state
     | IBC_Ordered \<Rightarrow> state\<lparr>ibc_sender_channel_open := False\<rparr>
     | IBC_Ordered_Allow_Timeout \<Rightarrow> state\<lparr>ibc_next_ack := Suc (ibc_next_ack state)\<rparr>)"
| "ibc_commit_terminal_metadata profile order (IBC_Closed_Proof packet facts) state =
    (if profile = IBC_Go_10 \<and> order = IBC_Ordered
     then state\<lparr>ibc_sender_channel_open := False\<rparr> else state)"

lemma ibc_metadata_preserves_the_economic_fields [simp]:
  "ibc_commitment (ibc_commit_terminal_metadata profile order evidence state) = ibc_commitment state"
  "ibc_pending_liability (ibc_commit_terminal_metadata profile order evidence state) = ibc_pending_liability state"
  "ibc_sender_units (ibc_commit_terminal_metadata profile order evidence state) = ibc_sender_units state"
  "ibc_acknowledged_destination_units (ibc_commit_terminal_metadata profile order evidence state) =
    ibc_acknowledged_destination_units state"
  "ibc_next_send (ibc_commit_terminal_metadata profile order evidence state) = ibc_next_send state"
  by (cases evidence; cases order; cases profile; simp)+

definition ibc_commit_resolution where
  "ibc_commit_resolution profile order evidence packet side state =
    (let clear = state\<lparr>ibc_commitment := None, ibc_pending_liability := 0\<rparr> in
     case side of Resolve_Credit \<Rightarrow>
       (ibc_commit_terminal_metadata profile order evidence
          (clear\<lparr>ibc_acknowledged_destination_units := ibc_acknowledged_destination_units state + ibc_amount packet\<rparr>),
        IBC_Clear_Success)
     | Resolve_Return \<Rightarrow>
       (ibc_commit_terminal_metadata profile order evidence
          (clear\<lparr>ibc_sender_units := ibc_sender_units state + ibc_amount packet\<rparr>),
        case ibc_send_mode packet of IBC_Escrowed \<Rightarrow> IBC_Unescrow_Refund (ibc_sender packet) (ibc_denom packet) (ibc_amount packet)
        | IBC_Burned \<Rightarrow> IBC_Remint_Refund (ibc_sender packet) (ibc_denom packet) (ibc_amount packet)))"

definition ibc_apply_terminal where
  "ibc_apply_terminal verify channel_bound bank_ready profile order evidence state =
    (if \<not> ibc_source_authentication verify channel_bound bank_ready profile order state evidence
     then (state, IBC_No_Commit)
     else case (ibc_commitment state, ibc_evidence_kind profile order evidence) of
       (Some live, Some (submitted, side)) \<Rightarrow>
         if submitted = live then ibc_commit_resolution profile order evidence live side state else (state, IBC_No_Commit)
     | _ \<Rightarrow> (state, IBC_No_Commit))"

lemma ibc_commit_resolution_implements_the_selected_accounting:
  assumes "ibc_commitment state = Some packet" "ibc_valid_liability state"
  shows "ibc_source_view (fst (ibc_commit_resolution profile order evidence packet side state)) =
    resolve_pending (\<lambda>_. True) (\<lambda>_. Some (packet, side)) evidence (ibc_source_view state)"
  using assms
  by (cases side) (simp_all add: ibc_commit_resolution_def ibc_valid_liability_def ibc_source_view_def
    resolve_pending_def bound_resolution_def Let_def split: ibc_send_mode.splits)

theorem the_ibc_source_commitment_consumer_implements_the_common_resolution:
  assumes valid: "ibc_valid_liability state"
  shows "ibc_source_view (fst (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state)) =
    resolve_pending (ibc_source_authentication verify channel_bound bank_ready profile order state)
      (ibc_evidence_kind profile order) evidence (ibc_source_view state)"
proof (cases "ibc_source_authentication verify channel_bound bank_ready profile order state evidence")
  case False
  then show ?thesis by (simp add: ibc_apply_terminal_def resolve_pending_def bound_resolution_def ibc_source_view_def
    split: option.splits)
next
  case True
  show ?thesis
  proof (cases "ibc_commitment state")
    case None
    with True show ?thesis by (simp add: ibc_apply_terminal_def resolve_pending_def ibc_source_view_def)
  next
    case (Some packet)
    note live = Some
    show ?thesis
    proof (cases "ibc_evidence_kind profile order evidence")
      case None
      with True live show ?thesis by (simp add: ibc_apply_terminal_def resolve_pending_def bound_resolution_def ibc_source_view_def)
    next
      case (Some result)
      obtain submitted side where operands: "result = (submitted, side)" by (cases result)
      from True live Some operands show ?thesis
        using ibc_commit_resolution_implements_the_selected_accounting[OF live valid, of profile order evidence side]
        by (cases "submitted = packet") (simp_all add: ibc_apply_terminal_def resolve_pending_def bound_resolution_def ibc_source_view_def)
    qed
  qed
qed

lemma source_resolution_preserves_the_exact_liability:
  assumes "ibc_valid_liability state"
  shows "ibc_valid_liability (fst (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state))"
  using assms
  by (simp add: ibc_apply_terminal_def ibc_commit_resolution_def ibc_valid_liability_def Let_def
    split: option.splits prod.splits resolution_side.splits ibc_send_mode.splits if_splits)

theorem an_ibc_terminal_consumer_preserves_active_and_pending_units:
  assumes "ibc_valid_liability state"
  shows "resolution_mass (ibc_source_view (fst (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state))) =
    resolution_mass (ibc_source_view state)"
  unfolding the_ibc_source_commitment_consumer_implements_the_common_resolution[OF assms]
  by (rule evidence_resolution_conserves_the_active_and_pending_amount)

lemma a_cleared_ibc_commitment_cannot_be_consumed_again:
  assumes "ibc_commitment state = None"
  shows "ibc_apply_terminal verify channel_bound bank_ready profile order evidence state = (state, IBC_No_Commit)"
  using assms by (simp add: ibc_apply_terminal_def)

lemma unclassified_ibc_evidence_cannot_consume_a_commitment:
  assumes "ibc_evidence_kind profile order evidence = None"
  shows "ibc_apply_terminal verify channel_bound bank_ready profile order evidence state = (state, IBC_No_Commit)"
  using assms by (cases "ibc_commitment state") (simp_all add: ibc_apply_terminal_def)

lemma a_registered_send_allocates_its_sequence_once:
  assumes "ibc_start_transfer packet state \<noteq> state"
  shows "ibc_commitment (ibc_start_transfer packet state) = Some packet"
    "ibc_sequence packet = ibc_next_send state (ibc_source_path packet)"
    "ibc_next_send (ibc_start_transfer packet state) (ibc_source_path packet) = Suc (ibc_sequence packet)"
  using assms by (auto simp: ibc_start_transfer_def split: if_splits)

lemma starting_a_transfer_does_not_reduce_any_send_sequence:
  "ibc_next_send state path \<le> ibc_next_send (ibc_start_transfer packet state) path"
  by (auto simp: ibc_start_transfer_def split: if_splits)

lemma a_terminal_consumer_keeps_the_send_allocator [simp]:
  "ibc_next_send (fst (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state)) =
    ibc_next_send state"
  by (simp add: ibc_apply_terminal_def ibc_commit_resolution_def Let_def
    split: option.splits prod.splits resolution_side.splits ibc_send_mode.splits if_splits)

datatype ibc_sender_action =
    IBC_Start_Send ibc_packet
  | IBC_Resolve_Send bool bool ibc_timeout_profile ibc_order ibc_terminal_evidence

fun ibc_sender_step where
  "ibc_sender_step verify (IBC_Start_Send packet) state = ibc_start_transfer packet state"
| "ibc_sender_step verify (IBC_Resolve_Send channel_bound bank_ready profile order evidence) state =
    fst (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state)"

lemma all_ibc_sender_steps_preserve_monotone_send_sequences:
  "ibc_next_send state path \<le> ibc_next_send (ibc_sender_step verify action state) path"
  by (cases action) (simp_all add: starting_a_transfer_does_not_reduce_any_send_sequence)

lemma all_ibc_sender_continuations_preserve_monotone_send_sequences:
  "ibc_next_send state path \<le> ibc_next_send (fold (ibc_sender_step verify) actions state) path"
proof (induction actions arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons action rest)
  have one: "ibc_next_send state path \<le> ibc_next_send (ibc_sender_step verify action state) path"
    by (rule all_ibc_sender_steps_preserve_monotone_send_sequences)
  have later: "ibc_next_send (ibc_sender_step verify action state) path \<le>
      ibc_next_send (fold (ibc_sender_step verify) rest (ibc_sender_step verify action state)) path"
    by (rule Cons.IH)
  show ?case
    using order_trans[OF one later] by simp
qed

lemma a_spent_send_key_is_below_the_allocator_in_every_continuation:
  assumes sent: "ibc_start_transfer old state \<noteq> state"
  shows "ibc_sequence old <
    ibc_next_send (fold (ibc_sender_step verify) actions (ibc_start_transfer old state)) (ibc_source_path old)"
  using all_ibc_sender_continuations_preserve_monotone_send_sequences[
    of "ibc_start_transfer old state" "ibc_source_path old" verify actions]
  unfolding a_registered_send_allocates_its_sequence_once(3)[OF sent] by simp

theorem a_spent_ibc_send_key_cannot_be_registered_again:
  fixes current :: ibc_sender_state
    and verify actions
  assumes sent: "ibc_start_transfer old state \<noteq> state"
    and same_path: "ibc_source_path retried = ibc_source_path old"
    and same_sequence: "ibc_sequence retried = ibc_sequence old"
  defines "current \<equiv> fold (ibc_sender_step verify) actions (ibc_start_transfer old state)"
  shows "ibc_start_transfer retried current = current"
proof (rule ccontr)
  assume repeated: "ibc_start_transfer retried current \<noteq> current"
  have newer: "ibc_sequence old < ibc_next_send current (ibc_source_path old)"
    unfolding current_def by (rule a_spent_send_key_is_below_the_allocator_in_every_continuation[OF sent])
  have "ibc_sequence old = ibc_next_send current (ibc_source_path old)"
    using a_registered_send_allocates_its_sequence_once(2)[OF repeated] same_path same_sequence by simp
  with newer show False by simp
qed

theorem a_historical_ack_cannot_consume_a_newly_registered_send_on_its_channel:
  fixes current after :: ibc_sender_state
    and verify actions
  assumes sent: "ibc_start_transfer old state \<noteq> state"
    and same_path: "ibc_source_path new = ibc_source_path old"
  defines "current \<equiv> fold (ibc_sender_step verify) actions (ibc_start_transfer old state)"
    and "after \<equiv> ibc_start_transfer new current"
  assumes fresh: "after \<noteq> current"
  shows "ibc_apply_terminal authenticate channel_bound bank_ready profile order
    (IBC_Acknowledgement old ack) after = (after, IBC_No_Commit)"
proof -
  have fresh_send: "ibc_start_transfer new current \<noteq> current"
    using fresh unfolding after_def .
  have newer: "ibc_sequence old < ibc_next_send current (ibc_source_path old)"
    unfolding current_def by (rule a_spent_send_key_is_below_the_allocator_in_every_continuation[OF sent])
  have live: "ibc_commitment after = Some new"
    unfolding after_def by (rule a_registered_send_allocates_its_sequence_once(1)[OF fresh_send])
  have sequence: "ibc_sequence new = ibc_next_send current (ibc_source_path old)"
    using a_registered_send_allocates_its_sequence_once(2)[OF fresh_send] same_path by simp
  have "ibc_sequence old \<noteq> ibc_sequence new" using newer sequence by simp
  then have different: "old \<noteq> new" by auto
  show ?thesis by (simp add: ibc_apply_terminal_def live different)
qed

lemma failed_ibc_refund_callback_preserves_the_pending_commitment:
  assumes "ibc_evidence_kind profile order evidence = Some (packet, Resolve_Return)"
  shows "ibc_apply_terminal verify channel_bound False profile order evidence state = (state, IBC_No_Commit)"
  using assms by (simp add: ibc_apply_terminal_def ibc_source_authentication_def)

lemma an_applied_ibc_resolution_consumes_its_commitment:
  assumes "snd (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state) \<noteq> IBC_No_Commit"
  shows "ibc_commitment (fst (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state)) = None"
  using assms
  by (simp add: ibc_apply_terminal_def ibc_commit_resolution_def Let_def
    split: option.splits prod.splits resolution_side.splits ibc_send_mode.splits if_splits)

theorem an_applied_ibc_resolution_cannot_refund_or_clear_twice:
  assumes "snd (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state) \<noteq> IBC_No_Commit"
  defines "after \<equiv> fst (ibc_apply_terminal verify channel_bound bank_ready profile order evidence state)"
  shows "ibc_apply_terminal other_verify other_channel other_bank profile order retried after = (after, IBC_No_Commit)"
  by (rule a_cleared_ibc_commitment_cannot_be_consumed_again)
    (unfold after_def, rule an_applied_ibc_resolution_consumes_its_commitment[OF assms(1)])

theorem a_refund_with_elapsed_evidence_fences_later_delivery:
  assumes committed: "snd (ibc_apply_terminal verify channel_bound bank_ready profile order
      (IBC_Elapsed_Proof packet facts) state) \<noteq> IBC_No_Commit"
    and height: "ibc_height_le (ibc_proof_height facts) (ibc_receiver_height receiver)"
    and time: "ibc_proof_time facts \<le> ibc_receiver_time receiver"
  shows "snd (ibc_receive order commitment_verified packet receiver) \<noteq> IBC_Forward_Application"
proof -
  have elapsed: "ibc_elapsed packet (ibc_proof_height facts) (ibc_proof_time facts)"
  proof (rule ccontr)
    assume "\<not> ibc_elapsed packet (ibc_proof_height facts) (ibc_proof_time facts)"
    then have absent: "ibc_evidence_kind profile order (IBC_Elapsed_Proof packet facts) = None" by simp
    have "ibc_apply_terminal verify channel_bound bank_ready profile order (IBC_Elapsed_Proof packet facts) state =
      (state, IBC_No_Commit)"
      by (rule unclassified_ibc_evidence_cannot_consume_a_commitment[OF absent])
    with committed show False by simp
  qed
  show ?thesis by (rule proven_deadline_rules_out_later_delivery[OF elapsed height time])
qed

definition ibc_application_effect where
  "ibc_application_effect outcome bank_succeeded packet before =
    (if outcome \<noteq> IBC_Forward_Application then (before, None)
     else if bank_succeeded then (before + ibc_amount packet, Some IBC_Ack_Success)
     else (before, Some IBC_Ack_Error))"

lemma a_committed_error_ack_has_no_destination_credit:
  assumes "ibc_application_effect outcome bank_succeeded packet before = (after, Some IBC_Ack_Error)"
  shows "after = before"
  using assms by (auto simp: ibc_application_effect_def split: if_splits)

lemma a_success_ack_reports_the_already_executed_destination_credit:
  assumes "ibc_application_effect outcome bank_succeeded packet before = (after, Some IBC_Ack_Success)"
  shows "outcome = IBC_Forward_Application \<and> after = before + ibc_amount packet"
  using assms by (auto simp: ibc_application_effect_def split: if_splits)

thm_oracles the_ibc_source_commitment_consumer_implements_the_common_resolution
  an_ibc_terminal_consumer_preserves_active_and_pending_units
  a_spent_ibc_send_key_cannot_be_registered_again
  a_historical_ack_cannot_consume_a_newly_registered_send_on_its_channel
  failed_ibc_refund_callback_preserves_the_pending_commitment
  source_attestation.actual_eab_credit_implements_the_common_resolution
  source_attestation.actual_eab_return_implements_the_common_resolution

end

theory IBC_Transfer_Examples
  imports "../IBC_Transfer_Instance"
begin

definition ibc_case_packet where
  "ibc_case_packet = \<lparr>ibc_source_chain = 1, ibc_source_port = 3, ibc_source_channel = 7,
    ibc_destination_chain = 2, ibc_destination_port = 3, ibc_destination_channel = 8,
    ibc_sequence = 5, ibc_denom = 17, ibc_sender = 21, ibc_receiver = 22, ibc_amount = 11,
    ibc_memo = [], ibc_send_mode = IBC_Escrowed,
    ibc_timeout_height = Some (2,8), ibc_timeout_time = Some 100\<rparr>"

definition ibc_case_sender where
  "ibc_case_sender = \<lparr>ibc_commitment = None, ibc_pending_liability = 0, ibc_sender_units = 30,
    ibc_acknowledged_destination_units = 0, ibc_next_ack = 5, ibc_sender_channel_open = True,
    ibc_next_send = (\<lambda>_. 1)((1,3,7) := 5)\<rparr>"

definition ibc_case_receiver where
  "ibc_case_receiver = \<lparr>ibc_receiver_open = True, ibc_receiver_height = (2,7), ibc_receiver_time = 95,
    ibc_receiver_first = 1, ibc_receiver_next = 5, ibc_receiver_receipts = (\<lambda>_. None)\<rparr>"

definition ibc_case_absence where
  "ibc_case_absence = \<lparr>ibc_proof_height = (2,7), ibc_proof_time = 95, ibc_reported_next = Some 5,
    ibc_proof_next = Some 5, ibc_proof_receipt = Some None, ibc_proof_closed = False\<rparr>"

abbreviation ibc_case_pending where
  "ibc_case_pending \<equiv> ibc_start_transfer ibc_case_packet ibc_case_sender"

abbreviation ibc_case_go where
  "ibc_case_go \<equiv> ibc_apply_terminal (\<lambda>_. True) True True IBC_Go_10 IBC_Unordered"

lemmas ibc_case_simps =
  ibc_case_packet_def ibc_case_sender_def ibc_case_receiver_def ibc_case_absence_def
  ibc_start_transfer_def ibc_apply_terminal_def ibc_source_authentication_def ibc_commit_resolution_def
  ibc_absent_for_elapsed_def ibc_absent_for_close_def ibc_elapsed_def ibc_height_le_def
  ibc_receive_def ibc_sequence_is_fresh_def ibc_application_effect_def ibc_deadline_fields_valid_def ibc_source_path_def Let_def

lemma a_live_unordered_transfer_reaches_the_application_and_success_ack_clears:
  "let arrival = ibc_receive IBC_Unordered True ibc_case_packet ibc_case_receiver;
       application = ibc_application_effect (snd arrival) True ibc_case_packet 0;
       completed = ibc_case_go (IBC_Acknowledgement ibc_case_packet IBC_Ack_Success) ibc_case_pending
   in ibc_receiver_receipts (fst arrival) 5 = Some IBC_Packet_Receipt \<and>
      application = (11, Some IBC_Ack_Success) \<and> snd completed = IBC_Clear_Success \<and>
      ibc_commitment (fst completed) = None \<and> ibc_pending_liability (fst completed) = 0 \<and>
      ibc_sender_units (fst completed) = 19 \<and> ibc_acknowledged_destination_units (fst completed) = 11"
  by (simp add: ibc_case_simps)

lemma a_real_error_ack_refunds_without_a_destination_effect:
  "let arrival = ibc_receive IBC_Unordered True ibc_case_packet ibc_case_receiver;
       application = ibc_application_effect (snd arrival) False ibc_case_packet 0;
       completed = ibc_case_go (IBC_Acknowledgement ibc_case_packet IBC_Ack_Error) ibc_case_pending
   in application = (0, Some IBC_Ack_Error) \<and> snd completed = IBC_Unescrow_Refund 21 17 11 \<and>
      ibc_commitment (fst completed) = None \<and> ibc_sender_units (fst completed) = 30 \<and>
      ibc_acknowledged_destination_units (fst completed) = 0"
  by (simp add: ibc_case_simps)

lemma an_error_ack_remints_an_originally_burned_voucher_to_the_sender:
  "let packet = ibc_case_packet\<lparr>ibc_send_mode := IBC_Burned\<rparr>;
       pending = ibc_start_transfer packet ibc_case_sender;
       result = ibc_case_go (IBC_Acknowledgement packet IBC_Ack_Error) pending
   in snd result = IBC_Remint_Refund 21 17 11 \<and> ibc_sender_units (fst result) = 30"
  by (simp add: ibc_case_simps)

lemma past_absence_cannot_refund_while_the_destination_can_still_receive:
  "ibc_case_go (IBC_Elapsed_Proof ibc_case_packet ibc_case_absence) ibc_case_pending = (ibc_case_pending, IBC_No_Commit) \<and>
   ibc_absent_for_elapsed IBC_Go_10 IBC_Unordered ibc_case_packet ibc_case_absence \<and>
   snd (ibc_receive IBC_Unordered True ibc_case_packet ibc_case_receiver) = IBC_Forward_Application"
  by (simp add: ibc_case_simps)

lemma removing_only_the_cutoff_allows_refund_and_a_later_receive:
  "let old = IBC_Elapsed_Proof ibc_case_packet ibc_case_absence;
       weakened = ibc_commit_resolution IBC_Go_10 IBC_Unordered old ibc_case_packet Resolve_Return ibc_case_pending
   in ibc_case_go old ibc_case_pending = (ibc_case_pending, IBC_No_Commit) \<and>
      ibc_absent_for_elapsed IBC_Go_10 IBC_Unordered ibc_case_packet ibc_case_absence \<and>
      snd weakened = IBC_Unescrow_Refund 21 17 11 \<and>
      snd (ibc_receive IBC_Unordered True ibc_case_packet ibc_case_receiver) = IBC_Forward_Application"
  by (simp add: ibc_case_simps)

lemma a_proven_height_at_expiry_refunds_once_and_refuses_late_delivery:
  "let facts = ibc_case_absence\<lparr>ibc_proof_height := (2,8)\<rparr>;
       destination = ibc_case_receiver\<lparr>ibc_receiver_height := (2,8)\<rparr>;
       evidence = IBC_Elapsed_Proof ibc_case_packet facts;
       result = ibc_case_go evidence ibc_case_pending
   in snd result = IBC_Unescrow_Refund 21 17 11 \<and> ibc_sender_units (fst result) = 30 \<and>
      ibc_case_go evidence (fst result) = (fst result, IBC_No_Commit) \<and>
      ibc_receive IBC_Unordered True ibc_case_packet destination = (destination, IBC_Receive_Refused)"
  by (simp add: ibc_case_simps)

lemma a_proven_timestamp_alone_fences_the_packet_and_a_received_packet_cannot_refund:
  "let facts = ibc_case_absence\<lparr>ibc_proof_time := 100\<rparr>;
       received = facts\<lparr>ibc_proof_receipt := Some (Some IBC_Packet_Receipt)\<rparr>
   in snd (ibc_case_go (IBC_Elapsed_Proof ibc_case_packet facts) ibc_case_pending) = IBC_Unescrow_Refund 21 17 11 \<and>
      ibc_case_go (IBC_Elapsed_Proof ibc_case_packet received) ibc_case_pending = (ibc_case_pending, IBC_No_Commit)"
  by (simp add: ibc_case_simps)

lemma timeout_on_close_uses_the_closed_counterparty_before_the_clock_limit:
  "let facts = ibc_case_absence\<lparr>ibc_proof_closed := True\<rparr>;
       destination = ibc_case_receiver\<lparr>ibc_receiver_open := False\<rparr>;
       result = ibc_case_go (IBC_Closed_Proof ibc_case_packet facts) ibc_case_pending
   in \<not> ibc_elapsed ibc_case_packet (ibc_proof_height facts) (ibc_proof_time facts) \<and>
      snd result = IBC_Unescrow_Refund 21 17 11 \<and>
      ibc_receive IBC_Unordered True ibc_case_packet destination = (destination, IBC_Receive_Refused)"
  by (simp add: ibc_case_simps)

lemma altered_packet_identity_or_unverified_ack_cannot_refund:
  "let other = ibc_case_packet\<lparr>ibc_destination_channel := 9\<rparr>;
       ack = IBC_Acknowledgement ibc_case_packet IBC_Ack_Error
   in ibc_case_go (IBC_Acknowledgement other IBC_Ack_Error) ibc_case_pending = (ibc_case_pending, IBC_No_Commit) \<and>
      ibc_apply_terminal (\<lambda>_. False) True True IBC_Go_10 IBC_Unordered ack ibc_case_pending =
        (ibc_case_pending, IBC_No_Commit)"
  by (simp add: ibc_case_simps)

lemma oat_requires_the_positive_timeout_marker_after_the_destination_attempt:
  "let after = ibc_case_receiver\<lparr>ibc_receiver_time := 100\<rparr>;
       marked = ibc_receive IBC_Ordered_Allow_Timeout True ibc_case_packet after;
       absent = ibc_case_absence\<lparr>ibc_proof_time := 100, ibc_reported_next := Some 6, ibc_proof_next := None\<rparr>;
       proved = absent\<lparr>ibc_proof_receipt := Some (Some IBC_Timeout_Receipt)\<rparr>
   in snd marked = IBC_Marked_Timeout \<and> ibc_receiver_next (fst marked) = 6 \<and>
      ibc_receiver_receipts (fst marked) 5 = Some IBC_Timeout_Receipt \<and>
      ibc_evidence_kind ICS004_Text IBC_Ordered_Allow_Timeout (IBC_Elapsed_Proof ibc_case_packet absent) = None \<and>
      ibc_evidence_kind ICS004_Text IBC_Ordered_Allow_Timeout (IBC_Elapsed_Proof ibc_case_packet proved) =
        Some (ibc_case_packet, Resolve_Return)"
  by (simp add: ibc_case_simps)

lemma literal_oat_pseudocode_returns_early_even_for_a_valid_predeadline_receive:
  "ibc_receive IBC_Ordered_Allow_Timeout True ibc_case_packet ibc_case_receiver =
    (ibc_case_receiver, IBC_Early_OAT_Return)"
  by (simp add: ibc_case_simps)

lemma oat_closed_timeout_needs_a_certified_next_sequence_or_the_timeout_receipt:
  "let unknown = ibc_case_absence\<lparr>ibc_proof_closed := True, ibc_proof_next := None, ibc_proof_receipt := None\<rparr>;
       not_attempted = unknown\<lparr>ibc_proof_next := Some 5\<rparr>;
       passed = unknown\<lparr>ibc_reported_next := Some 6, ibc_proof_next := Some 6\<rparr>;
       marked = passed\<lparr>ibc_proof_receipt := Some (Some IBC_Timeout_Receipt)\<rparr>
   in ibc_evidence_kind ICS004_Text IBC_Ordered_Allow_Timeout (IBC_Closed_Proof ibc_case_packet unknown) = None \<and>
      ibc_evidence_kind ICS004_Text IBC_Ordered_Allow_Timeout (IBC_Closed_Proof ibc_case_packet not_attempted) =
        Some (ibc_case_packet, Resolve_Return) \<and>
      ibc_evidence_kind ICS004_Text IBC_Ordered_Allow_Timeout (IBC_Closed_Proof ibc_case_packet passed) = None \<and>
      ibc_evidence_kind ICS004_Text IBC_Ordered_Allow_Timeout (IBC_Closed_Proof ibc_case_packet marked) =
        Some (ibc_case_packet, Resolve_Return)"
  by (simp add: ibc_case_simps)

definition literal_oat_closed_branch where
  "literal_oat_closed_branch packet closed_verified claimed_next marker_verified \<longleftrightarrow>
    closed_verified \<and> (claimed_next \<le> ibc_sequence packet \<or> marker_verified)"

lemma a_caller_selected_next_sequence_would_bypass_the_oat_closed_receipt_check:
  "let observed = ibc_case_absence\<lparr>ibc_proof_closed := True, ibc_proof_next := Some 6,
         ibc_proof_receipt := Some (Some IBC_Packet_Receipt)\<rparr>
   in literal_oat_closed_branch ibc_case_packet True 5 False \<and>
      ibc_evidence_kind ICS004_Text IBC_Ordered_Allow_Timeout (IBC_Closed_Proof ibc_case_packet observed) = None"
  by (simp add: literal_oat_closed_branch_def ibc_case_simps)

lemma a_historical_success_ack_does_not_reopen_or_resolve_the_next_send:
  "let old_ack = IBC_Acknowledgement ibc_case_packet IBC_Ack_Success;
       first = fst (ibc_case_go old_ack ibc_case_pending);
       same_key = ibc_case_packet\<lparr>ibc_amount := 9\<rparr>;
       fresh_packet = ibc_case_packet\<lparr>ibc_sequence := 6\<rparr>;
       fresh = ibc_start_transfer fresh_packet first
   in ibc_next_send first (ibc_source_path ibc_case_packet) = 6 \<and>
      ibc_start_transfer ibc_case_packet first = first \<and>
      ibc_start_transfer same_key first = first \<and>
      ibc_commitment fresh = Some fresh_packet \<and> ibc_pending_liability fresh = 11 \<and>
      ibc_case_go old_ack fresh = (fresh, IBC_No_Commit) \<and>
      ibc_acknowledged_destination_units fresh = 11"
  by (simp add: ibc_case_simps)

lemma a_failed_refund_retains_pending_until_the_same_evidence_commits_once:
  "let ack = IBC_Acknowledgement ibc_case_packet IBC_Ack_Error;
       failed = ibc_apply_terminal (\<lambda>_. True) True False IBC_Go_10 IBC_Unordered ack ibc_case_pending;
       retry = ibc_case_go ack (fst failed)
   in failed = (ibc_case_pending, IBC_No_Commit) \<and>
      ibc_commitment (fst failed) = Some ibc_case_packet \<and> ibc_pending_liability (fst failed) = 11 \<and>
      snd retry = IBC_Unescrow_Refund 21 17 11 \<and> ibc_sender_units (fst retry) = 30 \<and>
      ibc_case_go ack (fst retry) = (fst retry, IBC_No_Commit)"
  by (simp add: ibc_case_simps)

lemmas ibc_resolution_controls =
  a_live_unordered_transfer_reaches_the_application_and_success_ack_clears
  a_real_error_ack_refunds_without_a_destination_effect
  an_error_ack_remints_an_originally_burned_voucher_to_the_sender
  past_absence_cannot_refund_while_the_destination_can_still_receive
  removing_only_the_cutoff_allows_refund_and_a_later_receive
  a_proven_height_at_expiry_refunds_once_and_refuses_late_delivery
  a_proven_timestamp_alone_fences_the_packet_and_a_received_packet_cannot_refund
  timeout_on_close_uses_the_closed_counterparty_before_the_clock_limit
  altered_packet_identity_or_unverified_ack_cannot_refund
  oat_requires_the_positive_timeout_marker_after_the_destination_attempt
  literal_oat_pseudocode_returns_early_even_for_a_valid_predeadline_receive
  oat_closed_timeout_needs_a_certified_next_sequence_or_the_timeout_receipt
  a_caller_selected_next_sequence_would_bypass_the_oat_closed_receipt_check
  an_applied_ibc_resolution_cannot_refund_or_clear_twice
  a_refund_with_elapsed_evidence_fences_later_delivery
  a_spent_ibc_send_key_cannot_be_registered_again
  a_historical_ack_cannot_consume_a_newly_registered_send_on_its_channel
  a_historical_success_ack_does_not_reopen_or_resolve_the_next_send
  a_failed_refund_retains_pending_until_the_same_evidence_commits_once
  the_ibc_source_commitment_consumer_implements_the_common_resolution
  source_attestation.actual_eab_credit_implements_the_common_resolution
  source_attestation.actual_eab_return_implements_the_common_resolution

thm_oracles ibc_resolution_controls

ML \<open>
  val _ =
    if null (Thm_Deps.all_oracles @{thms ibc_resolution_controls})
    then ()
    else error "An EAB or IBC evidence-resolution theorem depends on an oracle"
\<close>

end

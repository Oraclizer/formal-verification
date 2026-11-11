theory Signed_Schedule_Pair
  imports "OIP_Reference_Profile.Reference_Scheduled_ACK_Wire" "OIP_Message_Code.Wire_Code_Read_Service"
    "OIP_Schedule_Product.Schedule_Product" "HOL-Library.Code_Target_Nat"
begin

section \<open>Same-context scheduled acknowledgement and current root read\<close>

text \<open>
  The typed funding commands produce the root units, publication and cut before
  the two canonical packets are decoded by their existing selectors. Signature
  verification and host revalidation remain external to this observation.
\<close>

lemma sw_ack_and_current_have_compatible_product_footprints:
  "compatible_service_actions (native_schedule_action (Native_Schedule_ACK sw_ack))
    (native_schedule_action (Native_Schedule_Current sw_token sw_proof sw_target sw_query sw_cut (Some sw_origin))) sw_world"
  using the_native_ack_and_current_footprints_decide_actual_service_compatibility
    [of "Native_Schedule_ACK sw_ack" "Native_Schedule_Current sw_token sw_proof sw_target sw_query sw_cut (Some sw_origin)" sw_world]
  by (auto simp: native_schedule_compatible_def Let_def)

definition sw_funded_state where
  "sw_funded_state sw_origin sw_asset sw_owner sw_destination sw_recipient sw_amount =
    ss_fund_commands [SS_Reserve 20,SS_Dispatch 0,SS_Debit 0,SS_Record 0,SS_Credit 0,SS_Reconcile 0 0,SS_Publish]
      \<lparr>ss_origin = sw_origin, ss_asset = sw_asset, ss_owner = sw_owner,
        ss_destination = sw_destination, ss_recipient = sw_recipient, ss_amount = sw_amount\<rparr>
      10 ss_initial"

definition sw_dispatched_slot where
  "sw_dispatched_slot sw_publication sw_receiver =
    fst (step_one_slot (\<lambda>_. True) (Slot_Dispatch (settlement_key sw_publication))
      (fst (step_one_slot (\<lambda>_. True) (Slot_Enqueue sw_publication sw_receiver) None)))"

definition sw_compatible_pair_words where
  "sw_compatible_pair_words sw_fields sw_ack_bytes sw_read_bytes =
    (case sw_fields of
      [sw_domain,sw_event,sw_asset,sw_owner,sw_destination,sw_recipient,sw_amount,sw_epoch,sw_commit,sw_revision,
       sw_receiver,sw_session,sw_ack_label,sw_read_label,sw_verified] \<Rightarrow>
       Option.bind (sw_funded_state (sw_domain,sw_event) sw_asset sw_owner sw_destination sw_recipient sw_amount) (\<lambda>sw_seed.
       Option.bind (map_of (sp_publications sw_seed) (sw_domain,sw_event)) (\<lambda>sw_native_publication.
       Option.bind (decode_wire_packet sw_ack_bytes) (\<lambda>sw_ack_packet.
       Option.bind (decode_wire_packet sw_read_bytes) (\<lambda>sw_read_packet.
         let sw_data = sp_data sw_seed;
             sw_ack_core = packet_core sw_ack_packet;
             sw_read_core = packet_core sw_read_packet;
             sw_publication = sp_publication_model sw_native_publication;
             sw_expected_ack = \<lparr>ack_settlement_key = settlement_key sw_publication,
               ack_publication = sw_publication, ack_target = sw_receiver\<rparr>
         in if sw_verified > 1 \<or> sw_ack_label = sw_read_label \<or>
              sw_commit \<noteq> origin_commit_position (publication_decision sw_publication) \<or>
              sw_epoch \<noteq> ss_epoch sw_data \<or> sw_revision \<noteq> ss_revision sw_data \<or> sw_receiver \<noteq> sp_target sw_seed \<or>
              wire_source_domain sw_ack_core \<noteq> sw_receiver \<or> wire_principal sw_ack_core \<noteq> sw_receiver \<or>
              wire_authority_epoch sw_ack_core \<noteq> sw_epoch \<or> wire_source_domain sw_read_core \<noteq> sw_domain \<or>
              wire_principal sw_read_core \<noteq> sw_owner
            then None else
           Option.bind (select_native_scheduled_ack sw_owner sw_expected_ack sw_ack_core) (\<lambda>sw_native_ack.
           case code_source_nonreceipt_read_service sw_owner sw_read_core of
             Some (Service_Read sw_token sw_proof sw_target (Current_Data (Root_Balance sw_origin sw_account) sw_cut) None) \<Rightarrow>
               if proof_session sw_proof \<noteq> sw_session \<or> \<not> ss_auth sw_token sw_session (proof_epoch sw_proof) sw_data \<or>
                  sw_target \<noteq> sw_destination \<or> sw_origin \<noteq> (sw_domain,sw_event) \<or>
                  sw_account \<noteq> (sw_destination,sw_asset,sw_recipient) \<or>
                  sw_cut \<noteq> ss_cut sw_data
               then None else
               let sw_ack_result = step_one_slot (\<lambda>_. sw_verified = 1) (Slot_Ack sw_expected_ack)
                     (sw_dispatched_slot sw_publication sw_receiver)
               in case fst sw_ack_result of None \<Rightarrow> None | Some sw_after \<Rightarrow>
                  Some [sw_ack_label, sw_read_label, (if snd sw_ack_result = Settlement_Changed True then 1 else 0),
                        secondary_attempts sw_after, (if secondary_state sw_after = Secondary_Completed then 1 else 0),
                        scheduled_ack_amount sw_native_ack, ss_epoch sw_data, ss_revision sw_data,
                        ss_get (ss_funding sw_data) (sw_origin,sw_account),
                        origin_commit_position (publication_decision sw_publication)]
           | _ \<Rightarrow> None)))))
      | _ \<Rightarrow> None)"

definition sw_compatible_pair_integer :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "sw_compatible_pair_integer sw_fields sw_ack sw_read =
     (if list_all (\<lambda>sw_word. 0 \<le> sw_word) (sw_fields @ sw_ack @ sw_read) then
       map_option (map integer_of_nat) (sw_compatible_pair_words (map nat_of_integer sw_fields)
         (map nat_of_integer sw_ack) (map nat_of_integer sw_read)) else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sw_ack_and_current_have_compatible_product_footprints}) then ()
  else error "Unexpected oracle in signed schedule pair"
\<close>

export_code sw_compatible_pair_integer in SML module_name OIP_Signed_Schedule file_prefix "oip_signed_schedule"

end

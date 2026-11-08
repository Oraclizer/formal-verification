theory Reference_Wire_Schedule_Classifier
  imports "Reference_Wire_Schedule_Code"
begin

datatype 'token native_schedule_operand =
    Native_Schedule_ACK product_secondary_ack
  | Native_Schedule_Current 'token session_proof nat application_query product_cut "source_key option"

datatype native_schedule_dependency = Native_Authority | Native_Revision | Native_Completion
  | Native_Read_Provider | Native_Read_Origin source_key | Native_Queue_Slot settlement_identity

fun native_schedule_action where
  "native_schedule_action (Native_Schedule_ACK ack) = Service_Maintenance (Exact_Acknowledge ack)"
| "native_schedule_action (Native_Schedule_Current token proof target query requested origin) =
     Service_Read token proof target (Current_Data query requested) None"

fun native_schedule_footprint where
  "native_schedule_footprint (Native_Schedule_ACK ack) =
     ({Native_Authority, Native_Queue_Slot (ack_settlement_key ack)}, {Native_Queue_Slot (ack_settlement_key ack)})"
| "native_schedule_footprint (Native_Schedule_Current token proof target query requested origin) =
     ({Native_Authority, Native_Revision, Native_Completion, Native_Read_Provider} \<union>
        (case origin of None \<Rightarrow> {} | Some key \<Rightarrow> {Native_Read_Origin key}), {})"

definition native_schedule_compatible where
  "native_schedule_compatible first second \<longleftrightarrow>
     (let (read_first, write_first) = native_schedule_footprint first;
          (read_second, write_second) = native_schedule_footprint second
      in write_first \<inter> read_second = {} \<and> write_second \<inter> read_first = {} \<and> write_first \<inter> write_second = {})"

theorem the_native_ack_and_current_footprints_decide_actual_service_compatibility:
  "native_schedule_compatible first second =
     compatible_service_actions (native_schedule_action first) (native_schedule_action second) model"
  by (cases first; cases second)
     (auto simp: native_schedule_compatible_def compatible_service_actions_def service_access_footprint_def Let_def
       split: option.splits)

lemma dropping_only_native_compatibility_exchanges_two_eligible_ack_occurrences_for_one_slot:
  assumes "ack_settlement_key first = ack_settlement_key second" "eligible left" "eligible right"
  shows "rust_try_adjacent_exchange eligible True
       (native_schedule_compatible (Native_Schedule_ACK first) (Native_Schedule_ACK second))
       (selected,left,right) (selected,left,right) = Rust_Serialized selected left right"
    "rust_try_adjacent_exchange eligible True True (selected,left,right) (selected,left,right) =
       Rust_Exchanged selected left right"
  using assms by (simp_all add: native_schedule_compatible_def rust_try_adjacent_exchange_def Let_def)

context source_attestation
begin

theorem the_classified_native_exchange_refines_the_actual_reference_service_pair:
  fixes step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection
  defines "step \<equiv> \<lambda>action current.
      service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
        legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
        authenticated connection action None current"
  assumes initial: "related native before"
    and coherent: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and left: "\<And>n s. related n s \<Longrightarrow> related (fst (rust_left n)) (fst (step (native_schedule_action first) s)) \<and>
         convert (snd (rust_left n)) = snd (step (native_schedule_action first) s)"
    and right: "\<And>n s. related n s \<Longrightarrow> related (fst (rust_right n)) (fst (step (native_schedule_action second) s)) \<and>
         convert (snd (rust_right n)) = snd (step (native_schedule_action second) s)"
    and chosen: "rust_try_adjacent_exchange eligible distinct_keys (native_schedule_compatible first second)
       (rust_schedule_pair False rust_left rust_right native) (rust_schedule_pair True rust_left rust_right native) =
         Rust_Exchanged selected_image left_reply right_reply"
    and published: "reference_schedule_release observed current (selected_image,left_reply,right_reply) = Some released"
  shows "let (spec, left_result, right_result) =
       service_ordered_pair step (native_schedule_action first) (native_schedule_action second) before
    in related (fst released) spec \<and> convert (fst (snd released)) = left_result \<and>
       convert (snd (snd released)) = right_result"
proof -
  have native_compatible: "native_schedule_compatible first second"
    using a_rust_exchange_releases_only_the_checked_image_and_the_same_labeled_replies(3)[OF chosen] by blast
  have model_compatible: "compatible_service_actions (native_schedule_action first) (native_schedule_action second)
      (service_settlement (reopen_retained_product connection (reference_product before)))"
    using native_compatible the_native_ack_and_current_footprints_decide_actual_service_compatibility
      [of first second "service_settlement (reopen_retained_product connection (reference_product before))"] by blast
  show ?thesis unfolding step_def
    by (rule a_confirmed_rust_exchange_refines_the_actual_reference_service_pair[unfolded step_def,
          OF initial coherent model_compatible left[unfolded step_def] right[unfolded step_def] chosen published])
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_native_ack_and_current_footprints_decide_actual_service_compatibility
    dropping_only_native_compatibility_exchanges_two_eligible_ack_occurrences_for_one_slot
    source_attestation.the_classified_native_exchange_refines_the_actual_reference_service_pair})
  then () else error "Unexpected oracle in native wire schedule classification"
\<close>

end

theory Reference_Wire_Schedule_Code
  imports "Reference_Parallel_Consumption"
    "Reference_Product_Image"
begin

definition reference_transport_patch where
  "reference_transport_patch key bytes store =
    (case bytes of None \<Rightarrow> store | Some core_bytes \<Rightarrow> store(key := Some core_bytes))"

lemma different_wire_binding_writes_exchange:
  assumes "first \<noteq> second"
  shows "reference_transport_patch second second_bytes (reference_transport_patch first first_bytes store) =
      reference_transport_patch first first_bytes (reference_transport_patch second second_bytes store)"
  using assms by (cases first_bytes; cases second_bytes) (simp_all add: reference_transport_patch_def fun_upd_twist)

definition reference_schedule_release where
  "reference_schedule_release observed current prepared =
    (if observed = current then Some prepared else None)"

lemma a_new_authority_cut_cannot_release_the_old_schedule_replies:
  assumes "observed \<noteq> current"
  shows "reference_schedule_release observed current prepared = None"
  using assms by (simp add: reference_schedule_release_def)

context source_attestation
begin

theorem compatible_authenticated_wire_actions_keep_the_product_transport_and_labeled_replies:
  assumes coherent: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and actions: "compatible_service_actions first second
        (service_settlement (reopen_retained_product connection (reference_product before)))"
    and transport: "first_key \<noteq> second_key"
  shows "let run = (\<lambda>action current.
          service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
            legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
            authenticated connection action None current)
    in (service_ordered_pair run first second before,
        reference_transport_patch second_key second_bytes (reference_transport_patch first_key first_bytes wire)) =
       (service_exchanged_pair run first second before,
        reference_transport_patch first_key first_bytes (reference_transport_patch second_key second_bytes wire))"
  unfolding Let_def
  by (rule prod_eqI;
      simp only: fst_conv snd_conv;
      rule compatible_actions_exchange_in_the_actual_reference_service[OF coherent actions, unfolded Let_def]
        different_wire_binding_writes_exchange[OF transport])

end

record ('native, 'cut) rust_schedule_image =
  rust_schedule_payload :: 'native
  rust_schedule_store :: wire_dedup_store
  rust_schedule_cut :: 'cut

datatype ('reply, 'error) rust_schedule_reply =
  Rust_Scheduled bool 'reply | Rust_Schedule_Error 'error

definition rust_schedule_consume where
  "rust_schedule_consume operand key exact conflicting code =
    (let prior = rust_schedule_store code key in
      if prior \<noteq> None \<and> prior \<noteq> Some exact then (code, Rust_Schedule_Error conflicting)
      else case operand (rust_schedule_payload code) of Inr error \<Rightarrow> (code, Rust_Schedule_Error error)
      | Inl (next, reply) \<Rightarrow>
        (code\<lparr>rust_schedule_payload := next,
              rust_schedule_store := (if prior = None then (rust_schedule_store code)(key := Some exact)
                else rust_schedule_store code)\<rparr>, Rust_Scheduled (prior = None) reply))"

definition rust_schedule_image_matches where
  "rust_schedule_image_matches related code model transport current \<longleftrightarrow>
    related (rust_schedule_payload code) model \<and> rust_schedule_store code = transport \<and>
    rust_schedule_cut code = current"

lemma rust_schedule_consumer_refines_one_selected_operand:
  assumes initial: "rust_schedule_image_matches related code model transport current"
    and conflict: "transport key = None \<or> transport key = Some exact"
    and consumer: "related (rust_schedule_payload code) model \<Longrightarrow>
      \<exists>next reply. operand (rust_schedule_payload code) = Inl (next,reply) \<and>
        related next (fst (step model)) \<and> translate reply = snd (step model)"
  shows "\<exists>next reply. rust_schedule_consume operand key exact conflicting code = (next, Rust_Scheduled (transport key = None) reply) \<and>
      rust_schedule_image_matches related next (fst (step model))
        (reference_transport_patch key (if transport key = None then Some exact else None) transport) current \<and>
      translate reply = snd (step model)"
  using initial conflict consumer
  by (auto simp: rust_schedule_consume_def rust_schedule_image_matches_def reference_transport_patch_def Let_def)

lemma a_conflicting_transport_key_refuses_before_running_the_rust_operand:
  assumes "rust_schedule_store code key \<noteq> None" "rust_schedule_store code key \<noteq> Some exact"
  shows "rust_schedule_consume operand key exact conflicting code = (code, Rust_Schedule_Error conflicting)"
  using assms by (simp add: rust_schedule_consume_def Let_def)

definition rust_schedule_pair where
  "rust_schedule_pair swapped left right code =
    (if swapped then let (middle, second) = right code; (next, first) = left middle in (next, first, second)
     else let (middle, first) = left code; (next, second) = right middle in (next, first, second))"

datatype ('image, 'reply) rust_exchange_result =
  Rust_Exchange_Hold | Rust_Serialized 'image 'reply 'reply | Rust_Exchanged 'image 'reply 'reply

definition rust_try_adjacent_exchange where
  "rust_try_adjacent_exchange eligible distinct_keys compatible baseline alternate =
    (case baseline of (original, left, right) \<Rightarrow>
     if eligible left \<and> eligible right \<and> distinct_keys \<and> compatible then
       if baseline = alternate then (case alternate of (selected, first, second) \<Rightarrow> Rust_Exchanged selected first second)
       else Rust_Exchange_Hold
     else Rust_Serialized original left right)"

text \<open>The two operand simulations are obligations for the typed ACK and Current read consumers.
The conclusion compares the labels in input order, including the recorded First or Identical arrival.
The publication-side replay and authority check are represented by the separate release rule.\<close>
theorem actual_rust_pair_preserves_the_related_selected_order_and_each_labeled_reply:
  assumes initial: "related code model"
    and left: "\<And>native spec. related native spec \<Longrightarrow>
      related (fst (rust_left native)) (fst (model_left spec)) \<and> convert (snd (rust_left native)) = snd (model_left spec)"
    and right: "\<And>native spec. related native spec \<Longrightarrow>
      related (fst (rust_right native)) (fst (model_right spec)) \<and> convert (snd (rust_right native)) = snd (model_right spec)"
  shows "let (native, left_reply, right_reply) = rust_schedule_pair swapped rust_left rust_right code;
      (spec, first, second) = (if swapped then service_exchanged_pair (\<lambda>b. if b then model_left else model_right) True False model
                              else service_ordered_pair (\<lambda>b. if b then model_left else model_right) True False model)
    in related native spec \<and> convert left_reply = first \<and> convert right_reply = second"
  using left[OF initial] right[OF initial]
    left[OF conjunct1[OF right[OF initial]]] right[OF conjunct1[OF left[OF initial]]]
  by (cases swapped) (simp_all add: rust_schedule_pair_def service_exchanged_pair_def service_ordered_pair_def Let_def split_def)

theorem a_rust_exchange_releases_only_the_checked_image_and_the_same_labeled_replies:
  assumes "rust_try_adjacent_exchange eligible distinct_keys compatible baseline alternate = Rust_Exchanged selected_image left right"
  shows "baseline = (selected_image, left, right)" "alternate = (selected_image, left, right)"
    "eligible left \<and> eligible right \<and> distinct_keys \<and> compatible"
  using assms by (auto simp: rust_try_adjacent_exchange_def split: prod.splits if_splits)

lemma shared_transport_or_incompatible_slots_use_the_actual_original_run:
  assumes "\<not> distinct_keys \<or> \<not> compatible"
  shows "rust_try_adjacent_exchange eligible distinct_keys compatible (selected_image, left, right) alternate =
    Rust_Serialized selected_image left right"
  using assms by (auto simp: rust_try_adjacent_exchange_def)

context source_attestation
begin

theorem a_confirmed_rust_exchange_refines_the_actual_reference_service_pair:
  fixes step directory policy read_policy authenticate verify verify_read endorse approve
    legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
    authenticated connection
  defines "step \<equiv> \<lambda>action current.
      service_at_reference_snapshot directory policy read_policy authenticate verify verify_read endorse approve
        legal_grant order_verified spend_grant spend_verified read_permitted verified maintainers registered verified_ack
        authenticated connection action None current"
  assumes initial: "related native before"
    and coherent: "reference_grants_fit registered (reference_product before) (reference_inputs before)"
    and compatible: "compatible_service_actions first second
      (service_settlement (reopen_retained_product connection (reference_product before)))"
    and left: "\<And>n s. related n s \<Longrightarrow>
       related (fst (rust_left n)) (fst (step first s)) \<and> convert (snd (rust_left n)) = snd (step first s)"
    and right: "\<And>n s. related n s \<Longrightarrow>
       related (fst (rust_right n)) (fst (step second s)) \<and> convert (snd (rust_right n)) = snd (step second s)"
    and selected: "rust_try_adjacent_exchange eligible distinct_keys classifier
      (rust_schedule_pair False rust_left rust_right native) (rust_schedule_pair True rust_left rust_right native) =
        Rust_Exchanged selected_image left_reply right_reply"
    and publication: "reference_schedule_release observed current (selected_image,left_reply,right_reply) = Some released"
  shows "let (spec, left_result, right_result) = service_ordered_pair step first second before in
      related (fst released) spec \<and> convert (fst (snd released)) = left_result \<and>
      convert (snd (snd released)) = right_result"
proof -
  have pair: "rust_schedule_pair True rust_left rust_right native = (selected_image,left_reply,right_reply)"
    by (rule a_rust_exchange_releases_only_the_checked_image_and_the_same_labeled_replies(2)[OF selected])
  have simulation: "let (spec, l, r) = service_exchanged_pair step first second before in
    related selected_image spec \<and> convert left_reply = l \<and> convert right_reply = r"
    using actual_rust_pair_preserves_the_related_selected_order_and_each_labeled_reply
      [where swapped=True and related=related and code=native and model=before and convert=convert
         and rust_left=rust_left and rust_right=rust_right and model_left="step first" and model_right="step second",
       OF initial left right] pair
    by (simp add: service_exchanged_pair_def Let_def)
  have same: "service_ordered_pair step first second before = service_exchanged_pair step first second before"
    unfolding step_def
    by (rule compatible_actions_exchange_in_the_actual_reference_service[OF coherent compatible, unfolded Let_def])
  have released: "released = (selected_image,left_reply,right_reply)"
    using publication by (simp add: reference_schedule_release_def split: if_splits)
  show ?thesis using simulation unfolding same released by (simp add: split_def)
qed

end

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms different_wire_binding_writes_exchange
      a_new_authority_cut_cannot_release_the_old_schedule_replies
      rust_schedule_consumer_refines_one_selected_operand
      actual_rust_pair_preserves_the_related_selected_order_and_each_labeled_reply
      a_rust_exchange_releases_only_the_checked_image_and_the_same_labeled_replies
      shared_transport_or_incompatible_slots_use_the_actual_original_run
      source_attestation.a_confirmed_rust_exchange_refines_the_actual_reference_service_pair
      source_attestation.compatible_authenticated_wire_actions_keep_the_product_transport_and_labeled_replies})
  then () else error "Unexpected oracle in the ordered wire schedule relation"
\<close>

end

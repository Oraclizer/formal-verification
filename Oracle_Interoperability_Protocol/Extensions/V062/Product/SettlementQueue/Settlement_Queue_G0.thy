theory Settlement_Queue_G0
  imports "OIP_Reference_Execution.Reference_Queue_Code"
    "OIP_Reference_Profile.Reference_Scheduled_ACK_Wire"
    "HOL-Library.Code_Target_Nat"
begin

section \<open>Exact typed queue stage with the native funding owner retained\<close>

text \<open>The public product publication has no funding-owner field. The native
  Publication equality does. Keep the owner beside the public publication and
  project it only after checking that additional exact field. The primary payload
  below is arbitrary: queue operations do not inspect or replace it. The finite
  executable seed carries a publication projection, not a claimed complete
  PrimarySnapshot or an authenticated receiver journal.\<close>

type_synonym sq_publication = "product_publication \<times> nat"

record sq_job =
  sq_commitment :: sq_publication
  sq_job_target :: nat
  sq_attempts :: nat
  sq_phase :: secondary_status

record sq_ack =
  sq_ack_key :: settlement_identity
  sq_ack_commitment :: sq_publication
  sq_ack_target :: nat

record 'primary sq_queue =
  sq_primary :: 'primary
  sq_target :: nat
  sq_jobs :: "settlement_identity \<Rightarrow> sq_job option"

definition sq_max_attempts :: nat where
  "sq_max_attempts = 2^64 - 1"

definition sq_key where
  "sq_key published = settlement_key (fst published)"

definition sq_project_job where
  "sq_project_job job = \<lparr>rust_secondary_commitment = fst (sq_commitment job),
     rust_secondary_receiver = sq_job_target job, rust_secondary_tries = sq_attempts job,
     rust_secondary_phase = sq_phase job\<rparr>"

definition sq_product_job where
  "sq_product_job job = \<lparr>secondary_publication = fst (sq_commitment job),
     secondary_target = sq_job_target job, secondary_attempts = sq_attempts job,
     secondary_state = sq_phase job\<rparr>"

definition sq_project_queue where
  "sq_project_queue queue = \<lparr>rust_queue_primary = sq_primary queue,
     rust_queue_receiver = sq_target queue,
     rust_queue_rows = map_option sq_project_job \<circ> sq_jobs queue\<rparr>"

definition sq_project_ack where
  "sq_project_ack acknowledgement = \<lparr>ack_settlement_key = sq_ack_key acknowledgement,
     ack_publication = fst (sq_ack_commitment acknowledgement), ack_target = sq_ack_target acknowledgement\<rparr>"

definition sq_ack_local where
  "sq_ack_local acknowledgement job queue \<longleftrightarrow>
     sq_ack_key acknowledgement = sq_key (sq_commitment job) \<and>
     sq_ack_commitment acknowledgement = sq_commitment job \<and>
     sq_ack_target acknowledgement = sq_job_target job \<and>
     sq_ack_target acknowledgement = sq_target queue \<and> sq_attempts job > 0"

definition sq_acknowledge where
  "sq_acknowledge verify acknowledgement queue =
    (let queue_key = sq_ack_key acknowledgement in
     case sq_jobs queue queue_key of None \<Rightarrow> (queue,False)
      | Some job \<Rightarrow> if sq_ack_local acknowledgement job queue \<and> verify acknowledgement
          then (queue\<lparr>sq_jobs := (sq_jobs queue)(queue_key := Some (job\<lparr>sq_phase := Secondary_Completed\<rparr>))\<rparr>,True)
          else (queue,False))"

definition sq_acknowledge_without_publication where
  "sq_acknowledge_without_publication verify acknowledgement queue =
    (let queue_key = sq_ack_key acknowledgement in
     case sq_jobs queue queue_key of None \<Rightarrow> (queue,False)
      | Some job \<Rightarrow> if sq_ack_key acknowledgement = sq_key (sq_commitment job) \<and>
          sq_ack_target acknowledgement = sq_job_target job \<and>
          sq_ack_target acknowledgement = sq_target queue \<and> sq_attempts job > 0 \<and> verify acknowledgement
          then (queue\<lparr>sq_jobs := (sq_jobs queue)(queue_key := Some (job\<lparr>sq_phase := Secondary_Completed\<rparr>))\<rparr>,True)
          else (queue,False))"

definition sq_acknowledge_without_attempts where
  "sq_acknowledge_without_attempts verify acknowledgement queue =
    (let queue_key = sq_ack_key acknowledgement in
     case sq_jobs queue queue_key of None \<Rightarrow> (queue,False)
      | Some job \<Rightarrow> if sq_ack_key acknowledgement = sq_key (sq_commitment job) \<and>
          sq_ack_commitment acknowledgement = sq_commitment job \<and>
          sq_ack_target acknowledgement = sq_job_target job \<and>
          sq_ack_target acknowledgement = sq_target queue \<and> verify acknowledgement
          then (queue\<lparr>sq_jobs := (sq_jobs queue)(queue_key := Some (job\<lparr>sq_phase := Secondary_Completed\<rparr>))\<rparr>,True)
          else (queue,False))"

fun sq_dispatch_one where
  "sq_dispatch_one None = (None,None)"
| "sq_dispatch_one (Some job) =
    (if sq_phase job = Secondary_Completed \<or> sq_attempts job \<ge> sq_max_attempts then (Some job,None)
     else let next_job = job\<lparr>sq_attempts := Suc (sq_attempts job), sq_phase := Secondary_In_Flight\<rparr>
          in (Some next_job,Some next_job))"

fun sq_fail_one where
  "sq_fail_one None = (None,False)"
| "sq_fail_one (Some job) =
    (if sq_phase job = Secondary_In_Flight then (Some (job\<lparr>sq_phase := Secondary_Waiting\<rparr>),True)
     else (Some job,False))"

definition sq_dispatch where
  "sq_dispatch queue_key queue =
    (let result = sq_dispatch_one (sq_jobs queue queue_key) in
     (queue\<lparr>sq_jobs := (sq_jobs queue)(queue_key := fst result)\<rparr>,snd result))"

definition sq_fail where
  "sq_fail queue_key queue =
    (let result = sq_fail_one (sq_jobs queue queue_key) in
     (queue\<lparr>sq_jobs := (sq_jobs queue)(queue_key := fst result)\<rparr>,snd result))"

definition sq_owner_matches where
  "sq_owner_matches acknowledgement queue =
    (case sq_jobs queue (sq_ack_key acknowledgement) of None \<Rightarrow> False
     | Some job \<Rightarrow> snd (sq_ack_commitment acknowledgement) = snd (sq_commitment job))"

lemma sq_exact_native_ack_projects_to_the_existing_checked_row:
  "map_prod sq_project_queue id (sq_acknowledge verify acknowledgement queue) =
    rust_acknowledge_row (\<lambda>_. sq_owner_matches acknowledgement queue \<and> verify acknowledgement)
      (sq_project_ack acknowledgement) (sq_project_queue queue)"
  by (cases "sq_jobs queue (sq_ack_key acknowledgement)")
    (auto simp: sq_acknowledge_def sq_ack_local_def sq_key_def sq_owner_matches_def
      sq_project_ack_def sq_project_queue_def sq_project_job_def rust_acknowledge_row_def
      Let_def comp_def prod_eq_iff fun_eq_iff)

lemma sq_queue_actions_preserve_the_entire_primary:
  "sq_primary (fst (sq_dispatch queue_key queue)) = sq_primary queue"
  "sq_primary (fst (sq_fail queue_key queue)) = sq_primary queue"
  "sq_primary (fst (sq_acknowledge verify acknowledgement queue)) = sq_primary queue"
  by (simp_all add: sq_dispatch_def sq_fail_def sq_acknowledge_def Let_def split: option.splits if_splits)

lemma sq_dispatch_is_the_existing_bounded_slot_operation:
  "map_prod (map_option sq_product_job) (\<lambda>job. Settlement_Dispatched (map_option sq_product_job job))
      (sq_dispatch_one old_job) =
    step_one_slot verified (Slot_Dispatch queue_key) (map_option sq_product_job old_job)"
  by (cases old_job)
    (simp_all add: sq_product_job_def sq_max_attempts_def Let_def split: if_splits)

lemma sq_failure_is_the_existing_slot_operation:
  "map_prod (map_option sq_product_job) Settlement_Changed (sq_fail_one old_job) =
    step_one_slot verified (Slot_Fail queue_key) (map_option sq_product_job old_job)"
  by (cases old_job) (simp_all add: sq_product_job_def split: if_splits)

theorem sq_exact_ack_reuses_the_public_queue_correspondence:
  fixes sq_external_verify :: "sq_ack \<Rightarrow> bool"
    and sq_input_ack :: sq_ack
  assumes related: "rust_queue_matches primary_related (sq_project_queue queue) model"
    and targets: "native_queue_has_one_target model"
  defines "mapped_verifier \<equiv> (\<lambda>abstract_ack::product_secondary_ack. sq_owner_matches sq_input_ack queue \<and> sq_external_verify sq_input_ack)"
  shows "rust_queue_matches primary_related
       (sq_project_queue (fst (sq_acknowledge sq_external_verify sq_input_ack queue)))
       (fst (execute_settlement_action mapped_verifier (Exact_Acknowledge (sq_project_ack sq_input_ack)) model))"
    "sq_primary (fst (sq_acknowledge sq_external_verify sq_input_ack queue)) = sq_primary queue"
    "Settlement_Changed (snd (sq_acknowledge sq_external_verify sq_input_ack queue)) =
       snd (execute_settlement_action mapped_verifier (Exact_Acknowledge (sq_project_ack sq_input_ack)) model)"
proof -
  note reuse = rust_ack_consumes_the_related_queue_and_preserves_its_primary_and_reply[OF related targets,
    where verify=mapped_verifier and ack="sq_project_ack sq_input_ack"]
  have native: "rust_acknowledge_row mapped_verifier (sq_project_ack sq_input_ack) (sq_project_queue queue) =
      map_prod sq_project_queue id (sq_acknowledge sq_external_verify sq_input_ack queue)"
    unfolding mapped_verifier_def
    by (rule sym, rule sq_exact_native_ack_projects_to_the_existing_checked_row)
  show "rust_queue_matches primary_related
       (sq_project_queue (fst (sq_acknowledge sq_external_verify sq_input_ack queue)))
       (fst (execute_settlement_action mapped_verifier (Exact_Acknowledge (sq_project_ack sq_input_ack)) model))"
    "Settlement_Changed (snd (sq_acknowledge sq_external_verify sq_input_ack queue)) =
       snd (execute_settlement_action mapped_verifier (Exact_Acknowledge (sq_project_ack sq_input_ack)) model)"
    using reuse native by (simp_all add: Let_def)
  show "sq_primary (fst (sq_acknowledge sq_external_verify sq_input_ack queue)) = sq_primary queue"
    by (rule sq_queue_actions_preserve_the_entire_primary(3))
qed

lemma sq_dispatch_and_failure_keep_key_publication_target_and_owner:
  assumes old: "sq_jobs queue queue_key = Some job"
    and live: "sq_phase job \<noteq> Secondary_Completed" "sq_attempts job < sq_max_attempts"
  shows "sq_jobs (fst (sq_dispatch queue_key (fst (sq_fail queue_key queue)))) queue_key =
      Some (job\<lparr>sq_attempts := Suc (sq_attempts job),sq_phase := Secondary_In_Flight\<rparr>)"
  using assms by (cases "sq_phase job")
    (simp_all add: sq_dispatch_def sq_fail_def Let_def)

lemma sq_unrelated_queue_slot_is_untouched:
  assumes "other_key \<noteq> queue_key"
  shows "sq_jobs (fst (sq_dispatch queue_key queue)) other_key = sq_jobs queue other_key"
    "sq_jobs (fst (sq_fail queue_key queue)) other_key = sq_jobs queue other_key"
  using assms by (simp_all add: sq_dispatch_def sq_fail_def Let_def)

lemma sq_ack_with_no_attempt_cannot_invoke_the_accepting_branch:
  assumes "sq_jobs queue (sq_ack_key acknowledgement) = Some job" "sq_attempts job = 0"
  shows "sq_acknowledge verify acknowledgement queue = (queue,False)"
  using assms by (simp add: sq_acknowledge_def sq_ack_local_def Let_def)

lemma sq_funding_owner_is_not_erased_from_native_publication_equality:
  assumes "sq_jobs queue (sq_ack_key acknowledgement) = Some job"
    "snd (sq_ack_commitment acknowledgement) \<noteq> snd (sq_commitment job)"
  shows "sq_acknowledge verify acknowledgement queue = (queue,False)"
  using assms by (auto simp: sq_acknowledge_def sq_ack_local_def Let_def)

lemma sq_completed_job_can_reack_but_cannot_redispatch:
  assumes "sq_jobs queue queue_key = Some job" "sq_phase job = Secondary_Completed"
  shows "sq_dispatch queue_key queue = (queue,None)"
  using assms by (simp add: sq_dispatch_def Let_def fun_upd_idem)

section \<open>Nonempty canonical typed seeds\<close>

definition sq_key_less where
  "sq_key_less left_key right_key \<longleftrightarrow>
    fst (fst left_key) < fst (fst right_key) \<or>
    (fst (fst left_key) = fst (fst right_key) \<and>
      (snd (fst left_key) < snd (fst right_key) \<or>
        (snd (fst left_key) = snd (fst right_key) \<and> snd left_key < snd right_key)))"

fun sq_sorted_keys where
  "sq_sorted_keys [] = True"
| "sq_sorted_keys [queue_key] = True"
| "sq_sorted_keys (first_key # second_key # rest_keys) =
    (sq_key_less first_key second_key \<and> sq_sorted_keys (second_key # rest_keys))"

definition sq_primary_lookup where
  "sq_primary_lookup publications origin = List.find (\<lambda>published. publication_origin (fst published) = origin) publications"

definition sq_seed_row_valid where
  "sq_seed_row_valid target publications pair \<longleftrightarrow>
    (let queue_key = fst pair; job = snd pair; published = sq_commitment job in
     queue_key = sq_key published \<and> sq_job_target job = target \<and>
     sq_attempts job \<le> sq_max_attempts \<and>
     (sq_phase job = Secondary_Waiting \<or> sq_attempts job > 0) \<and>
     publication_origin (fst published) = binding_key (origin_binding (publication_decision (fst published))) \<and>
     sq_primary_lookup publications (publication_origin (fst published)) = Some published)"

definition sq_make_seed where
  "sq_make_seed target publications rows =
    (if rows = [] \<or> \<not> distinct (map (publication_origin \<circ> fst) publications) \<or>
        \<not> distinct (map fst rows) \<or> \<not> sq_sorted_keys (map fst rows) \<or>
        \<not> list_all (sq_seed_row_valid target publications) rows then None
     else Some \<lparr>sq_primary = publications,sq_target = target,sq_jobs = map_of rows\<rparr>)"

lemma sq_seed_is_nonempty_and_uses_data_equality:
  assumes "sq_make_seed target publications rows = Some queue"
  shows "rows \<noteq> []" "distinct (map fst rows)"
    "list_all (sq_seed_row_valid target publications) rows"
    "sq_primary queue = publications" "sq_target queue = target" "sq_jobs queue = map_of rows"
  using assms by (auto simp: sq_make_seed_def split: if_splits)

section \<open>Raw-fixture-representable publication and sharp branch witnesses\<close>

definition sq_fixture_publication :: sq_publication where
  "sq_fixture_publication =
    (\<lparr>publication_origin = (0,17),publication_decision =
       \<lparr>origin_binding = \<lparr>binding_key = (0,17),binding_asset = 17,binding_amount = 5,
          binding_destination = 2,binding_recipient = 3,binding_source_epoch = 9,
          binding_operation = Destination_Credit,binding_separator = 0\<rparr>,
        origin_kind = Confirmed_Decision,origin_epoch = 9,origin_commit_position = 2\<rparr>\<rparr>,7)"

definition sq_fixture_key :: settlement_identity where
  "sq_fixture_key = ((0,17),2)"

definition sq_fixture_job where
  "sq_fixture_job attempts phase = \<lparr>sq_commitment = sq_fixture_publication,sq_job_target = 0,
     sq_attempts = attempts,sq_phase = phase\<rparr>"

definition sq_fixture_queue where
  "sq_fixture_queue attempts phase = \<lparr>sq_primary = [sq_fixture_publication],sq_target = 0,
     sq_jobs = (\<lambda>_. None)(sq_fixture_key := Some (sq_fixture_job attempts phase))\<rparr>"

definition sq_fixture_ack where
  "sq_fixture_ack = \<lparr>sq_ack_key = sq_fixture_key,sq_ack_commitment = sq_fixture_publication,sq_ack_target = 0\<rparr>"

definition sq_wrong_recipient_publication where
  "sq_wrong_recipient_publication =
    (let publication = fst sq_fixture_publication; decision = publication_decision publication in
     (publication\<lparr>publication_decision := decision\<lparr>origin_binding := (origin_binding decision)\<lparr>binding_recipient := 4\<rparr>\<rparr>\<rparr>,
      snd sq_fixture_publication))"

definition sq_wrong_recipient_ack where
  "sq_wrong_recipient_ack = sq_fixture_ack\<lparr>sq_ack_commitment := sq_wrong_recipient_publication\<rparr>"

lemma sq_nonempty_canonical_fixture:
  "sq_make_seed 0 [sq_fixture_publication] [(sq_fixture_key,sq_fixture_job 0 Secondary_Waiting)] =
    Some (sq_fixture_queue 0 Secondary_Waiting)"
  by (simp add: sq_make_seed_def sq_seed_row_valid_def sq_primary_lookup_def sq_key_def
      settlement_key_def sq_fixture_publication_def sq_fixture_key_def sq_fixture_job_def
      sq_fixture_queue_def sq_max_attempts_def Let_def)

lemma sq_prior_attempts_single_removal:
  "sq_acknowledge (\<lambda>_. True) sq_fixture_ack (sq_fixture_queue 0 Secondary_Waiting) =
     (sq_fixture_queue 0 Secondary_Waiting,False)"
  "sq_acknowledge_without_attempts (\<lambda>_. True) sq_fixture_ack (sq_fixture_queue 0 Secondary_Waiting) =
     (sq_fixture_queue 0 Secondary_Completed,True)"
  by (simp_all add: sq_acknowledge_def sq_ack_local_def sq_acknowledge_without_attempts_def
      sq_fixture_ack_def sq_fixture_queue_def sq_fixture_job_def sq_fixture_key_def
      sq_key_def settlement_key_def sq_fixture_publication_def Let_def)

lemma sq_wrong_publication_with_the_same_key_reaches_that_guard:
  "sq_ack_key sq_wrong_recipient_ack = sq_fixture_key"
  "sq_key (sq_ack_commitment sq_wrong_recipient_ack) = sq_fixture_key"
  "sq_acknowledge (\<lambda>_. True) sq_wrong_recipient_ack (sq_fixture_queue 1 Secondary_In_Flight) =
     (sq_fixture_queue 1 Secondary_In_Flight,False)"
  "sq_acknowledge_without_publication (\<lambda>_. True) sq_wrong_recipient_ack (sq_fixture_queue 1 Secondary_In_Flight) =
     (sq_fixture_queue 1 Secondary_Completed,True)"
  by (simp_all add: sq_wrong_recipient_ack_def sq_wrong_recipient_publication_def sq_acknowledge_def
      sq_ack_local_def sq_acknowledge_without_publication_def sq_fixture_ack_def sq_fixture_queue_def
      sq_fixture_job_def sq_fixture_key_def sq_key_def settlement_key_def sq_fixture_publication_def Let_def)

lemma sq_dispatch_fail_retry_and_exact_ack_fixture:
  "sq_dispatch sq_fixture_key (sq_fixture_queue 0 Secondary_Waiting) =
     (sq_fixture_queue 1 Secondary_In_Flight,Some (sq_fixture_job 1 Secondary_In_Flight))"
  "sq_fail sq_fixture_key (sq_fixture_queue 1 Secondary_In_Flight) =
     (sq_fixture_queue 1 Secondary_Waiting,True)"
  "sq_dispatch sq_fixture_key (sq_fixture_queue 1 Secondary_Waiting) =
     (sq_fixture_queue 2 Secondary_In_Flight,Some (sq_fixture_job 2 Secondary_In_Flight))"
  "sq_acknowledge (\<lambda>_. True) sq_fixture_ack (sq_fixture_queue 2 Secondary_In_Flight) =
     (sq_fixture_queue 2 Secondary_Completed,True)"
  "sq_acknowledge (\<lambda>_. True) sq_fixture_ack (sq_fixture_queue 2 Secondary_Completed) =
     (sq_fixture_queue 2 Secondary_Completed,True)"
  by (simp_all add: numeral_2_eq_2[symmetric] sq_dispatch_def sq_fail_def sq_acknowledge_def sq_ack_local_def
      sq_fixture_ack_def sq_fixture_queue_def sq_fixture_job_def sq_fixture_key_def sq_key_def
      settlement_key_def sq_fixture_publication_def sq_max_attempts_def Let_def)

lemma sq_u64_dispatch_refuses_without_mutating_the_job:
  "sq_dispatch sq_fixture_key (sq_fixture_queue sq_max_attempts Secondary_Waiting) =
     (sq_fixture_queue sq_max_attempts Secondary_Waiting,None)"
  by (simp add: sq_dispatch_def sq_fixture_queue_def sq_fixture_job_def Let_def)

lemma sq_immutable_primary_is_the_same_after_the_nonempty_trace:
  "sq_primary (sq_fixture_queue 0 Secondary_Waiting) = sq_primary (sq_fixture_queue 2 Secondary_Completed)"
  by (simp add: sq_fixture_queue_def)

section \<open>External verification is separate from local typed guards\<close>

datatype sq_verification = SQ_Verified | SQ_Refuted | SQ_Unobserved
datatype sq_action = SQ_Dispatch settlement_identity | SQ_Fail settlement_identity | SQ_Ack sq_verification sq_ack
datatype sq_reply = SQ_Dispatch_Reply "sq_job option" | SQ_Changed bool | SQ_Verification_Unobserved

definition sq_ack_stage where
  "sq_ack_stage observation acknowledgement queue =
    (case sq_jobs queue (sq_ack_key acknowledgement) of None \<Rightarrow> (queue,SQ_Changed False)
     | Some job \<Rightarrow> if \<not> sq_ack_local acknowledgement job queue then (queue,SQ_Changed False)
       else case observation of SQ_Unobserved \<Rightarrow> (queue,SQ_Verification_Unobserved)
        | SQ_Verified \<Rightarrow> map_prod id SQ_Changed (sq_acknowledge (\<lambda>_. True) acknowledgement queue)
        | SQ_Refuted \<Rightarrow> map_prod id SQ_Changed (sq_acknowledge (\<lambda>_. False) acknowledgement queue))"

fun sq_step where
  "sq_step (SQ_Dispatch queue_key) queue = map_prod id SQ_Dispatch_Reply (sq_dispatch queue_key queue)"
| "sq_step (SQ_Fail queue_key) queue = map_prod id SQ_Changed (sq_fail queue_key queue)"
| "sq_step (SQ_Ack observation acknowledgement) queue = sq_ack_stage observation acknowledgement queue"

fun sq_trace where
  "sq_trace [] queue = []"
| "sq_trace (action # actions) queue =
    (let result = sq_step action queue in (snd result,fst result) # sq_trace actions (fst result))"

lemma sq_unobserved_verification_is_not_false:
  "sq_ack_stage SQ_Unobserved sq_fixture_ack (sq_fixture_queue 1 Secondary_In_Flight) =
     (sq_fixture_queue 1 Secondary_In_Flight,SQ_Verification_Unobserved)"
  "sq_ack_stage SQ_Refuted sq_fixture_ack (sq_fixture_queue 1 Secondary_In_Flight) =
     (sq_fixture_queue 1 Secondary_In_Flight,SQ_Changed False)"
  "sq_ack_stage SQ_Unobserved sq_fixture_ack (sq_fixture_queue 0 Secondary_Waiting) =
     (sq_fixture_queue 0 Secondary_Waiting,SQ_Changed False)"
  by (simp_all add: sq_ack_stage_def sq_acknowledge_def sq_ack_local_def sq_fixture_ack_def
      sq_fixture_queue_def sq_fixture_job_def sq_fixture_key_def sq_key_def settlement_key_def
      sq_fixture_publication_def Let_def)

lemma sq_every_typed_step_frames_the_primary:
  "sq_primary (fst (sq_step action queue)) = sq_primary queue"
  by (cases action)
    (simp_all add: sq_ack_stage_def sq_queue_actions_preserve_the_entire_primary
       Let_def split: option.splits sq_verification.splits)

section \<open>Input-only typed envelope parser and executable views\<close>

fun sq_parse_publication :: "nat list \<Rightarrow> sq_publication option" where
  "sq_parse_publication [domain,event,position,asset,owner,destination,recipient,amount,epoch,kind] =
    (if kind \<notin> {1,2} then None else Some
      (\<lparr>publication_origin = (domain,event),publication_decision =
        \<lparr>origin_binding = \<lparr>binding_key = (domain,event),binding_asset = asset,binding_amount = amount,
          binding_destination = destination,binding_recipient = recipient,binding_source_epoch = epoch,
          binding_operation = Destination_Credit,binding_separator = 0\<rparr>,
         origin_kind = (if kind = 1 then Confirmed_Decision else Reversed_Decision),origin_epoch = epoch,
         origin_commit_position = position\<rparr>\<rparr>,owner))"
| "sq_parse_publication _ = None"

fun sq_parse_phase where
  "sq_parse_phase 0 = Some Secondary_Waiting"
| "sq_parse_phase (Suc 0) = Some Secondary_In_Flight"
| "sq_parse_phase (Suc (Suc 0)) = Some Secondary_Completed"
| "sq_parse_phase _ = None"

fun sq_parse_job where
  "sq_parse_job (domain # event # position # target # attempts # phase # publication_words) =
    (case (sq_parse_phase phase,sq_parse_publication publication_words) of (Some status,Some published) \<Rightarrow>
       Some (((domain,event),position),\<lparr>sq_commitment = published,sq_job_target = target,sq_attempts = attempts,sq_phase = status\<rparr>)
     | _ \<Rightarrow> None)"
| "sq_parse_job _ = None"

fun sq_parse_ack where
  "sq_parse_ack (domain # event # position # target # publication_words) =
    map_option (\<lambda>published. \<lparr>sq_ack_key = ((domain,event),position),sq_ack_commitment = published,sq_ack_target = target\<rparr>)
      (sq_parse_publication publication_words)"
| "sq_parse_ack _ = None"

fun sq_parse_action :: "nat list \<Rightarrow> sq_action option" where
  "sq_parse_action [] = None"
| "sq_parse_action (action_tag # argument_words) =
    (if action_tag = 1 then
       (case argument_words of [domain,event,position] \<Rightarrow> Some (SQ_Dispatch ((domain,event),position)) | _ \<Rightarrow> None)
     else if action_tag = 2 then
       (case argument_words of [domain,event,position] \<Rightarrow> Some (SQ_Fail ((domain,event),position)) | _ \<Rightarrow> None)
     else if action_tag = 3 then
       (case argument_words of verification # acknowledgement_words \<Rightarrow>
          if verification > 2 then None else
          map_option (SQ_Ack (if verification = 0 then SQ_Refuted else if verification = 1 then SQ_Verified else SQ_Unobserved))
            (sq_parse_ack acknowledgement_words)
        | _ \<Rightarrow> None)
     else None)"

fun sq_collect where
  "sq_collect [] = Some []"
| "sq_collect (None # rest_values) = None"
| "sq_collect (Some value # rest_values) = map_option ((#) value) (sq_collect rest_values)"

definition sq_publication_words where
  "sq_publication_words published =
    (let core = fst published; decision = publication_decision core; binding = origin_binding decision in
     [fst (publication_origin core),snd (publication_origin core),origin_commit_position decision,
      binding_asset binding,snd published,binding_destination binding,binding_recipient binding,binding_amount binding,
      origin_epoch decision,(if origin_kind decision = Confirmed_Decision then 1 else 2)])"

fun sq_phase_word where
  "sq_phase_word Secondary_Waiting = 0"
| "sq_phase_word Secondary_In_Flight = 1"
| "sq_phase_word Secondary_Completed = 2"

definition sq_key_words where
  "sq_key_words queue_key = [fst (fst queue_key),snd (fst queue_key),snd queue_key]"

definition sq_job_words where
  "sq_job_words job = [sq_job_target job,sq_attempts job,sq_phase_word (sq_phase job)] @ sq_publication_words (sq_commitment job)"

definition sq_slot_words where
  "sq_slot_words queue queue_key =
    (case sq_jobs queue queue_key of None \<Rightarrow> [0] @ sq_key_words queue_key
     | Some job \<Rightarrow> [1] @ sq_key_words queue_key @ sq_job_words job)"

definition sq_state_words where
  "sq_state_words keys queue = [sq_target queue,length (sq_primary queue)] @
    concat (map sq_publication_words (sq_primary queue)) @ [length keys] @ concat (map (sq_slot_words queue) keys)"

fun sq_reply_words where
  "sq_reply_words SQ_Verification_Unobserved = [0]"
| "sq_reply_words (SQ_Dispatch_Reply None) = [1]"
| "sq_reply_words (SQ_Dispatch_Reply (Some job)) = [2] @ sq_job_words job"
| "sq_reply_words (SQ_Changed False) = [3]"
| "sq_reply_words (SQ_Changed True) = [4]"

definition sq_run_nat where
  "sq_run_nat target publication_rows queue_rows action_rows =
    (case (sq_collect (map sq_parse_publication publication_rows),sq_collect (map sq_parse_job queue_rows),
           sq_collect (map sq_parse_action action_rows)) of (Some publications,Some rows,Some actions) \<Rightarrow>
       (case sq_make_seed target publications rows of None \<Rightarrow> None | Some queue \<Rightarrow>
         Some (map (\<lambda>(reply,state). [sq_reply_words reply,sq_state_words (map fst rows) state]) (sq_trace actions queue)))
     | _ \<Rightarrow> None)"

definition sq_probe_result where
  "sq_probe_result keys result = [sq_reply_words (SQ_Changed (snd result)),sq_state_words keys (fst result)]"

definition sq_probe_nat where
  "sq_probe_nat target publication_rows queue_rows action_words =
    (case (sq_collect (map sq_parse_publication publication_rows),sq_collect (map sq_parse_job queue_rows),
           sq_parse_action action_words) of (Some publications,Some rows,Some (SQ_Ack observation acknowledgement)) \<Rightarrow>
       (case sq_make_seed target publications rows of None \<Rightarrow> None | Some queue \<Rightarrow>
          if observation = SQ_Unobserved then None else
          let verify = (\<lambda>_. observation = SQ_Verified); keys = map fst rows in
          Some [sq_probe_result keys (sq_acknowledge verify acknowledgement queue),
                sq_probe_result keys (sq_acknowledge_without_publication verify acknowledgement queue),
                sq_probe_result keys (sq_acknowledge_without_attempts verify acknowledgement queue)])
     | _ \<Rightarrow> None)"

definition sq_u64_integers :: "integer list \<Rightarrow> bool" where
  "sq_u64_integers values = list_all (\<lambda>value. 0 \<le> value \<and> value \<le> 18446744073709551615) values"

definition sq_run_flat where
  "sq_run_flat target publication_rows queue_rows action_rows =
    (if \<not> sq_u64_integers [target] \<or> \<not> list_all sq_u64_integers publication_rows \<or>
        \<not> list_all sq_u64_integers queue_rows \<or> \<not> list_all sq_u64_integers action_rows then None else
      let ns = map nat_of_integer in
      map_option (map (map (map integer_of_nat)))
        (sq_run_nat (nat_of_integer target) (map ns publication_rows) (map ns queue_rows) (map ns action_rows)))"

definition sq_probe_flat where
  "sq_probe_flat target publication_rows queue_rows action_words =
    (if \<not> sq_u64_integers [target] \<or> \<not> list_all sq_u64_integers publication_rows \<or>
        \<not> list_all sq_u64_integers queue_rows \<or> \<not> sq_u64_integers action_words then None else
      let ns = map nat_of_integer in
      map_option (map (map (map integer_of_nat)))
        (sq_probe_nat (nat_of_integer target) (map ns publication_rows) (map ns queue_rows) (ns action_words)))"

definition sq_export_identity :: "integer list" where
  "sq_export_identity = [1,64,10,16,14]"

lemma sq_input_words_name_the_raw_fixture_publication:
  "sq_parse_publication [0,17,2,17,7,2,3,5,9,1] = Some sq_fixture_publication"
  by (simp add: sq_fixture_publication_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sq_exact_native_ack_projects_to_the_existing_checked_row
      sq_queue_actions_preserve_the_entire_primary sq_dispatch_is_the_existing_bounded_slot_operation
      sq_failure_is_the_existing_slot_operation sq_exact_ack_reuses_the_public_queue_correspondence
      sq_dispatch_and_failure_keep_key_publication_target_and_owner sq_unrelated_queue_slot_is_untouched
      sq_ack_with_no_attempt_cannot_invoke_the_accepting_branch sq_funding_owner_is_not_erased_from_native_publication_equality
      sq_completed_job_can_reack_but_cannot_redispatch
      sq_seed_is_nonempty_and_uses_data_equality sq_nonempty_canonical_fixture sq_prior_attempts_single_removal
      sq_wrong_publication_with_the_same_key_reaches_that_guard sq_dispatch_fail_retry_and_exact_ack_fixture
      sq_u64_dispatch_refuses_without_mutating_the_job sq_immutable_primary_is_the_same_after_the_nonempty_trace
      sq_unobserved_verification_is_not_false sq_every_typed_step_frames_the_primary
      sq_input_words_name_the_raw_fixture_publication})
  then () else error "Unexpected oracle in typed settlement queue G0"
\<close>

export_code sq_run_flat sq_probe_flat sq_export_identity
  in SML module_name OIP_Settlement_Queue_G0 file_prefix "oip_settlement_queue_g0"

end

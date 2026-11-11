theory Schedule_Cases
  imports "OIP_Schedule_Product.Schedule_Product"
begin

datatype sc_queue_kind = SC_Enqueue | SC_Dispatch | SC_Fail

datatype sc_input =
    SC_Queue_Pair sc_queue_kind sc_queue_kind nat nat nat nat bool
  | SC_Read_Queue nat nat nat nat nat nat bool
  | SC_Shared_Cut nat nat nat bool
  | SC_Current_Read nat nat nat nat nat bool
  | SC_Policy nat nat nat nat bool
  | SC_Publish nat nat bool
  | SC_Namespace nat nat nat bool
  | SC_Finite nat nat nat nat nat
  | SC_Bounded nat nat

record sc_case =
  sc_seed :: "ss_data sp_state"
  sc_events :: "(nat \<times> (nat,ss_other) sp_action) list"
  sc_adjacent :: "nat list"
  sc_before_probes :: "(nat,ss_other) sp_action list"
  sc_after_probes :: "(nat,ss_other) sp_action list"

definition sc_binding where
  "sc_binding event asset = \<lparr>ss_origin = (0,event),ss_asset = asset,ss_owner = 7,
    ss_destination = 2,ss_recipient = 3,ss_amount = 5\<rparr>"

definition sc_swap where "sc_swap requested = (if requested then [0] else [])"

definition sc_case where
  "sc_case state events adjacent before_probes after_probes =
    \<lparr>sc_seed = state,sc_events = events,sc_adjacent = adjacent,
      sc_before_probes = before_probes,sc_after_probes = after_probes\<rparr>"

fun sc_queue_action :: "sc_queue_kind \<Rightarrow> sp_key \<Rightarrow> (nat,ss_other) sp_action" where
  "sc_queue_action SC_Enqueue key = SP_Enqueue_Action 99 (fst key)"
| "sc_queue_action SC_Dispatch key = SP_Dispatch_Action 99 key"
| "sc_queue_action SC_Fail key = SP_Fail_Action 99 key"

definition sc_enqueue :: "sp_key \<Rightarrow> ss_data sp_state \<Rightarrow> ss_data sp_state" where
  "sc_enqueue key state = fst (sp_execute ss_can_maintain ss_other_step
    (SP_Enqueue_Action (99::nat) (fst key)) state)"

definition sc_current :: "nat \<Rightarrow> nat \<Rightarrow> (nat,ss_other) sp_action" where
  "sc_current asset revision = SP_Other_Action
    (SS_Current 7 2 9 0 (SS_Application asset)
       \<lparr>cut_authority_epoch = 9,cut_revision = revision\<rparr>)"

definition sc_prepare_pair where
  "sc_prepare_pair first_kind second_kind first_origin second_origin first_selector second_selector requested =
    (case ss_fund (sc_binding 17 17) 10 True ss_initial of None \<Rightarrow> None
     | Some first_state \<Rightarrow> case ss_fund (sc_binding 22 22) 30 True first_state of None \<Rightarrow> None
       | Some second_state \<Rightarrow>
         (case (map_of (ss_decisions (sp_data second_state)) (0,17),
                map_of (ss_decisions (sp_data second_state)) (0,22)) of
           (Some sc_first_pub,Some sc_second_pub) \<Rightarrow>
             if first_selector < 2 \<and> second_selector < 2 then
               let sc_keys = [sp_key_of sc_first_pub,sp_key_of sc_second_pub];
                   sc_first_key = sc_keys ! first_selector; sc_second_key = sc_keys ! second_selector
               in if fst sc_first_key = (0,first_origin) \<and> fst sc_second_key = (0,second_origin) then
                    let sc_seeded_first = (if first_kind = SC_Enqueue then second_state else sc_enqueue sc_first_key second_state);
                        sc_seeded = (if sc_first_key = sc_second_key then sc_seeded_first else sc_enqueue sc_second_key sc_seeded_first)
                    in Some (sc_case sc_seeded [(1,sc_queue_action first_kind sc_first_key),(2,sc_queue_action second_kind sc_second_key)]
                         (sc_swap requested) [] [])
                  else None
             else None
         | _ \<Rightarrow> None))"

definition sc_prepare_read_queue where
  "sc_prepare_read_queue event epoch_id domain asset recipient amount requested =
    (if amount \<noteq> 5 then None else
      case ss_fund (sc_binding 17 17) 10 True ss_initial of None \<Rightarrow> None
      | Some state \<Rightarrow> case map_of (ss_decisions (sp_data state)) (0,17) of None \<Rightarrow> None
        | Some pub \<Rightarrow> if fst (sp_key_of pub) \<noteq> (0,event) then None
          else Some (sc_case (sc_enqueue (sp_key_of pub) state)
            [(1,SP_Other_Action (SS_Raw 7 1 epoch_id domain (SS_Account domain asset recipient))),
             (2,SP_Dispatch_Action 99 (sp_key_of pub))] (sc_swap requested) [] []))"

definition sc_prepare_shared_cut where
  "sc_prepare_shared_cut first_asset second_asset epoch_id requested =
    (let sc_left_request = (ss_make_request (sc_binding 17 first_asset) 1 (SS_Reserve 20) ss_initial)\<lparr>ss_auth_epoch := epoch_id\<rparr>;
         sc_right_request = (ss_make_request (sc_binding 22 second_asset) 2 (SS_Reserve 20) ss_initial)\<lparr>ss_auth_epoch := epoch_id\<rparr>
     in Some (sc_case ss_initial [(1,SP_Other_Action (SS_Execute sc_left_request)),(2,SP_Other_Action (SS_Execute sc_right_request))]
         (sc_swap requested) [] []))"

definition sc_prepare_current where
  "sc_prepare_current asset old_revision new_revision old_value new_value requested =
    (if ss_query_value (SS_Application asset) (ss_current (sp_data ss_initial)) \<noteq> old_value then None
     else let binding = sc_binding 18 asset;
         reserve = ss_make_request binding 1 (SS_Reserve 20) ss_initial;
         write = (ss_make_request binding 2 (SS_Write 0 new_value) ss_initial)\<lparr>
           ss_expected := \<lparr>cut_authority_epoch = 9,cut_revision = Suc old_revision\<rparr>\<rparr>;
         cancel = (ss_make_request binding 3 (SS_Cancel 0) ss_initial)\<lparr>
           ss_expected := \<lparr>cut_authority_epoch = 9,cut_revision = old_revision + 2\<rparr>\<rparr>
     in Some (sc_case ss_initial [(1,SP_Other_Action (SS_Execute reserve)),
          (2,SP_Other_Action (SS_Execute write)),(3,SP_Other_Action (SS_Execute cancel)),
          (4,sc_current asset old_revision)] (if requested then [2] else [])
          [sc_current asset old_revision] [sc_current asset new_revision]))"

definition sc_prepare_policy where
  "sc_prepare_policy old_epoch new_epoch asset revision requested = Some
    (sc_case ss_initial [(1,SP_Other_Action (SS_Install 99 new_epoch)),
      (2,SP_Other_Action (SS_Historical 7 1 old_epoch 0 (SS_Application asset) revision))]
      (sc_swap requested) [] [])"

definition sc_prepare_publish where
  "sc_prepare_publish first_origin second_origin requested =
    (if first_origin \<noteq> 17 \<or> second_origin \<noteq> 17 then None else
      case ss_fund (sc_binding 17 17) 10 False ss_initial of None \<Rightarrow> None
      | Some state \<Rightarrow>
        let publish = ss_make_request (sc_binding 17 17) 16 SS_Publish state;
            enqueue = SP_Enqueue_Action 99 (0,17)
        in Some (sc_case state [(1,SP_Other_Action (SS_Execute publish)),(2,enqueue)]
             (sc_swap requested) [enqueue] []))"

definition sc_prepare_namespace where
  "sc_prepare_namespace actor foreign_namespace sequence requested =
    (if actor \<noteq> 7 then None else
      let sc_left_request = ss_make_request (sc_binding 17 17) sequence (SS_Reserve 20) ss_initial;
          sc_right_request = (ss_make_request (sc_binding 22 22) sequence (SS_Reserve 20) ss_initial)\<lparr>ss_namespace := foreign_namespace\<rparr>
      in Some (sc_case ss_initial [(1,SP_Other_Action (SS_Execute sc_left_request)),(2,SP_Other_Action (SS_Execute sc_right_request))]
          (sc_swap requested) [] []))"

definition sc_prepare_finite where
  "sc_prepare_finite first_label second_label read_label first_origin second_origin =
    (case sc_prepare_pair SC_Dispatch SC_Dispatch first_origin second_origin 0 1 True of None \<Rightarrow> None
     | Some prepared \<Rightarrow> case sc_events prepared of [(label_a,action_a),(label_b,action_b)] \<Rightarrow>
         Some (prepared\<lparr>sc_events := [(first_label,action_a),(second_label,action_b),
           (read_label,SP_Other_Action (SS_Raw 7 1 9 2 (SS_Account 2 17 3)))],sc_adjacent := [0,1]\<rparr>)
       | _ \<Rightarrow> None)"

definition sc_prepare_bounded where
  "sc_prepare_bounded event attempts =
    (if attempts \<ge> 2^64 then None else
      case ss_fund (sc_binding 17 17) 10 True ss_initial of None \<Rightarrow> None
      | Some state \<Rightarrow> case map_of (ss_decisions (sp_data state)) (0,17) of None \<Rightarrow> None
        | Some pub \<Rightarrow> let key = sp_key_of pub; seeded = sc_enqueue key state in
          if fst key \<noteq> (0,event) then None else case sp_jobs seeded key of None \<Rightarrow> None
          | Some job \<Rightarrow> Some (sc_case (seeded\<lparr>sp_jobs := (sp_jobs seeded)(key := Some (job\<lparr>sp_job_attempts := attempts\<rparr>))\<rparr>)
              [(1,SP_Dispatch_Action 99 key)] [] [] []))"

fun sc_prepare where
  "sc_prepare (SC_Queue_Pair a b oa ob ca cb requested) = sc_prepare_pair a b oa ob ca cb requested"
| "sc_prepare (SC_Read_Queue event epoch_id domain asset recipient amount requested) =
     sc_prepare_read_queue event epoch_id domain asset recipient amount requested"
| "sc_prepare (SC_Shared_Cut a b epoch_id requested) = sc_prepare_shared_cut a b epoch_id requested"
| "sc_prepare (SC_Current_Read asset old_revision new_revision old_value new_value requested) =
     sc_prepare_current asset old_revision new_revision old_value new_value requested"
| "sc_prepare (SC_Policy old_epoch new_epoch asset revision requested) = sc_prepare_policy old_epoch new_epoch asset revision requested"
| "sc_prepare (SC_Publish a b requested) = sc_prepare_publish a b requested"
| "sc_prepare (SC_Namespace actor namespace sequence requested) = sc_prepare_namespace actor namespace sequence requested"
| "sc_prepare (SC_Finite a b c oa ob) = sc_prepare_finite a b c oa ob"
| "sc_prepare (SC_Bounded event attempts) = sc_prepare_bounded event attempts"

definition sc_execute where
  "sc_execute enforce requested prepared = sp_schedule enforce ss_can_maintain ss_classify_other ss_other_step
    (sc_events prepared) (if requested then sc_adjacent prepared else []) (sc_seed prepared)"

definition sc_probes where
  "sc_probes actions state = map (\<lambda>action. snd (sp_execute ss_can_maintain ss_other_step action state)) actions"

lemma sc_compatibility_mutant_keeps_exact_seed_events_and_plan:
  "sc_execute False True prepared = sp_schedule False ss_can_maintain ss_classify_other ss_other_step
    (sc_events prepared) (sc_adjacent prepared) (sc_seed prepared)"
  "sc_execute True True prepared = sp_schedule True ss_can_maintain ss_classify_other ss_other_step
    (sc_events prepared) (sc_adjacent prepared) (sc_seed prepared)"
  by (simp_all add: sc_execute_def)

lemma sc_declared_post_read_cut_is_not_a_state_assignment:
  "map_option sc_seed (sc_prepare_current asset old_revision first_new_cut old_value new_value requested) =
    map_option sc_seed (sc_prepare_current asset old_revision second_new_cut old_value new_value requested)"
  by (simp add: sc_prepare_current_def sc_case_def Let_def)

lemma sc_commit_selector_does_not_rewrite_a_publication:
  "ss_decisions (sp_data (sc_enqueue key state)) = ss_decisions (sp_data state)"
  "sp_publications (sc_enqueue key state) = sp_publications state"
  by (simp_all add: sc_enqueue_def sp_execute_def sp_queue_action_def Let_def split: option.splits)

text \<open>
  Inputs select operational fixture shapes; they do not supply a verdict,
  final cut, job output or after-image. Funding is executed, including terminal
  decision commit construction, before key-list selectors are used. The single
  bounded-attempt hook is an explicit native typed seed mutation; it is not a
  signed wire request. The old-value input checks the actual initial snapshot.
  The new-revision input is only the post-read expected cut. All input rows are
  run from freshly prepared state in baseline, guarded and one-guard-removed
  modes. Ground results are evaluated by exported code, not kernel-normalized
  into a large proof or supplied to the model as conclusions.
\<close>

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sc_compatibility_mutant_keeps_exact_seed_events_and_plan
      sc_declared_post_read_cut_is_not_a_state_assignment sc_commit_selector_does_not_rewrite_a_publication})
  then () else error "Unexpected oracle in closed scheduler input composition"
\<close>

end

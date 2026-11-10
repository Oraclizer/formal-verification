theory Ordered_Maintenance_G0
  imports Ordered_Maintenance_Source_Input
    "OIP_Reference_Profile.Reference_Witness_Selection"
    "OIP_Reference_Profile.Reference_Trusted_Time"
    "OIP_Product.Parallel_Examples"
begin

section \<open>Typed route and publication canary\<close>

datatype ordered_maintenance_action =
    Ordered_Observe_Time product_session_id nat
  | Ordered_Enqueue source_key
  | Ordered_Dispatch settlement_identity
  | Ordered_Fail settlement_identity

datatype ordered_maintenance_role = Ordered_Time_Key | Ordered_Queue_Key

fun ordered_maintenance_role_of where
  "ordered_maintenance_role_of (Ordered_Observe_Time session now) = Ordered_Time_Key"
| "ordered_maintenance_role_of action = Ordered_Queue_Key"

record ordered_maintenance_request =
  om_profile :: recovery_profile
  om_principal :: product_principal
  om_cut :: product_cut
  om_selection :: wire_bytes
  om_action :: ordered_maintenance_action

record 'key ordered_maintenance_policy =
  om_current_profile :: recovery_profile
  om_current_epoch :: nat
  om_local_maintainers :: "product_principal set"
  om_role_key :: "product_principal \<Rightarrow> ordered_maintenance_role \<Rightarrow> 'key option"
  om_trusted_now :: "nat option"

type_synonym 'head maintenance_witness = "'head reference_product_image reference_witness_cut"

fun ordered_maintenance_in_scope where
  "ordered_maintenance_in_scope (Ordered_Observe_Time session observed) now =
    (0 < observed \<and> (\<exists>current. now = Some current \<and> observed \<le> current))"
| "ordered_maintenance_in_scope action now = True"

definition ordered_maintenance_authenticated where
  "ordered_maintenance_authenticated policy verify token_actor request signature \<longleftrightarrow>
    token_actor = Some (om_principal request) \<and>
    om_profile request = om_current_profile policy \<and>
    cut_authority_epoch (om_cut request) = om_current_epoch policy \<and>
    ordered_maintenance_in_scope (om_action request) (om_trusted_now policy) \<and>
    (\<exists>key. om_role_key policy (om_principal request) (ordered_maintenance_role_of (om_action request)) = Some key
      \<and> verify key request signature)"

definition open_generic_maintenance :: "bool \<Rightarrow> bool \<Rightarrow> product_principal option \<Rightarrow> product_principal option" where
  "open_generic_maintenance attached_ordered configured_ordered local_actor =
    (if attached_ordered \<or> configured_ordered then None else local_actor)"

definition ordered_maintenance_current_authority where
  "ordered_maintenance_current_authority policy verify token_actor request signature opened_head observed \<longleftrightarrow>
    (let frame = witness_control observed in
      ordered_maintenance_authenticated policy verify token_actor request signature \<and>
      om_principal request \<in> om_local_maintainers policy \<and>
      om_principal request \<notin> control_revoked (image_ordered_control frame) \<and>
      control_head (image_ordered_control frame) = Some opened_head \<and>
      om_cut request = reference_observed_cut (image_read_history frame))"

definition select_ordered_maintenance where
  "select_ordered_maintenance selection_of policy verify token_actor request signature opened_head observed =
    (if ordered_maintenance_current_authority policy verify token_actor request signature opened_head observed \<and>
        om_selection request = selection_of observed then Some observed else None)"

definition ordered_maintenance_records where
  "ordered_maintenance_records observed_cut = reference_product (image_authority (witness_control observed_cut))"

definition maintenance_dispatch_effect where
  "maintenance_dispatch_effect verified request R =
    (case om_action request of Ordered_Dispatch key \<Rightarrow>
      let result = step_settlement_slot verified (Slot_Dispatch key) (retained_secondary R)
      in Some (R\<lparr>retained_secondary := fst result\<rparr>, snd result)
    | _ \<Rightarrow> None)"

definition consume_generic_dispatch where
  "consume_generic_dispatch attached_ordered configured_ordered local_actor verified request R =
    (case open_generic_maintenance attached_ordered configured_ordered local_actor of
       None \<Rightarrow> (R, None)
     | Some _ \<Rightarrow> (case maintenance_dispatch_effect verified request R of
         None \<Rightarrow> (R, None) | Some (after, reply) \<Rightarrow> (after, Some reply)))"

definition maintenance_proposal where
  "maintenance_proposal archive before new_head R =
    (let frame = witness_control before;
         authority = (image_authority frame)\<lparr>reference_product := R\<rparr>;
         control = image_ordered_control frame;
         changed = (record_reference_product_image authority 0 frame)
           \<lparr>image_ordered_control := control\<lparr>control_revision := Suc (control_revision control),
             control_head := Some new_head\<rparr>\<rparr>;
         next = before\<lparr>witness_version := Suc (witness_version before), witness_control := changed\<rparr>
     in \<lparr>proposal_before = before, proposal_after = next, proposal_archive = archive\<rparr>)"

definition publish_maintenance_dispatch where
  "publish_maintenance_dispatch archive_bound archives archive reauthenticated before live new_head candidate =
    (if \<not> reauthenticated then (live, None)
     else case candidate of None \<Rightarrow> (live, None)
       | Some (R, reply) \<Rightarrow>
           if R = ordered_maintenance_records before then
             (case witnessed_current archive_bound archives before live of None \<Rightarrow> (live, None)
              | Some _ \<Rightarrow> (live, Some reply))
           else
             (case witnessed_selection archive_bound archives (maintenance_proposal archive before new_head R) live of
                None \<Rightarrow> (live, None) | Some after \<Rightarrow> (after, Some reply)))"

definition consume_selected_dispatch where
  "consume_selected_dispatch archive_bound archives archive reauthenticated checked verified request live new_head =
    (case checked of None \<Rightarrow> (live, None)
     | Some before \<Rightarrow> publish_maintenance_dispatch archive_bound archives archive reauthenticated before live new_head
         (maintenance_dispatch_effect verified request (ordered_maintenance_records before)))"

lemma generic_maintenance_route_controls:
  "open_generic_maintenance True False (Some actor) = None"
  "open_generic_maintenance False True (Some actor) = None"
  "open_generic_maintenance False False (Some actor) = Some actor"
  "open_generic_maintenance False False None = None"
  by (simp_all add: open_generic_maintenance_def)

context source_attestation
begin

lemma maintenance_dispatch_reuses_the_real_recovered_queue_step:
  assumes action: "om_action request = Ordered_Dispatch key"
  shows "map_option (map_prod id Scheduled_Settlement) (maintenance_dispatch_effect verified_ack request R) =
    Some (schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance (Exact_Dispatch_Secondary key)) R)"
proof -
  have slot: "classify_service_action (Service_Maintenance (Exact_Dispatch_Secondary key))
      (service_settlement (reopen_retained_product connection R)) = Service_Slot (Slot_Dispatch key)"
    by simp
  let ?step = "step_settlement_slot verified_ack (Slot_Dispatch key) (retained_secondary R)"
  have scheduled: "schedule_at_retained_state directory policy read_policy authenticate verify verify_read endorse approve
      legal_grant order_verified spend_grant spend_verified read_permitted permitted verified maintainers registered verified_ack
      connection (Service_Maintenance (Exact_Dispatch_Secondary key)) R =
      (R\<lparr>retained_secondary := fst ?step\<rparr>, Scheduled_Settlement (snd ?step))"
    by (rule classified_settlement_action_updates_only_its_real_slot[OF slot, unfolded Let_def])
  show ?thesis using action
    by (simp add: maintenance_dispatch_effect_def Let_def scheduled)
qed

end

lemma a_moved_witness_cut_blocks_dispatch_publication_and_reply:
  assumes moved: "before \<noteq> live"
  shows "publish_maintenance_dispatch archive_bound archives archive reauthenticated before live new_head candidate =
    (live, None)"
  using moved
  by (cases candidate)
    (auto simp: publish_maintenance_dispatch_def witnessed_current_def witnessed_selection_def maintenance_proposal_def
      Let_def split: prod.splits)

section \<open>Source-bound typed input and model observations\<close>

definition source_maintenance_request :: ordered_maintenance_request where
  "source_maintenance_request =
    \<lparr>om_profile = maintenance_input_profile, om_principal = maintenance_input_principal,
      om_cut = maintenance_input_product_cut, om_selection = maintenance_input_selection,
      om_action = Ordered_Observe_Time (fst maintenance_input_observe_time) (snd maintenance_input_observe_time)\<rparr>"

lemma source_input_selects_the_time_role:
  "ordered_maintenance_role_of (om_action source_maintenance_request) = Ordered_Time_Key"
  "ordered_maintenance_in_scope (om_action source_maintenance_request) (Some 105)"
  by (simp_all add: source_maintenance_request_def maintenance_input_observe_time_def)

definition dispatch_witness :: "nat maintenance_witness" where
  "dispatch_witness =
    (let R = capture_retained_product parallel_example_world;
         authority = \<lparr>reference_product = R, reference_inputs =
           \<lparr>reference_epoch = 9, reference_grants = (\<lambda>_. {})\<rparr>\<rparr>;
         frame = \<lparr>image_authority = authority,
           image_read_history = initialize_reference_history 9 (capture_reference_view authority),
           image_transport = (\<lambda>_. None),
           image_ordered_control = \<lparr>control_revision = 0, control_head = Some 1, control_writer = 0,
             control_revoked = {}, control_cancelled = {}, control_decisions = (\<lambda>_. None),
             control_latest = (\<lambda>_. None)\<rparr>\<rparr>
     in \<lparr>witness_version = 0, witness_generation = 0, witness_control = frame\<rparr>)"

definition fixture_selection where
  "fixture_selection observed_cut = replicate 32 (witness_version observed_cut)"

definition dispatch_request where
  "dispatch_request = \<lparr>om_profile = maintenance_input_profile, om_principal = maintenance_input_principal,
    om_cut = reference_observed_cut (image_read_history (witness_control dispatch_witness)),
    om_selection = fixture_selection dispatch_witness, om_action = Ordered_Dispatch parallel_example_key\<rparr>"

definition dispatch_policy :: "nat ordered_maintenance_policy" where
  "dispatch_policy = \<lparr>om_current_profile = maintenance_input_profile, om_current_epoch = 9,
    om_local_maintainers = {maintenance_input_principal}, om_role_key =
      (\<lambda>actor role. if actor = maintenance_input_principal \<and> role = Ordered_Queue_Key then Some 11 else None),
    om_trusted_now = None\<rparr>"

definition dispatch_verifier :: "nat \<Rightarrow> ordered_maintenance_request \<Rightarrow> nat \<Rightarrow> bool" where
  "dispatch_verifier key request signature \<longleftrightarrow> key = 11 \<and> request = dispatch_request \<and> signature = 42"

abbreviation dispatch_actor where
  "dispatch_actor \<equiv> Some maintenance_input_principal"

abbreviation dispatch_authenticated where
  "dispatch_authenticated \<equiv> ordered_maintenance_authenticated dispatch_policy dispatch_verifier dispatch_actor dispatch_request 42"

abbreviation dispatch_selection where
  "dispatch_selection \<equiv> select_ordered_maintenance fixture_selection dispatch_policy dispatch_verifier dispatch_actor dispatch_request 42 1"

abbreviation dispatch_candidate where
  "dispatch_candidate observed_cut \<equiv> maintenance_dispatch_effect (\<lambda>_. False) dispatch_request (ordered_maintenance_records observed_cut)"

abbreviation dispatched_job where
  "dispatched_job \<equiv> queue_example_job\<lparr>secondary_attempts := 1, secondary_state := Secondary_In_Flight\<rparr>"

definition dispatch_archive_binds where
  "dispatch_archive_binds R observed_cut \<longleftrightarrow> R = ordered_maintenance_records observed_cut"

definition dispatch_advance_witness where
  "dispatch_advance_witness = dispatch_witness\<lparr>witness_version := Suc (witness_version dispatch_witness)\<rparr>"

lemma current_dispatch_guard_fires:
  "dispatch_authenticated"
  "dispatch_selection dispatch_witness = Some dispatch_witness"
  "ordered_maintenance_current_authority dispatch_policy dispatch_verifier dispatch_actor dispatch_request 42 1 dispatch_advance_witness"
  by (simp_all add: select_ordered_maintenance_def ordered_maintenance_current_authority_def
    ordered_maintenance_authenticated_def dispatch_policy_def dispatch_verifier_def dispatch_request_def
    dispatch_advance_witness_def dispatch_witness_def fixture_selection_def initialize_reference_history_def
    reference_observed_cut_def Let_def)

lemma a_reopened_dispatch_has_the_existing_queued_job:
  "retained_secondary (ordered_maintenance_records dispatch_witness) parallel_example_key = Some queue_example_job"
  by (simp add: ordered_maintenance_records_def dispatch_witness_def capture_retained_product_def parallel_example_world_def
    initial_regulated_product_def initial_governed_world_def initial_legal_world_def initial_product_reads_def
    parallel_example_settlement_def checked_primary_commitment_opens_one_secondary_job Let_def)

lemma staged_dispatch_uses_the_existing_queued_job:
  "dispatch_candidate dispatch_witness =
    Some ((ordered_maintenance_records dispatch_witness)\<lparr>retained_secondary :=
      (retained_secondary (ordered_maintenance_records dispatch_witness))(parallel_example_key := Some dispatched_job)\<rparr>,
      Settlement_Dispatched (Some dispatched_job))"
  by (simp add: maintenance_dispatch_effect_def dispatch_request_def step_settlement_slot_def
    a_reopened_dispatch_has_the_existing_queued_job queue_example_job_def Let_def)

abbreviation dispatch_after where
  "dispatch_after \<equiv> (ordered_maintenance_records dispatch_witness)\<lparr>retained_secondary :=
    (retained_secondary (ordered_maintenance_records dispatch_witness))(parallel_example_key := Some dispatched_job)\<rparr>"

abbreviation commit_dispatch where
  "commit_dispatch before live candidate \<equiv> publish_maintenance_dispatch dispatch_archive_binds {dispatch_after}
    dispatch_after dispatch_authenticated before live 2 candidate"

abbreviation consume_dispatch where
  "consume_dispatch checked live \<equiv> consume_selected_dispatch dispatch_archive_binds {dispatch_after} dispatch_after
    dispatch_authenticated checked (\<lambda>_. False) dispatch_request live 2"

lemma dispatch_changes_the_job_and_releases_the_exact_result:
  "ordered_maintenance_records (fst (consume_dispatch (dispatch_selection dispatch_witness) dispatch_witness)) = dispatch_after"
  "snd (consume_dispatch (dispatch_selection dispatch_witness) dispatch_witness) = Some (Settlement_Dispatched (Some dispatched_job))"
  "witness_version (fst (consume_dispatch (dispatch_selection dispatch_witness) dispatch_witness)) = 1"
proof -
  have changed: "dispatch_after \<noteq> ordered_maintenance_records dispatch_witness"
  proof
    assume "dispatch_after = ordered_maintenance_records dispatch_witness"
    then have "retained_secondary dispatch_after parallel_example_key =
        retained_secondary (ordered_maintenance_records dispatch_witness) parallel_example_key" by simp
    with a_reopened_dispatch_has_the_existing_queued_job show False by (simp add: queue_example_job_def)
  qed
  let ?proposal = "maintenance_proposal dispatch_after dispatch_witness 2 dispatch_after"
  have selected: "ordered_maintenance_records (proposal_after ?proposal) = dispatch_after"
    by (simp add: ordered_maintenance_records_def maintenance_proposal_def record_reference_product_image_def Let_def)
  have bound: "dispatch_archive_binds dispatch_after (proposal_after ?proposal)"
    using selected by (simp only: dispatch_archive_binds_def)
  have version: "witness_version (proposal_after ?proposal) = 1"
    by (simp add: maintenance_proposal_def dispatch_witness_def Let_def)
  have picked: "witnessed_selection dispatch_archive_binds {dispatch_after} ?proposal dispatch_witness = Some (proposal_after ?proposal)"
    using bound by (simp add: witnessed_selection_def maintenance_proposal_def Let_def)
  have published: "consume_dispatch (dispatch_selection dispatch_witness) dispatch_witness =
      (proposal_after ?proposal, Some (Settlement_Dispatched (Some dispatched_job)))"
    by (simp only: current_dispatch_guard_fires(1,2) consume_selected_dispatch_def option.simps
      publish_maintenance_dispatch_def staged_dispatch_uses_the_existing_queued_job prod.case changed picked
      not_True_eq_False if_True if_False)
  show "ordered_maintenance_records (fst (consume_dispatch (dispatch_selection dispatch_witness) dispatch_witness)) = dispatch_after"
    using published selected by simp
  show "snd (consume_dispatch (dispatch_selection dispatch_witness) dispatch_witness) = Some (Settlement_Dispatched (Some dispatched_job))"
    using published by simp
  show "witness_version (fst (consume_dispatch (dispatch_selection dispatch_witness) dispatch_witness)) = 1"
    using published version by simp
qed

lemma generic_dispatch_uses_the_standalone_authority_and_stops_on_ordered_authority:
  "consume_generic_dispatch False False dispatch_actor (\<lambda>_. False) dispatch_request
    (ordered_maintenance_records dispatch_witness) = (dispatch_after, Some (Settlement_Dispatched (Some dispatched_job)))"
  "consume_generic_dispatch True False dispatch_actor (\<lambda>_. False) dispatch_request
    (ordered_maintenance_records dispatch_witness) = (ordered_maintenance_records dispatch_witness, None)"
  "consume_generic_dispatch False True dispatch_actor (\<lambda>_. False) dispatch_request
    (ordered_maintenance_records dispatch_witness) = (ordered_maintenance_records dispatch_witness, None)"
  by (simp_all add: consume_generic_dispatch_def open_generic_maintenance_def staged_dispatch_uses_the_existing_queued_job)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms generic_maintenance_route_controls
      source_attestation.maintenance_dispatch_reuses_the_real_recovered_queue_step
      a_moved_witness_cut_blocks_dispatch_publication_and_reply source_input_selects_the_time_role
      current_dispatch_guard_fires a_reopened_dispatch_has_the_existing_queued_job staged_dispatch_uses_the_existing_queued_job
      dispatch_changes_the_job_and_releases_the_exact_result generic_dispatch_uses_the_standalone_authority_and_stops_on_ordered_authority})
  then () else error "Unexpected oracle in ordered maintenance feasibility core"
\<close>

end

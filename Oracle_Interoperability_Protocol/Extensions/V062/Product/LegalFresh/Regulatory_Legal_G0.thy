theory Regulatory_Legal_G0
  imports "OIP_Reference_Execution.Reference_Legal_Code"
    "OIP_Reference_Execution.Reference_Trace_Regulation"
    "HOL-Library.Code_Target_Nat"
begin

section \<open>Fresh typed confiscation before the native issuance check\<close>

text \<open>The public legal predicates are imported unchanged. This unit models
  the native fresh, unapplied branch after current session, payload/cut, ordinary
  origin exclusion and commit-resource admission. Legal/provider/crypto evidence
  remains external. Refusal preserves this legal-effect projection; a retained
  refusal receipt is a separate write outside this projection.\<close>

record lg_request =
  lg_order :: product_legal_order
  lg_native_words :: "nat list"
  lg_scope_words :: "nat list"

record lg_event =
  lg_event_action :: reg_action
  lg_event_asset :: nat
  lg_event_applied :: bool
  lg_event_parent :: "source_key option"
  lg_event_deadline :: "nat option"

record lg_state =
  lg_epoch :: nat
  lg_clock :: nat
  lg_money :: "nat list"
  lg_modes :: "(nat \<times> nat) \<Rightarrow> reg_state option"
  lg_events :: "source_key \<Rightarrow> lg_event option"
  lg_freezes :: "nat \<Rightarrow> source_key option"
  lg_seizures :: "nat \<Rightarrow> source_key option"
  lg_grants :: "nat list list"
  lg_enrollments :: "nat list list"
  lg_current_issued :: "(nat list \<times> nat list) option"
  lg_current_applied :: bool

datatype lg_evidence = LG_Verified | LG_Refuted | LG_Unobserved
datatype lg_reply = LG_Emitted | LG_Applied | LG_Refused legal_refusal | LG_Evidence_Unobserved | LG_Outside_Fresh_Scope

fun lg_stage_code where
  "lg_stage_code Legal_Source_Emission = 0"
| "lg_stage_code Legal_Receiving_Commit = 1"

fun lg_route_code where
  "lg_route_code Regulatory_Normal = 0"
| "lg_route_code Regulatory_Administrative = 1"
| "lg_route_code Regulatory_Adapter = 2"
| "lg_route_code Regulatory_Force_Inclusion = 3"

definition lg_exact_order where
  "lg_exact_order request = (lg_native_words request,lg_scope_words request)"

definition lg_prior_event where
  "lg_prior_event state event_key action asset =
    (case lg_events state event_key of None \<Rightarrow> None | Some prior_event \<Rightarrow>
       if lg_event_applied prior_event \<and> lg_event_action prior_event = action \<and> lg_event_asset prior_event = asset
       then Some prior_event else None)"

definition lg_active_freeze where
  "lg_active_freeze state asset =
    (case lg_freezes state asset of None \<Rightarrow> None | Some freeze_key \<Rightarrow>
       if lg_prior_event state freeze_key FREEZE asset = None then None else Some freeze_key)"

definition lg_active_seizure where
  "lg_active_seizure state asset =
    (case lg_seizures state asset of None \<Rightarrow> None | Some seizure_key \<Rightarrow>
       (case (lg_prior_event state seizure_key SEIZE asset,lg_active_freeze state asset) of
          (Some seizure_event,Some freeze_key) \<Rightarrow>
            if lg_event_parent seizure_event = Some freeze_key
            then Some (seizure_key,lg_event_deadline seizure_event) else None
        | _ \<Rightarrow> None))"

definition lg_source_mode where
  "lg_source_mode state request = lg_modes state (fst (legal_origin (lg_order request)),legal_asset (lg_order request))"

definition lg_receiver_mode where
  "lg_receiver_mode state request = lg_modes state
    (binding_destination (legal_binding (lg_order request)),legal_asset (lg_order request))"

definition lg_transition where
  "lg_transition state request = native_confiscation_gate (lg_order request)
    (lg_source_mode state request) (lg_receiver_mode state request)
    (lg_active_seizure state (legal_asset (lg_order request))) (lg_clock state)"

definition lg_native_gate_without_recorded_deadline where
  "lg_native_gate_without_recorded_deadline order source_mode receiver_mode seizure now =
    (if source_mode = None \<or> source_mode \<noteq> receiver_mode then Legal_Refuse Invalid_Legal_State
     else case seizure of None \<Rightarrow> Legal_Refuse Missing_Prior_Seizure
      | Some (seizure_key,recorded_deadline) \<Rightarrow>
        if source_mode \<noteq> Some SEIZED \<or> legal_predecessor order \<noteq> Some seizure_key
        then Legal_Refuse Missing_Prior_Seizure
        else case legal_appeal_deadline order of None \<Rightarrow> Legal_Refuse Appeal_Deadline_Mismatch
         | Some supplied_deadline \<Rightarrow> if now < supplied_deadline then Legal_Refuse Appeal_Still_Open
            else if legal_destination order = None then Legal_Refuse Missing_Confiscation_Destination else Legal_Admit)"

definition lg_native_gate_without_elapsed_time where
  "lg_native_gate_without_elapsed_time order source_mode receiver_mode seizure now =
    (if source_mode = None \<or> source_mode \<noteq> receiver_mode then Legal_Refuse Invalid_Legal_State
     else case seizure of None \<Rightarrow> Legal_Refuse Missing_Prior_Seizure
      | Some (seizure_key,recorded_deadline) \<Rightarrow>
        if source_mode \<noteq> Some SEIZED \<or> legal_predecessor order \<noteq> Some seizure_key
        then Legal_Refuse Missing_Prior_Seizure
        else case legal_appeal_deadline order of None \<Rightarrow> Legal_Refuse Appeal_Deadline_Mismatch
         | Some supplied_deadline \<Rightarrow>
            if recorded_deadline \<noteq> Some supplied_deadline then Legal_Refuse Appeal_Deadline_Mismatch
            else if legal_destination order = None then Legal_Refuse Missing_Confiscation_Destination else Legal_Admit)"

definition lg_transition_without_recorded_deadline where
  "lg_transition_without_recorded_deadline state request = lg_native_gate_without_recorded_deadline (lg_order request)
    (lg_source_mode state request) (lg_receiver_mode state request)
    (lg_active_seizure state (legal_asset (lg_order request))) (lg_clock state)"

definition lg_transition_without_elapsed_time where
  "lg_transition_without_elapsed_time state request = lg_native_gate_without_elapsed_time (lg_order request)
    (lg_source_mode state request) (lg_receiver_mode state request)
    (lg_active_seizure state (legal_asset (lg_order request))) (lg_clock state)"

definition lg_authority where
  "lg_authority stage route actor request state \<longleftrightarrow>
    (let order = lg_order request in actor = legal_officer order \<and> legal_basis order \<noteq> 0 \<and>
      legal_asset order \<in> set (lg_scope_words request) \<and>
      [lg_stage_code stage,lg_route_code route,actor,legal_jurisdiction order,legal_basis order,
        legal_asset order,3,lg_epoch state] \<in> set (lg_grants state))"

definition lg_binding_scope where
  "lg_binding_scope request state \<longleftrightarrow>
    (let order = lg_order request; binding = legal_binding order in
      [legal_asset order,fst (legal_origin order),binding_destination binding] \<in> set (lg_enrollments state) \<and>
      (case legal_destination order of None \<Rightarrow> True | Some destination \<Rightarrow> destination = binding_recipient binding))"

fun lg_fresh_scope where
  "lg_fresh_scope Legal_Source_Emission state = (lg_current_issued state = None)"
| "lg_fresh_scope Legal_Receiving_Commit state = (\<not> lg_current_applied state)"

fun lg_native_issuance where
  "lg_native_issuance Legal_Source_Emission request state =
     (legal_issuance_epoch (lg_order request) = lg_epoch state \<and> lg_current_issued state = None)"
| "lg_native_issuance Legal_Receiving_Commit request state = (lg_current_issued state = Some (lg_exact_order request))"

definition lg_event_of where
  "lg_event_of request applied = \<lparr>lg_event_action = legal_action (lg_order request),
    lg_event_asset = legal_asset (lg_order request),lg_event_applied = applied,
    lg_event_parent = legal_predecessor (lg_order request),lg_event_deadline = legal_appeal_deadline (lg_order request)\<rparr>"

definition lg_emit_effect where
  "lg_emit_effect request state = state\<lparr>lg_current_issued := Some (lg_exact_order request),
     lg_events := (lg_events state)(legal_origin (lg_order request) := Some (lg_event_of request False))\<rparr>"

definition lg_receive_effect where
  "lg_receive_effect request state = state\<lparr>lg_current_applied := True,
     lg_events := (lg_events state)(legal_origin (lg_order request) := Some (lg_event_of request True)),
     lg_modes := (\<lambda>domain_asset. if snd domain_asset = legal_asset (lg_order request)
       then map_option (\<lambda>_. CONFISCATED) (lg_modes state domain_asset) else lg_modes state domain_asset)\<rparr>"

definition lg_fresh_step_with where
  "lg_fresh_step_with transition evidence stage route actor request state =
    (if legal_action (lg_order request) \<noteq> CONFISCATE \<or> \<not> lg_fresh_scope stage state
       then (state,LG_Outside_Fresh_Scope)
     else case evidence of LG_Unobserved \<Rightarrow> (state,LG_Evidence_Unobserved)
      | LG_Refuted \<Rightarrow> (state,LG_Refused Invalid_Legal_Authority)
      | LG_Verified \<Rightarrow>
        if \<not> lg_authority stage route actor request state then (state,LG_Refused Invalid_Legal_Authority)
        else if \<not> lg_binding_scope request state then (state,LG_Refused Invalid_Legal_Binding)
        else case transition state request of Legal_Refuse reason \<Rightarrow> (state,LG_Refused reason)
         | Legal_Admit \<Rightarrow> if \<not> lg_native_issuance stage request state then (state,LG_Refused Conflicting_Legal_Order)
           else case stage of Legal_Source_Emission \<Rightarrow> (lg_emit_effect request state,LG_Emitted)
            | Legal_Receiving_Commit \<Rightarrow> (lg_receive_effect request state,LG_Applied))"

text \<open>This diagnostic records the public predicate's issuance-first order
  on the same typed projections. It is not an unconditional equality claim for
  a complete legal_product_world. The actual public predicate remains unchanged.\<close>

definition lg_public_order_projection where
  "lg_public_order_projection stage route actor request state =
    (if \<not> lg_authority stage route actor request state then Legal_Refuse Invalid_Legal_Authority
     else if (case stage of Legal_Source_Emission \<Rightarrow>
          legal_issuance_epoch (lg_order request) \<noteq> lg_epoch state \<or>
          (lg_current_issued state \<noteq> None \<and> lg_current_issued state \<noteq> Some (lg_exact_order request))
        | Legal_Receiving_Commit \<Rightarrow> lg_current_issued state \<noteq> Some (lg_exact_order request))
       then Legal_Refuse Conflicting_Legal_Order else lg_transition state request)"

lemma lg_resolved_seizure_has_the_actual_applied_chain:
  assumes "lg_active_seizure state asset = Some (seizure_key,deadline)"
  obtains seizure_event freeze_key freeze_event where
    "lg_seizures state asset = Some seizure_key" "lg_events state seizure_key = Some seizure_event"
    "lg_event_applied seizure_event" "lg_event_action seizure_event = SEIZE" "lg_event_asset seizure_event = asset"
    "lg_event_deadline seizure_event = deadline" "lg_event_parent seizure_event = Some freeze_key"
    "lg_freezes state asset = Some freeze_key" "lg_events state freeze_key = Some freeze_event"
    "lg_event_applied freeze_event" "lg_event_action freeze_event = FREEZE" "lg_event_asset freeze_event = asset"
  using assms by (auto simp: lg_active_seizure_def lg_active_freeze_def lg_prior_event_def
      split: option.splits prod.splits if_splits)

lemma lg_admission_uses_the_recorded_deadline_and_current_pair:
  assumes "lg_transition state request = Legal_Admit"
  shows "lg_source_mode state request = Some SEIZED" "lg_receiver_mode state request = Some SEIZED"
    "\<exists>seizure_key deadline. lg_active_seizure state (legal_asset (lg_order request)) = Some (seizure_key,Some deadline) \<and>
      legal_predecessor (lg_order request) = Some seizure_key \<and>
      legal_appeal_deadline (lg_order request) = Some deadline \<and> deadline \<le> lg_clock state"
    "legal_destination (lg_order request) \<noteq> None"
  using assms by (auto simp: lg_transition_def native_confiscation_gate_def
      split: option.splits prod.splits if_splits)

theorem lg_existing_public_state_gate_is_reused_under_its_exact_contract:
  fixes request :: lg_request and state :: lg_state
  assumes action: "legal_action (lg_order request) = CONFISCATE"
    and source: "lg_source_mode state request = legal_current_state spec (fst (legal_origin (lg_order request))) (legal_asset (lg_order request))"
    and configured: "lg_source_mode state request \<noteq> None" "lg_receiver_mode state request = lg_source_mode state request"
    and time: "lg_clock state = legal_clock spec"
    and seizure: "(\<exists>seizure_key deadline. lg_active_seizure state (legal_asset (lg_order request)) = Some (seizure_key,deadline) \<and>
      legal_predecessor (lg_order request) = Some seizure_key) \<longleftrightarrow>
      exact_legal_predecessor spec (lg_order request) (active_seizure_event spec (legal_asset (lg_order request))) SEIZE"
    and appeal: "\<And>seizure_key deadline. lg_active_seizure state (legal_asset (lg_order request)) = Some (seizure_key,deadline) \<Longrightarrow>
      legal_predecessor (lg_order request) = Some seizure_key \<Longrightarrow> deadline = recorded_appeal_deadline spec (legal_asset (lg_order request))"
  shows "lg_transition state request = legal_state_gate spec (lg_order request)"
  unfolding lg_transition_def
  by (rule the_native_confiscation_gate_matches_the_exact_current_legal_state[OF action source configured time seizure appeal])

lemma lg_fresh_refusal_preserves_the_legal_effect_projection:
  assumes "lg_fresh_step_with transition evidence stage route actor request state = (after,LG_Refused reason)"
  shows "after = state"
  using assms by (auto simp: lg_fresh_step_with_def split: lg_evidence.splits legal_admission.splits legal_stage.splits if_splits)

lemma lg_source_emission_never_changes_the_mode_table:
  "lg_modes (fst (lg_fresh_step_with transition evidence Legal_Source_Emission route actor request state)) = lg_modes state"
  by (simp add: lg_fresh_step_with_def lg_emit_effect_def split: lg_evidence.splits legal_admission.splits)

lemma lg_fresh_steps_keep_the_money_projection:
  "lg_money (fst (lg_fresh_step_with transition evidence stage route actor request state)) = lg_money state"
  by (cases stage)
    (simp_all add: lg_fresh_step_with_def lg_emit_effect_def lg_receive_effect_def
      split: lg_evidence.splits legal_admission.splits)

lemma lg_receive_updates_only_existing_modes_for_the_selected_asset:
  assumes "lg_modes state (domain,legal_asset (lg_order request)) = Some old_mode"
  shows "lg_modes (lg_receive_effect request state) (domain,legal_asset (lg_order request)) = Some CONFISCATED"
  using assms by (simp add: lg_receive_effect_def)

lemma lg_other_asset_modes_are_unchanged:
  "asset \<noteq> legal_asset (lg_order request) \<Longrightarrow>
    lg_modes (lg_receive_effect request state) (domain,asset) = lg_modes state (domain,asset)"
  by (simp add: lg_receive_effect_def)

lemma lg_public_predicate_refuses_an_unissued_receive_before_its_state_gate:
  assumes verified: "order_verified Legal_Receiving_Commit entry actor order"
    and authority: "legal_officer order = actor" "legal_basis order \<noteq> 0" "legal_asset order \<in> legal_scope order"
      "legal_grant Legal_Receiving_Commit entry actor (legal_jurisdiction order) (legal_asset order) (legal_action order)
        (cut_authority_epoch (legal_current_cut spec))"
    and unissued: "issued_legal_orders spec (legal_origin order) = None"
  shows "legal_admission_at_cut legal_grant order_verified Legal_Receiving_Commit entry actor order spec =
     Legal_Refuse Conflicting_Legal_Order"
  using assms by (simp add: legal_admission_at_cut_def)

section \<open>Typed envelope construction\<close>

fun lg_option_word where
  "lg_option_word 0 value = Some None"
| "lg_option_word (Suc 0) value = Some (Some value)"
| "lg_option_word _ _ = None"

fun lg_option_key where
  "lg_option_key 0 domain event = Some None"
| "lg_option_key (Suc 0) domain event = Some (Some (domain,event))"
| "lg_option_key _ _ _ = None"

fun lg_parse_mode where
  "lg_parse_mode mode_tag =
    (if mode_tag = 0 then Some ACTIVE else if mode_tag = 1 then Some RESTRICTED
     else if mode_tag = 2 then Some FROZEN else if mode_tag = 3 then Some SEIZED
     else if mode_tag = 4 then Some CONFISCATED else None)"

fun lg_parse_action where
  "lg_parse_action action_tag =
    (if action_tag = 0 then Some FREEZE else if action_tag = 1 then Some RESTRICT
     else if action_tag = 2 then Some SEIZE else if action_tag = 3 then Some CONFISCATE
     else if action_tag = 4 then Some UNFREEZE else if action_tag = 5 then Some UNRESTRICT
     else if action_tag = 6 then Some RELEASE else None)"

fun lg_parse_request where
  "lg_parse_request [domain,event,asset,owner,receiver,recipient,amount,action_tag,officer,jurisdiction,basis,epoch,
      predecessor_flag,predecessor_domain,predecessor_event,deadline_flag,deadline,destination_flag,destination] scope =
    (if action_tag \<noteq> 3 \<or> \<not> sorted scope \<or> \<not> distinct scope then None else
      case (lg_option_key predecessor_flag predecessor_domain predecessor_event,lg_option_word deadline_flag deadline,
            lg_option_word destination_flag destination) of (Some predecessor,Some appeal,Some destination_value) \<Rightarrow>
        Some \<lparr>lg_order = \<lparr>legal_origin = (domain,event),legal_binding =
          \<lparr>binding_key = (domain,event),binding_asset = asset,binding_amount = amount,binding_destination = receiver,
            binding_recipient = recipient,binding_source_epoch = epoch,binding_operation = Regulatory_State_Effect CONFISCATE,binding_separator = 0\<rparr>,
          legal_asset = asset,legal_action = CONFISCATE,legal_officer = officer,legal_jurisdiction = jurisdiction,
          legal_basis = basis,legal_scope = set scope,legal_issuance_epoch = epoch,legal_predecessor = predecessor,
          legal_appeal_deadline = appeal,legal_destination = destination_value\<rparr>,
          lg_native_words = [domain,event,asset,owner,receiver,recipient,amount,action_tag,officer,jurisdiction,basis,epoch,
            predecessor_flag,predecessor_domain,predecessor_event,deadline_flag,deadline,destination_flag,destination],lg_scope_words = scope\<rparr>
       | _ \<Rightarrow> None)"
| "lg_parse_request _ _ = None"

fun lg_parse_mode_row where
  "lg_parse_mode_row [domain,asset,mode_tag] = map_option (\<lambda>mode. ((domain,asset),mode)) (lg_parse_mode mode_tag)"
| "lg_parse_mode_row _ = None"

fun lg_parse_event where
  "lg_parse_event [domain,event,action_tag,asset,applied,predecessor_flag,predecessor_domain,predecessor_event,deadline_flag,deadline] =
    (if applied > 1 then None else case (lg_parse_action action_tag,
      lg_option_key predecessor_flag predecessor_domain predecessor_event,lg_option_word deadline_flag deadline) of
      (Some action,Some predecessor,Some appeal) \<Rightarrow> Some ((domain,event),
        \<lparr>lg_event_action = action,lg_event_asset = asset,lg_event_applied = (applied = 1),
          lg_event_parent = predecessor,lg_event_deadline = appeal\<rparr>) | _ \<Rightarrow> None)"
| "lg_parse_event _ = None"

fun lg_parse_index where
  "lg_parse_index [asset,domain,event] = Some (asset,(domain,event))"
| "lg_parse_index _ = None"

fun lg_collect where
  "lg_collect [] = Some []"
| "lg_collect (None # rest_values) = None"
| "lg_collect (Some value # rest_values) = map_option ((#) value) (lg_collect rest_values)"

fun lg_parse_route where
  "lg_parse_route route_tag = (if route_tag = 0 then Some Regulatory_Normal else if route_tag = 1 then Some Regulatory_Administrative
     else if route_tag = 2 then Some Regulatory_Adapter else if route_tag = 3 then Some Regulatory_Force_Inclusion else None)"

fun lg_parse_evidence where
  "lg_parse_evidence evidence_tag = (if evidence_tag = 0 then Some LG_Refuted else if evidence_tag = 1 then Some LG_Verified
    else if evidence_tag = 2 then Some LG_Unobserved else None)"

definition lg_make_state where
  "lg_make_state epoch clock money modes events freezes seizures grants enrollments =
    \<lparr>lg_epoch = epoch,lg_clock = clock,lg_money = money,lg_modes = map_of modes,lg_events = map_of events,
     lg_freezes = map_of freezes,lg_seizures = map_of seizures,lg_grants = grants,lg_enrollments = enrollments,
     lg_current_issued = None,lg_current_applied = False\<rparr>"

section \<open>Small original-input witnesses and the ordering boundary\<close>

definition lg_fixture_words where
  "lg_fixture_words deadline = [0,42,17,7,2,3,0,3,7,1,1,9,1,0,41,1,deadline,1,3]"

definition lg_fixture_request where
  "lg_fixture_request deadline = the (lg_parse_request (lg_fixture_words deadline) [17])"

definition lg_fixture_state where
  "lg_fixture_state mode now recorded = lg_make_state 9 now [10,0] [((0,17),mode),((2,17),mode)]
     ((if mode = FROZEN \<or> mode = SEIZED then
        [((0,40),\<lparr>lg_event_action=FREEZE,lg_event_asset=17,lg_event_applied=True,lg_event_parent=None,lg_event_deadline=None\<rparr>)] else []) @
      (if mode = SEIZED then
        [((0,41),\<lparr>lg_event_action=SEIZE,lg_event_asset=17,lg_event_applied=True,lg_event_parent=Some (0,40),lg_event_deadline=Some recorded\<rparr>)] else []) @
      (if mode = RESTRICTED then
        [((0,44),\<lparr>lg_event_action=RESTRICT,lg_event_asset=17,lg_event_applied=True,lg_event_parent=None,lg_event_deadline=None\<rparr>)] else []))
     (if mode = FROZEN \<or> mode = SEIZED then [(17,(0,40))] else []) (if mode = SEIZED then [(17,(0,41))] else [])
     [[0,0,7,1,1,17,3,9],[1,0,7,1,1,17,3,9]] [[17,0,2]]"

lemma lg_original_early_and_shortened_deadlines_are_distinct:
  "lg_transition (lg_fixture_state SEIZED 4 5) (lg_fixture_request 5) = Legal_Refuse Appeal_Still_Open"
  "lg_transition (lg_fixture_state SEIZED 4 5) (lg_fixture_request 4) = Legal_Refuse Appeal_Deadline_Mismatch"
  by (code_simp)+

lemma lg_recorded_deadline_single_removal:
  "lg_transition_without_recorded_deadline (lg_fixture_state SEIZED 4 5) (lg_fixture_request 4) = Legal_Admit"
  "lg_transition_without_elapsed_time (lg_fixture_state SEIZED 4 5) (lg_fixture_request 4) = Legal_Refuse Appeal_Deadline_Mismatch"
  by (code_simp)+

lemma lg_elapsed_time_single_removal:
  "lg_transition_without_elapsed_time (lg_fixture_state SEIZED 4 5) (lg_fixture_request 5) = Legal_Admit"
  "lg_transition_without_recorded_deadline (lg_fixture_state SEIZED 4 5) (lg_fixture_request 5) = Legal_Refuse Appeal_Still_Open"
  by (code_simp)+

lemma lg_same_pair_and_elapsed_boundary_admit:
  "lg_transition (lg_fixture_state SEIZED 5 5) (lg_fixture_request 5) = Legal_Admit"
  "lg_transition (lg_fixture_state ACTIVE 5 5) (lg_fixture_request 5) = Legal_Refuse Missing_Prior_Seizure"
  "lg_transition (lg_fixture_state FROZEN 5 5) (lg_fixture_request 5) = Legal_Refuse Missing_Prior_Seizure"
  "lg_transition (lg_fixture_state RESTRICTED 5 5) (lg_fixture_request 5) = Legal_Refuse Missing_Prior_Seizure"
  by (code_simp)+

lemma lg_native_early_receive_and_public_order_projection_differ_when_unissued:
  "snd (lg_fresh_step_with lg_transition LG_Verified Legal_Receiving_Commit Regulatory_Normal 7
      (lg_fixture_request 5) (lg_fixture_state SEIZED 4 5)) = LG_Refused Appeal_Still_Open"
  "lg_public_order_projection Legal_Receiving_Commit Regulatory_Normal 7
      (lg_fixture_request 5) (lg_fixture_state SEIZED 4 5) = Legal_Refuse Conflicting_Legal_Order"
  by (code_simp)+

lemma lg_source_emits_without_applying_and_receiver_applies_the_pair:
  "let request = lg_fixture_request 5; state = lg_fixture_state SEIZED 5 5;
       emitted = lg_fresh_step_with lg_transition LG_Verified Legal_Source_Emission Regulatory_Normal 7 request state;
       received = lg_fresh_step_with lg_transition LG_Verified Legal_Receiving_Commit Regulatory_Normal 7 request (fst emitted)
   in snd emitted = LG_Emitted \<and> lg_source_mode (fst emitted) request = Some SEIZED \<and>
      lg_receiver_mode (fst emitted) request = Some SEIZED \<and> snd received = LG_Applied \<and>
      lg_source_mode (fst received) request = Some CONFISCATED \<and>
      lg_receiver_mode (fst received) request = Some CONFISCATED"
  by code_simp

section \<open>Executable projection, with public ordering recorded separately\<close>

fun lg_refusal_code where
  "lg_refusal_code Invalid_Legal_Authority = 0"
| "lg_refusal_code Invalid_Legal_State = 1"
| "lg_refusal_code Missing_Prior_Freeze = 2"
| "lg_refusal_code Missing_Prior_Seizure = 3"
| "lg_refusal_code Appeal_Deadline_Mismatch = 4"
| "lg_refusal_code Appeal_Still_Open = 5"
| "lg_refusal_code Missing_Confiscation_Destination = 6"
| "lg_refusal_code Conflicting_Legal_Order = 7"
| "lg_refusal_code Invalid_Legal_Binding = 8"

fun lg_reply_words where
  "lg_reply_words LG_Evidence_Unobserved = [0]"
| "lg_reply_words LG_Outside_Fresh_Scope = [1]"
| "lg_reply_words LG_Emitted = [2]"
| "lg_reply_words LG_Applied = [3]"
| "lg_reply_words (LG_Refused reason) = [4,lg_refusal_code reason]"

fun lg_admission_words where
  "lg_admission_words Legal_Admit = [0]"
| "lg_admission_words (Legal_Refuse reason) = [1,lg_refusal_code reason]"

fun lg_mode_word where
  "lg_mode_word None = 5"
| "lg_mode_word (Some ACTIVE) = 0"
| "lg_mode_word (Some RESTRICTED) = 1"
| "lg_mode_word (Some FROZEN) = 2"
| "lg_mode_word (Some SEIZED) = 3"
| "lg_mode_word (Some CONFISCATED) = 4"

definition lg_view where
  "lg_view request state = [lg_mode_word (lg_source_mode state request),lg_mode_word (lg_receiver_mode state request),
      (if lg_current_issued state = None then 0 else if lg_current_issued state = Some (lg_exact_order request) then 1 else 2),
      (if lg_current_applied state then 1 else 0),lg_epoch state,lg_clock state] @ lg_money state"

definition lg_pair_observe where
  "lg_pair_observe transition evidence route actor request state =
    (let first = lg_fresh_step_with transition evidence Legal_Source_Emission route actor request state;
         second = lg_fresh_step_with transition evidence Legal_Receiving_Commit route actor request (fst first)
     in [[lg_reply_words (snd first),lg_admission_words (lg_public_order_projection Legal_Source_Emission route actor request state),
            lg_view request state,lg_view request (fst first)],
         [lg_reply_words (snd second),lg_admission_words (lg_public_order_projection Legal_Receiving_Commit route actor request (fst first)),
            lg_view request (fst first),lg_view request (fst second)]])"

definition lg_run_nat_with where
  "lg_run_nat_with transition header mode_rows event_rows freeze_rows seizure_rows grants enrollments request_words scope_words =
    (case header of epoch # clock # route_tag # actor # evidence_tag # money \<Rightarrow>
      (case (lg_parse_route route_tag,lg_parse_evidence evidence_tag,lg_parse_request request_words scope_words,
         lg_collect (map lg_parse_mode_row mode_rows),lg_collect (map lg_parse_event event_rows),
         lg_collect (map lg_parse_index freeze_rows),lg_collect (map lg_parse_index seizure_rows)) of
        (Some route,Some evidence,Some request,Some modes,Some events,Some freezes,Some seizures) \<Rightarrow>
          if \<not> distinct (map fst modes) \<or> \<not> distinct (map fst events) \<or>
             \<not> distinct (map fst freezes) \<or> \<not> distinct (map fst seizures) \<or>
             map_of events (legal_origin (lg_order request)) \<noteq> None then None else
          Some (lg_pair_observe transition evidence route actor request
            (lg_make_state epoch clock money modes events freezes seizures grants enrollments))
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition lg_u64_words :: "integer list \<Rightarrow> bool" where
  "lg_u64_words values = list_all (\<lambda>value. 0 \<le> value \<and> value \<le> 18446744073709551615) values"

definition lg_integer_call where
  "lg_integer_call transition header modes events freezes seizures grants enrollments request scope =
    (if \<not> list_all lg_u64_words ([header,request,scope] @ modes @ events @ freezes @ seizures @ grants @ enrollments)
       then None else let ns = map nat_of_integer in
       map_option (map (map (map integer_of_nat))) (lg_run_nat_with transition (ns header) (map ns modes) (map ns events)
         (map ns freezes) (map ns seizures) (map ns grants) (map ns enrollments) (ns request) (ns scope)))"

definition lg_run_flat where "lg_run_flat = lg_integer_call lg_transition"
definition lg_run_without_recorded_deadline_flat where "lg_run_without_recorded_deadline_flat = lg_integer_call lg_transition_without_recorded_deadline"
definition lg_run_without_elapsed_time_flat where "lg_run_without_elapsed_time_flat = lg_integer_call lg_transition_without_elapsed_time"
definition lg_export_identity :: "integer list" where "lg_export_identity = [1,8,4,2,19,10,8]"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms lg_resolved_seizure_has_the_actual_applied_chain
      lg_admission_uses_the_recorded_deadline_and_current_pair lg_existing_public_state_gate_is_reused_under_its_exact_contract
      lg_fresh_refusal_preserves_the_legal_effect_projection lg_source_emission_never_changes_the_mode_table
      lg_fresh_steps_keep_the_money_projection lg_receive_updates_only_existing_modes_for_the_selected_asset
      lg_other_asset_modes_are_unchanged lg_public_predicate_refuses_an_unissued_receive_before_its_state_gate
      lg_original_early_and_shortened_deadlines_are_distinct lg_recorded_deadline_single_removal
      lg_elapsed_time_single_removal lg_same_pair_and_elapsed_boundary_admit
      lg_native_early_receive_and_public_order_projection_differ_when_unissued
      lg_source_emits_without_applying_and_receiver_applies_the_pair})
  then () else error "Unexpected oracle in typed native confiscation G0"
\<close>

export_code lg_run_flat lg_run_without_recorded_deadline_flat lg_run_without_elapsed_time_flat lg_export_identity
  in SML module_name OIP_Regulatory_Legal_G0 file_prefix "oip_regulatory_legal_g0"

end

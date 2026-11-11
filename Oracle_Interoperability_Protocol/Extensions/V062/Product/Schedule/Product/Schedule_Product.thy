theory Schedule_Product
  imports "OIP_Typed_Scheduler.Typed_Scheduler"
    "OIP_Reference_Execution.Reference_Read_Code"
begin

record ss_binding =
  ss_origin :: source_key
  ss_asset :: nat
  ss_owner :: nat
  ss_destination :: nat
  ss_recipient :: nat
  ss_amount :: nat

datatype ss_command = SS_Reserve nat | SS_Dispatch nat | SS_Debit nat
  | SS_Record nat | SS_Credit nat | SS_Reconcile nat nat | SS_Publish
  | SS_Write nat nat | SS_Cancel nat

record ss_request =
  ss_actor :: nat
  ss_namespace :: nat
  ss_sequence :: nat
  ss_session :: nat
  ss_auth_epoch :: nat
  ss_original_epoch :: nat
  ss_expected :: product_cut
  ss_binding :: ss_binding
  ss_command :: ss_command
  ss_request_versions :: "(nat \<times> nat) list"
  ss_owner_consent :: bool
  ss_signature :: bool

record ss_reservation =
  ss_reserved_binding :: ss_binding
  ss_generation :: nat
  ss_holder :: nat
  ss_deadline :: nat
  ss_phase :: nat
  ss_terminal :: "nat option"

record ss_snapshot =
  ss_values :: "(nat \<times> nat) list"
  ss_versions :: "(nat \<times> nat) list"
  ss_balances :: "((nat \<times> nat \<times> nat) \<times> nat) list"

datatype ss_reply = SS_Executed nat "(nat \<times> nat) option"
  | SS_Raw_Value nat | SS_Current_Value "(product_cut \<times> nat) option"
  | SS_Historical_Value "(nat \<times> nat) option" | SS_Changed bool
  | SS_Endpoint_Rejected | SS_Unsupported

record ss_data =
  ss_epoch :: nat
  ss_revision :: nat
  ss_clock :: nat
  ss_provider :: nat
  ss_connected :: bool
  ss_current_allowed :: bool
  ss_current :: ss_snapshot
  ss_prefixes :: "ss_snapshot list"
  ss_reservations :: "(source_key \<times> ss_reservation) list"
  ss_active :: "(nat \<times> source_key) list"
  ss_evidence :: "(nat \<times> ss_binding) list"
  ss_decisions :: "(source_key \<times> sp_publication) list"
  ss_calls :: "((nat \<times> nat) \<times> (ss_request \<times> ss_reply)) list"
  ss_funding :: "((source_key \<times> (nat \<times> nat \<times> nat)) \<times> nat) list"

datatype ss_query = SS_Application nat | SS_Account nat nat nat
datatype ss_other = SS_Execute ss_request
  | SS_Raw nat nat nat nat ss_query
  | SS_Current nat nat nat nat ss_query product_cut
  | SS_Historical nat nat nat nat ss_query nat
  | SS_Install nat nat

definition ss_put where
  "ss_put key value rows = (key,value) # filter (\<lambda>(old,entry). old \<noteq> key) rows"

definition ss_get where
  "ss_get rows key = (case map_of rows key of None \<Rightarrow> 0 | Some value \<Rightarrow> value)"

definition ss_source_account where
  "ss_source_account binding = (fst (ss_origin binding),ss_asset binding,ss_owner binding)"

definition ss_destination_account where
  "ss_destination_account binding = (ss_destination binding,ss_asset binding,ss_recipient binding)"

definition ss_cut where
  "ss_cut data = \<lparr>cut_authority_epoch = ss_epoch data,cut_revision = ss_revision data\<rparr>"

definition ss_auth where
  "ss_auth actor session epoch data \<longleftrightarrow>
    ss_connected data \<and> actor = 7 \<and> session \<in> {1,2} \<and> epoch = ss_epoch data"

definition ss_can_maintain where
  "ss_can_maintain token data \<longleftrightarrow> ss_connected data \<and> token = 99"

definition ss_make_publication where
  "ss_make_publication binding original_epoch commit_epoch position =
    \<lparr>sp_publication_model = \<lparr>publication_origin = ss_origin binding,
      publication_decision = \<lparr>origin_binding = \<lparr>binding_key = ss_origin binding,
        binding_asset = ss_asset binding,binding_amount = ss_amount binding,
        binding_destination = ss_destination binding,binding_recipient = ss_recipient binding,
        binding_source_epoch = original_epoch,binding_operation = Destination_Credit,binding_separator = 0\<rparr>,
        origin_kind = Confirmed_Decision,origin_epoch = original_epoch,origin_commit_position = position\<rparr>\<rparr>,
      sp_publication_commit_epoch = commit_epoch,sp_publication_owner = ss_owner binding\<rparr>"

definition ss_exact_terminal where
  "ss_exact_terminal data slot reference \<longleftrightarrow>
    ss_terminal slot \<noteq> None \<and> map_of (ss_evidence data) reference = Some (ss_reserved_binding slot)"

definition ss_bound where
  "ss_bound request slot generation data \<longleftrightarrow>
    ss_reserved_binding slot = ss_binding request \<and> ss_holder slot = ss_actor request \<and>
    ss_generation slot = generation \<and>
    map_of (ss_active data) (ss_asset (ss_binding request)) = Some (ss_origin (ss_binding request))"

definition ss_versions_fit where
  "ss_versions_fit request data \<longleftrightarrow>
    ss_get (ss_request_versions request) (ss_asset (ss_binding request)) =
      ss_get (ss_versions (ss_current data)) (ss_asset (ss_binding request))"

definition ss_store_slot where
  "ss_store_slot slot data = data\<lparr>ss_reservations :=
    ss_put (ss_origin (ss_reserved_binding slot)) slot (ss_reservations data)\<rparr>"

definition ss_finish_slot where
  "ss_finish_slot phase slot data =
    (ss_store_slot (slot\<lparr>ss_phase := phase\<rparr>) data)\<lparr>ss_active :=
      filter (\<lambda>(asset,key). asset \<noteq> ss_asset (ss_reserved_binding slot)) (ss_active data)\<rparr>"

definition ss_body where
  "ss_body request data =
    (let binding = ss_binding request; origin = ss_origin binding; asset = ss_asset binding;
         snapshot = ss_current data in
     case ss_command request of SS_Reserve duration \<Rightarrow>
       if duration = 0 \<or> ss_clock data + duration \<ge> 2^64 \<or>
          map_of (ss_reservations data) origin \<noteq> None \<or> \<not> ss_versions_fit request data
       then (data,1,False)
       else if map_of (ss_active data) asset \<noteq> None then (data,2,False)
       else let slot = \<lparr>ss_reserved_binding = binding,ss_generation = 0,ss_holder = ss_actor request,
              ss_deadline = ss_clock data + duration,ss_phase = 1,ss_terminal = None\<rparr>
         in ((ss_store_slot slot data)\<lparr>ss_active := ss_put asset origin (ss_active data)\<rparr>,10,True)
     | command \<Rightarrow> case map_of (ss_reservations data) origin of None \<Rightarrow> (data,1,False)
       | Some slot \<Rightarrow> if ss_reserved_binding slot \<noteq> binding then (data,1,False) else
         (case command of
           SS_Dispatch generation \<Rightarrow>
             if ss_bound request slot generation data \<and> ss_versions_fit request data \<and>
                ss_phase slot = 1 \<and> ss_clock data < ss_deadline slot \<and> ss_amount binding > 0 \<and>
                ss_amount binding \<le> ss_get (ss_balances snapshot) (ss_source_account binding)
             then (ss_store_slot (slot\<lparr>ss_phase := 2\<rparr>) data,11,True) else (data,1,False)
         | SS_Debit generation \<Rightarrow>
             if ss_bound request slot generation data \<and> ss_versions_fit request data \<and>
                ss_phase slot = 2 \<and> ss_original_epoch request = ss_epoch data \<and>
                ss_clock data < ss_deadline slot \<and> ss_amount binding > 0 \<and>
                ss_amount binding \<le> ss_get (ss_balances snapshot) (ss_source_account binding)
             then let next = snapshot\<lparr>ss_balances := ss_put (ss_source_account binding)
                  (ss_get (ss_balances snapshot) (ss_source_account binding) - ss_amount binding) (ss_balances snapshot)\<rparr>
               in ((ss_store_slot (slot\<lparr>ss_phase := 3\<rparr>) data)\<lparr>ss_current := next\<rparr>,12,True)
             else (data,1,False)
         | SS_Record reference \<Rightarrow>
             if ss_phase slot = 3 \<and> ss_terminal slot = None \<and> map_of (ss_evidence data) reference = None
             then ((ss_store_slot (slot\<lparr>ss_terminal := Some reference\<rparr>) data)\<lparr>
                 ss_evidence := ss_put reference binding (ss_evidence data),
                 ss_decisions := ss_put origin (ss_make_publication binding (ss_original_epoch request) (ss_epoch data) (ss_revision data)) (ss_decisions data)\<rparr>,16,True)
             else (data,1,False)
         | SS_Credit reference \<Rightarrow>
             if ss_bound request slot 0 data \<and> ss_phase slot = 3 \<and> ss_exact_terminal data slot reference \<and>
                ss_get (ss_balances snapshot) (ss_destination_account binding) + ss_amount binding < 2^64
             then let next = snapshot\<lparr>ss_balances := ss_put (ss_destination_account binding)
                  (ss_get (ss_balances snapshot) (ss_destination_account binding) + ss_amount binding) (ss_balances snapshot)\<rparr>
               in ((ss_store_slot (slot\<lparr>ss_phase := 4\<rparr>) data)\<lparr>ss_current := next,
                  ss_funding := ss_put (origin,ss_destination_account binding) (ss_amount binding) (ss_funding data)\<rparr>,17,True)
             else (data,1,False)
         | SS_Reconcile generation reference \<Rightarrow>
             if ss_owner_consent request \<and> ss_bound request slot generation data \<and> ss_versions_fit request data \<and>
                ss_phase slot = 4 \<and> ss_clock data < ss_deadline slot \<and> ss_exact_terminal data slot reference
             then (ss_finish_slot 5 slot data,18,True) else (data,1,False)
         | SS_Publish \<Rightarrow> if ss_phase slot \<in> {4,5,6} \<and> map_of (ss_decisions data) origin \<noteq> None
             then (data,22,True) else (data,1,False)
         | SS_Write generation value \<Rightarrow>
             if ss_bound request slot generation data \<and> ss_versions_fit request data \<and>
                ss_phase slot = 1 \<and> ss_clock data < ss_deadline slot \<and>
                ss_actor request = 7 \<and> asset = 17 \<and> value = 9 \<and>
                Suc (ss_get (ss_versions snapshot) asset) < 2^64
             then (data\<lparr>ss_current := snapshot\<lparr>ss_values := ss_put asset value (ss_values snapshot),
                  ss_versions := ss_put asset (Suc (ss_get (ss_versions snapshot) asset)) (ss_versions snapshot)\<rparr>\<rparr>,20,True)
             else (data,1,False)
         | SS_Cancel generation \<Rightarrow>
             if ss_owner_consent request \<and> ss_bound request slot generation data \<and> ss_versions_fit request data \<and>
                ss_phase slot = 1 \<and> ss_clock data < ss_deadline slot
             then (ss_finish_slot 7 slot data,13,True) else (data,1,False)
         | SS_Reserve duration \<Rightarrow> (data,1,False)))"

definition ss_record_result where
  "ss_record_result request reply data = data\<lparr>ss_calls := ss_put (ss_namespace request,ss_sequence request)
    (request,reply) (ss_calls data)\<rparr>"

definition ss_execute_primary where
  "ss_execute_primary request state =
    (let data = sp_data state in
     if \<not> ss_auth (ss_actor request) (ss_session request) (ss_auth_epoch request) data \<or>
        ss_namespace request \<noteq> ss_actor request \<or> \<not> ss_signature request \<or>
        ss_asset (ss_binding request) \<notin> set (map fst (ss_values (ss_current data)))
     then (state,SS_Endpoint_Rejected)
     else case map_of (ss_calls data) (ss_namespace request,ss_sequence request) of
       Some (prior,reply) \<Rightarrow> if prior = request then (state,reply) else (state,SS_Unsupported)
     | None \<Rightarrow>
       if ss_expected request \<noteq> ss_cut data then
         (state\<lparr>sp_data := ss_record_result request (SS_Executed 2 None) data\<rparr>,SS_Executed 2 None)
       else if Suc (ss_revision data) \<ge> 2^64 then (state,SS_Unsupported)
       else let (effect,code,committed) = ss_body request data;
                reply = SS_Executed code (if committed then Some (ss_epoch data,ss_revision data) else None);
                next = (if committed then effect\<lparr>ss_revision := Suc (ss_revision data),
                    ss_prefixes := native_resize_read_prefixes (Suc (ss_revision data)) (ss_current effect) (ss_prefixes data)\<rparr>
                    else effect);
                pubs = (if committed \<and> ss_command request = SS_Publish then
                    (case map_of (ss_decisions data) (ss_origin (ss_binding request)) of None \<Rightarrow> sp_publications state
                     | Some pub \<Rightarrow> ss_put (ss_origin (ss_binding request)) pub (sp_publications state))
                    else sp_publications state)
            in (state\<lparr>sp_data := ss_record_result request reply next,sp_publications := pubs\<rparr>,reply))"

fun ss_query_value where
  "ss_query_value (SS_Application asset) snapshot = ss_get (ss_values snapshot) asset"
| "ss_query_value (SS_Account domain asset holder) snapshot = ss_get (ss_balances snapshot) (domain,asset,holder)"

definition ss_read_allowed where
  "ss_read_allowed actor session epoch target query data \<longleftrightarrow>
    ss_auth actor session epoch data \<and> target \<in> {0,2} \<and>
    (case query of SS_Application asset \<Rightarrow> asset \<in> set (map fst (ss_values (ss_current data)))
     | SS_Account domain asset holder \<Rightarrow> target = domain \<and> asset \<in> set (map fst (ss_values (ss_current data))))"

fun ss_classify_other where
  "ss_classify_other (SS_Raw actor session epoch target query) data = SP_Observation_Class None None"
| "ss_classify_other (SS_Current actor session epoch target query expected) data = SP_Observation_Class None None"
| "ss_classify_other (SS_Historical actor session epoch target query position) data = SP_Observation_Class None None"
| "ss_classify_other action data = SP_Serial_Class"

definition ss_other_step where
  "ss_other_step action state =
    (let data = sp_data state in case action of SS_Execute request \<Rightarrow> ss_execute_primary request state
     | SS_Raw actor session epoch target query \<Rightarrow>
         if ss_read_allowed actor session epoch target query data then (state,SS_Raw_Value (ss_query_value query (ss_current data)))
         else (state,SS_Endpoint_Rejected)
     | SS_Current actor session epoch target query expected \<Rightarrow>
         if ss_read_allowed actor session epoch target query data \<and> ss_current_allowed data
         then (state,SS_Current_Value (native_current_read_value True (ss_query_value query) expected
           (ss_epoch data) (ss_revision data) (ss_prefixes data))) else (state,SS_Endpoint_Rejected)
     | SS_Historical actor session epoch target query position \<Rightarrow>
         if ss_read_allowed actor session epoch target query data
         then (state,SS_Historical_Value (native_history_read_value True (ss_query_value query) position (ss_prefixes data)))
         else (state,SS_Endpoint_Rejected)
     | SS_Install token epoch \<Rightarrow>
         if ss_can_maintain token data \<and> ss_epoch data < epoch \<and> ss_revision data + 2 < 2^64
         then (state\<lparr>sp_data := data\<lparr>ss_epoch := epoch,ss_revision := ss_revision data + 2,
              ss_prefixes := native_resize_read_prefixes (ss_revision data + 2) (ss_current data) (ss_prefixes data)\<rparr>\<rparr>,SS_Changed True)
         else (state,SS_Changed False))"

definition ss_initial where
  "ss_initial =
    (let snapshot = \<lparr>ss_values = [(17,0),(22,0)],ss_versions = [(17,0),(22,0)],
          ss_balances = [((0,17,7),10),((0,22,7),10)]\<rparr>;
         data = \<lparr>ss_epoch = 9,ss_revision = 0,ss_clock = 0,ss_provider = 1,ss_connected = True,
          ss_current_allowed = True,ss_current = snapshot,ss_prefixes = [snapshot],ss_reservations = [],
          ss_active = [],ss_evidence = [],ss_decisions = [],ss_calls = [],ss_funding = []\<rparr>
     in \<lparr>sp_data = data,sp_publications = [],sp_jobs = (\<lambda>_. None),sp_known_keys = [],sp_target = 99\<rparr>)"

definition ss_make_request where
  "ss_make_request binding sequence command state =
    \<lparr>ss_actor = 7,ss_namespace = 7,ss_sequence = sequence,ss_session = 2,ss_auth_epoch = ss_epoch (sp_data state),ss_original_epoch = 9,
      ss_expected = ss_cut (sp_data state),ss_binding = binding,ss_command = command,
      ss_request_versions = (case command of SS_Cancel generation \<Rightarrow>
        if snd (ss_origin binding) = 18 then [(ss_asset binding,1)] else [] | _ \<Rightarrow> []),
      ss_owner_consent = True,ss_signature = True\<rparr>"

fun ss_fund_commands where
  "ss_fund_commands [] binding sequence state = Some state"
| "ss_fund_commands (command # rest) binding sequence state =
    (let result = ss_execute_primary (ss_make_request binding sequence command state) state
     in case snd result of SS_Executed code (Some commit) \<Rightarrow>
         ss_fund_commands rest binding (Suc sequence) (fst result) | _ \<Rightarrow> None)"

definition ss_fund where
  "ss_fund binding first publish state = ss_fund_commands
    ([SS_Reserve 20,SS_Dispatch 0,SS_Debit 0,SS_Record first,SS_Credit first,SS_Reconcile 0 first] @
     (if publish then [SS_Publish] else [])) binding first state"

lemma ss_nonserial_observations_do_not_write_queue_or_current_data:
  assumes "ss_classify_other action (sp_data state) \<noteq> SP_Serial_Class"
  shows "fst (ss_other_step action state) = state"
  using assms by (cases action) (auto simp: ss_other_step_def Let_def split: if_splits)

lemma ss_current_permission_is_checked_even_for_historical_data:
  assumes "epoch \<noteq> ss_epoch (sp_data state)"
  shows "ss_other_step (SS_Historical actor session epoch target query position) state = (state,SS_Endpoint_Rejected)"
  using assms by (simp add: ss_other_step_def ss_read_allowed_def ss_auth_def Let_def)

lemma ss_foreign_namespace_cannot_be_turned_into_a_completed_retry:
  assumes "ss_namespace request \<noteq> ss_actor request"
  shows "ss_execute_primary request state = (state,SS_Endpoint_Rejected)"
  using assms by (simp add: ss_execute_primary_def Let_def)

text \<open>
  Closed fixture operations compute effects from input requests and current
  data. The two registered assets, empty initial queues, caller/session binding,
  fixed write grant (7,17,9), trusted signatures/evidence and connected native
  storage boundary are typed seed premises, not signed-wrapper evidence.
  Publication commit comes from the modeled RecordTerminal operation, never
  from a caller slot or a case's commit-list selector. Unknown completed-call
  conflict shapes are explicit Unsupported, not guessed protocol outcomes.
  All thirteen original cases remain required; cache provider and signed
  publication guards have separately named model/source obligations.
\<close>

end

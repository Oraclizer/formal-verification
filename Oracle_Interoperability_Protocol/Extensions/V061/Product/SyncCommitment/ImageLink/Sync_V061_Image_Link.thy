theory Sync_V061_Image_Link
  imports "OIP_Sync_V061_Position_Selection.Sync_V061_Selection"
begin

type_synonym sync_image_rows = "(client_call_id \<times> wire_bytes \<times> sync_outcome) list"
type_synonym sync_image_entries = "(sync_stream \<times> sync_entry) list"

text \<open>The fields below are projections of one already decoded native image. They
  contain neither the native record address nor an assumed successful Sync transition.
  The global journal is observed after its common order and position checks.\<close>

record sync_image_view =
  sync_image_deployment :: nat
  sync_image_cut :: product_cut
  sync_image_endpoints :: "nat list"
  sync_image_assets :: "product_asset list"
  sync_image_calls :: sync_image_rows
  sync_image_ordinary_ids :: "client_call_id list"
  sync_image_regulatory_ids :: "client_call_id list"
  sync_image_bindings :: "(authenticated_message_id \<times> wire_bytes) list"
  sync_image_journal :: "(nat \<times> (client_call_id \<times> nat)) list"
  sync_image_history :: "sync_image_entries list"
  sync_image_streams :: sync_image_entries
  sync_image_events :: "source_key list"

definition sync_image_typed_shape where
  "sync_image_typed_shape img_view \<longleftrightarrow>
    distinct (map fst (sync_image_calls img_view)) \<and> distinct (map fst (sync_image_bindings img_view)) \<and>
    sorted_wrt (<) (map fst (sync_image_journal img_view)) \<and>
    list_all (\<lambda>(position,_). position < cut_revision (sync_image_cut img_view)) (sync_image_journal img_view) \<and>
    distinct (map fst (sync_image_streams img_view)) \<and> distinct (sync_image_events img_view) \<and>
    list_all (\<lambda>projection. distinct (map fst projection)) (sync_image_history img_view)"

definition sync_image_commit_ok where
  "sync_image_commit_ok img_view call_id core request outcome \<longleftrightarrow>
    (case outcome of Sync_Uncommitted _ \<Rightarrow> True | Sync_Committed position \<Rightarrow>
      cut_revision (sync_signed_cut request) = position \<and> position < cut_revision (sync_image_cut img_view) \<and>
      map_of (sync_image_journal img_view) position = Some (call_id,wire_target_domain core))"

definition sync_image_check_row where
  "sync_image_check_row img_view row =
    (case row of (call_id,raw,outcome) \<Rightarrow>
      Option.bind (sync_decode_core raw) (\<lambda>core.
       Option.bind (sync_read_operands core) (\<lambda>request.
        if sync_call request = call_id \<and> wire_deployment core = sync_image_deployment img_view \<and>
           wire_target_domain core \<in> set (sync_image_endpoints img_view) \<and> fst (sync_key request) \<in> set (sync_image_assets img_view) \<and>
           cut_authority_epoch (sync_signed_cut request) \<le> cut_authority_epoch (sync_image_cut img_view) \<and>
           map_of (sync_image_bindings img_view) (code_transport_key core) = Some raw \<and>
           call_id \<notin> set (sync_image_ordinary_ids img_view) \<and> call_id \<notin> set (sync_image_regulatory_ids img_view) \<and>
           sync_image_commit_ok img_view call_id core request outcome
        then Some (core,request) else None)))"

fun sync_image_successes where
  "sync_image_successes img_view [] = Some []"
| "sync_image_successes img_view (row # remaining) =
    Option.bind (sync_image_check_row img_view row) (\<lambda>(_,request).
      map_option (\<lambda>checked. case snd (snd row) of Sync_Uncommitted _ \<Rightarrow> checked
          | Sync_Committed position \<Rightarrow> (position,request) # checked)
        (sync_image_successes img_view remaining))"

definition sync_image_replay_mode where
  "sync_image_replay_mode request prior \<longleftrightarrow>
    (case (sync_mode request,prior) of
       (Sync_Initial,None) \<Rightarrow> sync_claimed_prior request = None
     | (Sync_Incremental,Some current) \<Rightarrow> sync_claimed_prior request = Some (sync_commitment current)
     | (Sync_Full,Some _) \<Rightarrow> sync_claimed_prior request = None
     | _ \<Rightarrow> False)"

definition sync_image_history_at where
  "sync_image_history_at img_view revision stream =
    (if revision < length (sync_image_history img_view)
     then map_of (sync_image_history img_view ! revision) stream else None)"

fun sync_image_replay where
  "sync_image_replay img_view [] img_entries events = Some (img_entries,events)"
| "sync_image_replay img_view ((position,request) # remaining) img_entries events =
    (let stream = sync_key request; prior = map_of img_entries stream; event = sync_event_key request;
         item = sync_requested request
     in if sync_image_replay_mode request prior \<and> event \<notin> set events \<and>
           (case prior of None \<Rightarrow> True | Some current \<Rightarrow> sync_position current < sync_position item) \<and>
           sync_image_history_at img_view (Suc position) stream = Some item
        then sync_image_replay img_view remaining ((stream,item) # filter (\<lambda>entry. fst entry \<noteq> stream) img_entries) (event # events)
        else None)"

definition sync_image_same_entries :: "sync_image_entries \<Rightarrow> sync_image_entries \<Rightarrow> bool" where
  "sync_image_same_entries left_map right_map \<longleftrightarrow>
    list_all (\<lambda>map_key. map_of left_map map_key = map_of right_map map_key) (map fst left_map @ map fst right_map)"

lemma sync_image_same_entries_iff:
  "sync_image_same_entries left_map right_map \<longleftrightarrow> map_of left_map = map_of right_map"
proof
  assume agree: "sync_image_same_entries left_map right_map"
  show "map_of left_map = map_of right_map"
  proof (rule ext)
    fix map_key
    show "map_of left_map map_key = map_of right_map map_key"
    proof (cases "map_key \<in> set (map fst left_map @ map fst right_map)")
      case True
      with agree show ?thesis by (auto simp: sync_image_same_entries_def list_all_iff)
    next
      case False
      have left: "map_of left_map map_key = None" using False by (simp add: map_of_eq_None_iff)
      have right: "map_of right_map map_key = None" using False by (simp add: map_of_eq_None_iff)
      show ?thesis using left right by simp
    qed
  qed
next
  assume "map_of left_map = map_of right_map"
  then show "sync_image_same_entries left_map right_map"
    by (simp add: sync_image_same_entries_def list_all_iff)
qed

definition sync_image_valid where
  "sync_image_valid img_view \<longleftrightarrow>
    (case sync_image_successes img_view (sync_image_calls img_view) of None \<Rightarrow> False
      | Some successes \<Rightarrow> distinct (map fst successes) \<and>
        (case sync_image_replay img_view (sort_key fst successes) [] [] of None \<Rightarrow> False
         | Some (img_entries,events) \<Rightarrow> sync_image_same_entries (sync_image_streams img_view) img_entries \<and>
             set (sync_image_events img_view) = set events))"

definition sync_image_call_table where
  "sync_image_call_table img_view = map_of (map (\<lambda>(img_call_key,exact,result). (img_call_key,(exact,result))) (sync_image_calls img_view))"

definition sync_image_current_history where
  "sync_image_current_history img_view \<longleftrightarrow>
    length (sync_image_history img_view) = Suc (cut_revision (sync_image_cut img_view)) \<and>
    sync_image_same_entries (last (sync_image_history img_view)) (sync_image_streams img_view)"

text \<open>This is the Sync-relevant projection of the separate, common checks in
  validate_retained_transition. Other ledger, read, policy and settlement fields
  are outside this relation.\<close>

definition sync_image_transition where
  "sync_image_transition previous img_view \<longleftrightarrow>
    sync_image_typed_shape img_view \<and> sync_image_valid img_view \<and> sync_image_current_history img_view \<and>
    (case previous of None \<Rightarrow> cut_revision (sync_image_cut img_view) = 0
     | Some parent \<Rightarrow> sync_image_current_history parent \<and>
       list_all (\<lambda>(img_call_key,exact,result). sync_image_call_table img_view img_call_key = Some (exact,result)) (sync_image_calls parent) \<and>
       list_all (\<lambda>(key,exact). map_of (sync_image_bindings img_view) key = Some exact) (sync_image_bindings parent) \<and>
       take (length (sync_image_journal parent)) (sync_image_journal img_view) = sync_image_journal parent \<and>
       take (length (sync_image_history parent)) (sync_image_history img_view) = sync_image_history parent)"

definition sync_image_projection_rel where
  "sync_image_projection_rel img_view state \<longleftrightarrow>
    sync_image_deployment img_view = sync_deployment_at state \<and> sync_image_cut img_view = sync_current_cut state \<and>
    sync_image_call_table img_view = sync_outcome_table state \<and>
    map_of (sync_image_streams img_view) = sync_entries (sync_current_snapshot state) \<and>
    set (sync_image_events img_view) = {event. sync_used_events state event \<noteq> None}"

lemma sync_image_row_binds_the_exact_original_and_transport:
  assumes "sync_image_check_row img_view (img_call_key,raw,outcome) = Some (core,request)"
  shows "sync_decode_core raw = Some core" "sync_read_operands core = Some request" "sync_call request = img_call_key"
    "map_of (sync_image_bindings img_view) (code_transport_key core) = Some raw"
    "img_call_key \<notin> set (sync_image_ordinary_ids img_view)" "img_call_key \<notin> set (sync_image_regulatory_ids img_view)"
    "encode_wire_core core = raw"
proof -
  show decoded: "sync_decode_core raw = Some core" and "sync_read_operands core = Some request" and "sync_call request = img_call_key"
    and "map_of (sync_image_bindings img_view) (code_transport_key core) = Some raw"
    and "img_call_key \<notin> set (sync_image_ordinary_ids img_view)" and "img_call_key \<notin> set (sync_image_regulatory_ids img_view)"
    using assms by (auto simp: sync_image_check_row_def bind_eq_Some_conv split: if_splits)
  show "encode_wire_core core = raw" by (rule sync_decoded_core_has_the_exact_bytes[OF decoded])
qed

lemma sync_image_success_binds_its_pre_effect_position:
  assumes "sync_image_check_row img_view (img_call_key,raw,Sync_Committed position) = Some (core,request)"
  shows "cut_revision (sync_signed_cut request) = position"
    "position < cut_revision (sync_image_cut img_view)"
    "map_of (sync_image_journal img_view) position = Some (img_call_key,wire_target_domain core)"
  using assms by (auto simp: sync_image_check_row_def sync_image_commit_ok_def bind_eq_Some_conv split: if_splits)

lemma sync_image_lost_transport_refuses_its_retained_row:
  assumes "sync_decode_core raw = Some core"
    "map_of (sync_image_bindings img_view) (code_transport_key core) \<noteq> Some raw"
  shows "sync_image_check_row img_view (img_call_key,raw,outcome) = None"
  using assms by (cases "sync_read_operands core") (simp_all add: sync_image_check_row_def)

lemma sync_image_scan_rejects_an_invalid_row:
  assumes "row \<in> set rows" "sync_image_check_row img_view row = None"
  shows "sync_image_successes img_view rows = None"
  using assms by (induction rows) (auto simp: Option.bind_eq_None_conv split: option.splits prod.splits)

lemma sync_image_lost_transport_invalidates_the_image:
  assumes "(img_call_key,raw,outcome) \<in> set (sync_image_calls img_view)" "sync_decode_core raw = Some core"
    "map_of (sync_image_bindings img_view) (code_transport_key core) \<noteq> Some raw"
  shows "\<not> sync_image_valid img_view"
  using sync_image_scan_rejects_an_invalid_row[OF assms(1)
    sync_image_lost_transport_refuses_its_retained_row[OF assms(2,3)]]
  by (simp add: sync_image_valid_def)

lemma sync_image_two_committed_rows_at_one_journal_position_have_the_same_call_id:
  assumes "sync_image_commit_ok img_view first_id first_core first_request (Sync_Committed position)"
    "sync_image_commit_ok img_view next_id next_core next_request (Sync_Committed position)"
  shows "first_id = next_id" "wire_target_domain first_core = wire_target_domain next_core"
  using assms by (auto simp: sync_image_commit_ok_def)

lemma sync_image_current_projection_keeps_the_same_retained_outcome:
  assumes "sync_image_projection_rel img_view state" "sync_image_call_table img_view img_call_key = Some (exact,outcome)"
  shows "sync_outcome_table state img_call_key = Some (exact,outcome)"
  using assms by (simp add: sync_image_projection_rel_def)

lemma sync_image_selected_reopen_matches_the_checked_projection:
  assumes reopened: "sync_reopen_selected archives recovered observed = Some restored"
    and related: "sync_image_projection_rel img_view (witness_control observed)"
    and current: "sync_image_current_history img_view"
  shows "sync_image_call_table img_view = sync_outcome_table restored"
    "sync_image_cut img_view = sync_current_cut restored"
    "map_of (last (sync_image_history img_view)) = sync_entries (sync_current_snapshot restored)"
    "set (sync_image_events img_view) = {event. sync_used_events restored event \<noteq> None}"
proof -
  have exact: "restored = witness_control observed"
    using reopened by (auto simp: sync_reopen_selected_def witnessed_current_def split: if_splits)
  show "sync_image_call_table img_view = sync_outcome_table restored" "sync_image_cut img_view = sync_current_cut restored"
    "map_of (last (sync_image_history img_view)) = sync_entries (sync_current_snapshot restored)"
    "set (sync_image_events img_view) = {event. sync_used_events restored event \<noteq> None}"
    using related current by (simp_all add: exact sync_image_projection_rel_def sync_image_current_history_def sync_image_same_entries_iff)
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_image_same_entries_iff sync_image_row_binds_the_exact_original_and_transport
    sync_image_success_binds_its_pre_effect_position sync_image_lost_transport_refuses_its_retained_row
    sync_image_lost_transport_invalidates_the_image sync_image_two_committed_rows_at_one_journal_position_have_the_same_call_id
    sync_image_current_projection_keeps_the_same_retained_outcome sync_image_selected_reopen_matches_the_checked_projection})
  then () else error "Unexpected oracle in the Sync retained image link"
\<close>

end

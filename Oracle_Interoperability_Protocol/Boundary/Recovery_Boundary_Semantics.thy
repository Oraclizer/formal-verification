theory Recovery_Boundary_Semantics
  imports "OIP_Product.Recovery_Commit" "OIP_Reference_Profile.Reference_Witness_Selection" "OIP_Product.Promotion_Financial"
begin

section \<open>Crashes, storage rollback and witness rollback around the frozen commit protocol\<close>

text \<open>The storage protocol uses complete-record flushing to an empty address, compare-and-set publication
  and authenticated reopening. The ghost_disks and ghost_cuts history lists supply guarded disk and
  witness restoration copies, and ghost_slot supplies Issue's logical ordinal. Storage and witness
  restoration happen only while nothing runs, and reopening requires no live endpoint. Membership in
  the model histories does not authenticate deployed backups or establish physical durability.
  Relating concrete copies, restoration commands and release positions to these fields requires a
  separate implementation refinement and authentication/storage profile.\<close>

record ('act, 'reply, 'digest) staged_step =
  staged_entry :: "authority_connection \<times> 'act"
  staged_record :: "'digest persisted_commit"
  staged_reply :: 'reply
  staged_base :: "'digest commit_head"

record ('act, 'reply, 'digest) boundary_system =
  sys_disk :: "'digest recovery_store"
  sys_witness :: "'digest commit_head reference_witness_cut"
  sys_endpoint :: "('digest commit_head \<times> retained_product) option"
  sys_staged :: "('act, 'reply, 'digest) staged_step list"
  sys_released :: "(nat \<times> 'reply) list"
  ghost_word :: "(authority_connection \<times> 'act) list"
  ghost_slot :: "'digest commit_head \<Rightarrow> nat option"
  ghost_disks :: "'digest recovery_store list"
  ghost_cuts :: "'digest commit_head reference_witness_cut list"

datatype 'act boundary_event =
    Ask authority_connection 'act
  | Flush_Record nat
  | Publish_Head nat
  | Select_Head nat
  | Issue_Reply nat
  | Repair_Head
  | Crash_Endpoint
  | Reopen_Endpoint current_attachment
  | Roll_Back_Disk nat
  | Roll_Back_Witness nat

fun is_witness_rollback :: "'act boundary_event \<Rightarrow> bool" where
  "is_witness_rollback (Roll_Back_Witness k) = True"
| "is_witness_rollback _ = False"

definition flushed_archive where
  "flushed_archive digest disk = {record. flushed_records disk (head_for_record digest record) = Some record}"

definition record_binds_cut where
  "record_binds_cut digest record observed \<longleftrightarrow> head_for_record digest record = witness_control observed"

lemma flushed_archive_binding_iff:
  "(\<exists>archive \<in> flushed_archive digest disk. record_binds_cut digest archive observed) \<longleftrightarrow>
    (\<exists>r. flushed_records disk (witness_control observed) = Some r \<and> head_for_record digest r = witness_control observed)"
proof
  assume "\<exists>archive \<in> flushed_archive digest disk. record_binds_cut digest archive observed"
  then show "\<exists>r. flushed_records disk (witness_control observed) = Some r \<and> head_for_record digest r = witness_control observed"
    by (auto simp: flushed_archive_def record_binds_cut_def)
next
  assume "\<exists>r. flushed_records disk (witness_control observed) = Some r \<and> head_for_record digest r = witness_control observed"
  then obtain r where flushed: "flushed_records disk (witness_control observed) = Some r"
      and bound: "head_for_record digest r = witness_control observed" by blast
  have "r \<in> flushed_archive digest disk" using flushed bound by (simp add: flushed_archive_def)
  moreover have "record_binds_cut digest r observed" using bound by (simp add: record_binds_cut_def)
  ultimately show "\<exists>archive \<in> flushed_archive digest disk. record_binds_cut digest archive observed" by blast
qed

lemma witnessed_current_on_flushed_archive [simp]:
  "witnessed_current (record_binds_cut digest) (flushed_archive digest disk) recovered observed =
    (if recovered = observed \<and> (\<exists>r. flushed_records disk (witness_control observed) = Some r \<and>
         head_for_record digest r = witness_control observed)
     then Some (witness_control observed) else None)"
  unfolding witnessed_current_def flushed_archive_binding_iff ..

lemma witnessed_selection_on_flushed_archive [simp]:
  "witnessed_selection (record_binds_cut digest) (flushed_archive digest disk) proposal current =
    (if proposal_before proposal = current \<and> witness_version (proposal_after proposal) = Suc (witness_version current) \<and>
        witness_generation current \<le> witness_generation (proposal_after proposal) \<and>
        flushed_records disk (head_for_record digest (proposal_archive proposal)) = Some (proposal_archive proposal) \<and>
        head_for_record digest (proposal_archive proposal) = witness_control (proposal_after proposal)
     then Some (proposal_after proposal) else None)"
  by (simp add: witnessed_selection_def record_binds_cut_def flushed_archive_def)

definition disk_cut where
  "disk_cut disk = map_option (\<lambda>h. \<lparr>witness_version = head_sequence h, witness_generation = 0, witness_control = h\<rparr>)
     (committed_head disk)"

definition witnessed_reopen where
  "witnessed_reopen digest profile attachment disk w =
    (case disk_cut disk of None \<Rightarrow> None
     | Some recovered \<Rightarrow>
        (case witnessed_current (record_binds_cut digest) (flushed_archive digest disk) recovered w of None \<Rightarrow> None
         | Some head \<Rightarrow> map_option (\<lambda>W. (head, capture_retained_product W))
             (reopen_from_authenticated_head digest profile (Some attachment) disk)))"

definition advance_endpoint where
  "advance_endpoint p h endpoint =
    (case endpoint of None \<Rightarrow> None
     | Some (base, R) \<Rightarrow> if base = staged_base p then Some (h, image_records (staged_record p)) else Some (base, R))"

definition staged_commit where
  "staged_commit profile base R =
    \<lparr>image_profile = profile, image_sequence = Suc (head_sequence base), image_parent = Some (head_digest base),
     image_records = R\<rparr>"

definition stage_step where
  "stage_step profile c a base R reply \<sigma> =
    \<sigma>\<lparr>sys_staged := sys_staged \<sigma> @ [\<lparr>staged_entry = (c, a), staged_record = staged_commit profile base R,
       staged_reply = reply, staged_base = base\<rparr>]\<rparr>"

definition witness_fresh where
  "witness_fresh \<sigma> base \<longleftrightarrow> disk_cut (sys_disk \<sigma>) = Some (sys_witness \<sigma>) \<and> witness_control (sys_witness \<sigma>) = base"

definition disk_fresh where
  "disk_fresh \<sigma> base \<longleftrightarrow> committed_head (sys_disk \<sigma>) = Some base"

definition request_effect where
  "request_effect step profile fresh c a \<sigma> =
    (case sys_endpoint \<sigma> of None \<Rightarrow> \<sigma>
     | Some (base, R) \<Rightarrow>
        (if fst (step c a R) = R then
           (if fresh \<sigma> base
            then \<sigma>\<lparr>sys_released := sys_released \<sigma> @ [(length (ghost_word \<sigma>), snd (step c a R))],
                    ghost_word := ghost_word \<sigma> @ [(c, a)]\<rparr>
            else \<sigma>)
         else stage_step profile c a base (fst (step c a R)) (snd (step c a R)) \<sigma>))"

definition flush_effect where
  "flush_effect digest i \<sigma> =
    (if i < length (sys_staged \<sigma>) then
       \<sigma>\<lparr>sys_disk := flush_commit_record digest (staged_record (sys_staged \<sigma> ! i)) (sys_disk \<sigma>),
         ghost_disks := ghost_disks \<sigma> @ [flush_commit_record digest (staged_record (sys_staged \<sigma> ! i)) (sys_disk \<sigma>)]\<rparr>
     else \<sigma>)"

definition publish_effect where
  "publish_effect digest i \<sigma> =
    (if i < length (sys_staged \<sigma>) then
       (let p = sys_staged \<sigma> ! i;
            disk = publish_recovery_head digest (Some (staged_base p)) (staged_record p) (sys_disk \<sigma>)
        in \<sigma>\<lparr>sys_disk := disk, ghost_disks := ghost_disks \<sigma> @ [disk]\<rparr>)
     else \<sigma>)"

definition selection_proposal where
  "selection_proposal digest p w =
    \<lparr>proposal_before = w,
     proposal_after = w\<lparr>witness_version := Suc (witness_version w),
                        witness_control := head_for_record digest (staged_record p)\<rparr>,
     proposal_archive = staged_record p\<rparr>"

definition select_effect where
  "select_effect digest i \<sigma> =
    (if i < length (sys_staged \<sigma>) then
       (let p = sys_staged \<sigma> ! i; h = head_for_record digest (staged_record p); w = sys_witness \<sigma> in
        if committed_head (sys_disk \<sigma>) = Some h \<and> witness_control w = staged_base p then
          (case witnessed_selection (record_binds_cut digest) (flushed_archive digest (sys_disk \<sigma>))
                  (selection_proposal digest p w) w of
             None \<Rightarrow> \<sigma>
           | Some w' \<Rightarrow> \<sigma>\<lparr>sys_witness := w', sys_endpoint := advance_endpoint p h (sys_endpoint \<sigma>),
                 ghost_word := ghost_word \<sigma> @ [staged_entry p],
                 ghost_slot := (ghost_slot \<sigma>)(h := Some (length (ghost_word \<sigma>))),
                 ghost_cuts := ghost_cuts \<sigma> @ [w']\<rparr>)
        else \<sigma>)
     else \<sigma>)"

definition issue_effect where
  "issue_effect digest i \<sigma> =
    (if i < length (sys_staged \<sigma>) then
       (let p = sys_staged \<sigma> ! i; h = head_for_record digest (staged_record p) in
        if committed_head (sys_disk \<sigma>) = Some h \<and> flushed_records (sys_disk \<sigma>) h = Some (staged_record p) \<and>
           witness_control (sys_witness \<sigma>) = h
        then \<sigma>\<lparr>sys_released := sys_released \<sigma> @ [(the (ghost_slot \<sigma> h), staged_reply p)]\<rparr>
        else \<sigma>)
     else \<sigma>)"

definition repair_effect where
  "repair_effect \<sigma> =
    (if committed_head (sys_disk \<sigma>) \<noteq> Some (witness_control (sys_witness \<sigma>)) \<and>
        flushed_records (sys_disk \<sigma>) (witness_control (sys_witness \<sigma>)) \<noteq> None
     then \<sigma>\<lparr>sys_disk := (sys_disk \<sigma>)\<lparr>committed_head := Some (witness_control (sys_witness \<sigma>))\<rparr>,
            ghost_disks := ghost_disks \<sigma> @ [(sys_disk \<sigma>)\<lparr>committed_head := Some (witness_control (sys_witness \<sigma>))\<rparr>]\<rparr>
     else \<sigma>)"

definition system_down where
  "system_down \<sigma> \<longleftrightarrow> sys_endpoint \<sigma> = None \<and> sys_staged \<sigma> = []"

definition reopen_effect where
  "reopen_effect digest profile attachment \<sigma> =
    (if sys_endpoint \<sigma> = None
     then \<sigma>\<lparr>sys_endpoint := witnessed_reopen digest profile attachment (sys_disk \<sigma>) (sys_witness \<sigma>)\<rparr> else \<sigma>)"

definition roll_back_disk_effect where
  "roll_back_disk_effect k \<sigma> =
    (if system_down \<sigma> \<and> k < length (ghost_disks \<sigma>) then \<sigma>\<lparr>sys_disk := ghost_disks \<sigma> ! k\<rparr> else \<sigma>)"

definition roll_back_witness_effect where
  "roll_back_witness_effect k \<sigma> =
    (if system_down \<sigma> \<and> k < length (ghost_cuts \<sigma>) then \<sigma>\<lparr>sys_witness := ghost_cuts \<sigma> ! k\<rparr> else \<sigma>)"

fun boundary_step where
  "boundary_step step digest profile (Ask c a) \<sigma> = request_effect step profile witness_fresh c a \<sigma>"
| "boundary_step step digest profile (Flush_Record i) \<sigma> = flush_effect digest i \<sigma>"
| "boundary_step step digest profile (Publish_Head i) \<sigma> = publish_effect digest i \<sigma>"
| "boundary_step step digest profile (Select_Head i) \<sigma> = select_effect digest i \<sigma>"
| "boundary_step step digest profile (Issue_Reply i) \<sigma> = issue_effect digest i \<sigma>"
| "boundary_step step digest profile Repair_Head \<sigma> = repair_effect \<sigma>"
| "boundary_step step digest profile Crash_Endpoint \<sigma> = \<sigma>\<lparr>sys_endpoint := None, sys_staged := []\<rparr>"
| "boundary_step step digest profile (Reopen_Endpoint attachment) \<sigma> = reopen_effect digest profile attachment \<sigma>"
| "boundary_step step digest profile (Roll_Back_Disk k) \<sigma> = roll_back_disk_effect k \<sigma>"
| "boundary_step step digest profile (Roll_Back_Witness k) \<sigma> = roll_back_witness_effect k \<sigma>"

subsection \<open>The same system without an independent witness\<close>

definition disk_only_publish where
  "disk_only_publish digest i \<sigma> =
    (if i < length (sys_staged \<sigma>) then
       (let p = sys_staged \<sigma> ! i; h = head_for_record digest (staged_record p) in
        if committed_head (sys_disk \<sigma>) = Some (staged_base p) \<and>
           candidate_extends_head (Some (staged_base p)) (staged_record p) \<and>
           flushed_records (sys_disk \<sigma>) h = Some (staged_record p)
        then \<sigma>\<lparr>sys_disk := publish_recovery_head digest (Some (staged_base p)) (staged_record p) (sys_disk \<sigma>),
               ghost_disks := ghost_disks \<sigma> @ [publish_recovery_head digest (Some (staged_base p)) (staged_record p) (sys_disk \<sigma>)],
               sys_endpoint := advance_endpoint p h (sys_endpoint \<sigma>),
               ghost_word := ghost_word \<sigma> @ [staged_entry p],
               ghost_slot := (ghost_slot \<sigma>)(h := Some (length (ghost_word \<sigma>)))\<rparr>
        else \<sigma>)
     else \<sigma>)"

definition disk_only_issue where
  "disk_only_issue digest i \<sigma> =
    (if i < length (sys_staged \<sigma>) then
       (let p = sys_staged \<sigma> ! i; h = head_for_record digest (staged_record p) in
        if committed_head (sys_disk \<sigma>) = Some h \<and> flushed_records (sys_disk \<sigma>) h = Some (staged_record p)
        then \<sigma>\<lparr>sys_released := sys_released \<sigma> @ [(the (ghost_slot \<sigma> h), staged_reply p)]\<rparr>
        else \<sigma>)
     else \<sigma>)"

definition disk_only_reopen where
  "disk_only_reopen accept digest profile attachment \<sigma> =
    (if sys_endpoint \<sigma> = None then
       \<sigma>\<lparr>sys_endpoint := (if accept (sys_disk \<sigma>) then
            (case committed_head (sys_disk \<sigma>) of None \<Rightarrow> None
             | Some head \<Rightarrow> map_option (\<lambda>W. (head, capture_retained_product W))
                 (reopen_from_authenticated_head digest profile (Some attachment) (sys_disk \<sigma>)))
          else None)\<rparr>
     else \<sigma>)"

fun disk_only_step where
  "disk_only_step accept step digest profile (Ask c a) \<sigma> = request_effect step profile disk_fresh c a \<sigma>"
| "disk_only_step accept step digest profile (Flush_Record i) \<sigma> = flush_effect digest i \<sigma>"
| "disk_only_step accept step digest profile (Publish_Head i) \<sigma> = disk_only_publish digest i \<sigma>"
| "disk_only_step accept step digest profile (Select_Head i) \<sigma> = \<sigma>"
| "disk_only_step accept step digest profile (Issue_Reply i) \<sigma> = disk_only_issue digest i \<sigma>"
| "disk_only_step accept step digest profile Repair_Head \<sigma> = \<sigma>"
| "disk_only_step accept step digest profile Crash_Endpoint \<sigma> = \<sigma>\<lparr>sys_endpoint := None, sys_staged := []\<rparr>"
| "disk_only_step accept step digest profile (Reopen_Endpoint attachment) \<sigma> =
    disk_only_reopen accept digest profile attachment \<sigma>"
| "disk_only_step accept step digest profile (Roll_Back_Disk k) \<sigma> = roll_back_disk_effect k \<sigma>"
| "disk_only_step accept step digest profile (Roll_Back_Witness k) \<sigma> = \<sigma>"

subsection \<open>Start state and the uninterrupted comparison run\<close>

definition genesis_record where
  "genesis_record profile R0 = \<lparr>image_profile = profile, image_sequence = 0, image_parent = None, image_records = R0\<rparr>"

definition genesis_disk where
  "genesis_disk digest profile R0 =
    \<lparr>flushed_records = (\<lambda>_. None)(head_for_record digest (genesis_record profile R0) := Some (genesis_record profile R0)),
     committed_head = Some (head_for_record digest (genesis_record profile R0))\<rparr>"

definition genesis_cut where
  "genesis_cut digest profile R0 =
    \<lparr>witness_version = 0, witness_generation = 0, witness_control = head_for_record digest (genesis_record profile R0)\<rparr>"

definition genesis_system where
  "genesis_system digest profile R0 =
    \<lparr>sys_disk = genesis_disk digest profile R0, sys_witness = genesis_cut digest profile R0,
     sys_endpoint = Some (head_for_record digest (genesis_record profile R0), R0),
     sys_staged = [], sys_released = [], ghost_word = [], ghost_slot = (\<lambda>_. None),
     ghost_disks = [genesis_disk digest profile R0], ghost_cuts = [genesis_cut digest profile R0]\<rparr>"

fun run_word_transcript where
  "run_word_transcript step [] R = (R, [])"
| "run_word_transcript step ((c, a) # rest) R =
    (fst (run_word_transcript step rest (fst (step c a R))),
     snd (step c a R) # snd (run_word_transcript step rest (fst (step c a R))))"

lemma transcript_length [simp]: "length (snd (run_word_transcript step w R)) = length w"
  by (induction step w R rule: run_word_transcript.induct) simp_all

lemma transcript_final_is_the_product_word:
  "fst (run_word_transcript step w R) = run_product_action_word step w R"
  by (induction step w R rule: run_word_transcript.induct) simp_all

lemma product_word_append:
  "run_product_action_word step (w @ v) R = run_product_action_word step v (run_product_action_word step w R)"
  by (induction step w R rule: run_product_action_word.induct) simp_all

lemma transcript_append:
  "snd (run_word_transcript step (w @ v) R) =
    snd (run_word_transcript step w R) @ snd (run_word_transcript step v (run_product_action_word step w R))"
  by (induction step w R rule: run_word_transcript.induct) simp_all

lemma transcript_prefix:
  "k < length w \<Longrightarrow> snd (run_word_transcript step (w @ v) R) ! k = snd (run_word_transcript step w R) ! k"
  by (simp add: transcript_append nth_append)

lemma product_word_snoc:
  "run_product_action_word step (w @ [x]) R = fst (step (fst x) (snd x) (run_product_action_word step w R))"
  by (cases x) (simp add: product_word_append)

lemma transcript_snoc_last:
  "snd (run_word_transcript step (w @ [x]) R) ! length w = snd (step (fst x) (snd x) (run_product_action_word step w R))"
  by (cases x) (simp add: transcript_append nth_append)

subsection \<open>Records are identified by their address\<close>

definition content_at where
  "content_at digest h R \<longleftrightarrow> (\<exists>r. head_for_record digest r = h \<and> image_records r = R)"

lemma content_at_record [simp]: "content_at digest (head_for_record digest r) (image_records r)"
  by (auto simp: content_at_def)

lemma addressed_records_are_unique:
  assumes "inj digest" "head_for_record digest r = head_for_record digest r'"
  shows "r = r'"
  using assms by (simp add: head_for_record_def inj_eq)

lemma content_at_unique:
  assumes "inj digest" "content_at digest h R" "content_at digest h R'"
  shows "R = R'"
proof -
  obtain r where r: "head_for_record digest r = h" "image_records r = R" using assms(2) by (auto simp: content_at_def)
  obtain r' where r': "head_for_record digest r' = h" "image_records r' = R'" using assms(3) by (auto simp: content_at_def)
  have "r = r'" by (rule addressed_records_are_unique[OF assms(1)]) (simp add: r(1) r'(1))
  then show ?thesis using r(2) r'(2) by simp
qed

lemma witnessed_reopen_returns_the_witnessed_record:
  assumes "witnessed_reopen digest profile attachment disk w = Some (h, R)"
  shows "h = witness_control w \<and> committed_head disk = Some h \<and>
    (\<exists>r. flushed_records disk h = Some r \<and> head_for_record digest r = h \<and> image_records r = R)"
proof (cases "committed_head disk")
  case None
  then have "disk_cut disk = None" by (simp add: disk_cut_def)
  then show ?thesis using assms by (simp add: witnessed_reopen_def)
next
  case (Some head)
  let ?recovered = "\<lparr>witness_version = head_sequence head, witness_generation = 0, witness_control = head\<rparr>"
  have cut: "disk_cut disk = Some ?recovered" using Some by (simp add: disk_cut_def)
  show ?thesis
  proof (cases "?recovered = w \<and> (\<exists>r. flushed_records disk (witness_control w) = Some r \<and>
      head_for_record digest r = witness_control w)")
    case False
    have "witnessed_current (record_binds_cut digest) (flushed_archive digest disk) ?recovered w = None"
      unfolding witnessed_current_on_flushed_archive using False by (rule if_not_P)
    then show ?thesis using assms cut by (simp add: witnessed_reopen_def del: witnessed_current_on_flushed_archive)
  next
    case True
    have at: "w = ?recovered" using True by simp
    obtain r where r: "flushed_records disk head = Some r" "head_for_record digest r = head" using True by auto
    have current: "witnessed_current (record_binds_cut digest) (flushed_archive digest disk) ?recovered w = Some head"
      unfolding witnessed_current_on_flushed_archive using True by (simp add: at)
    have opened: "reopen_from_authenticated_head digest profile (Some attachment) disk =
        (if attachment_profile attachment \<noteq> profile \<or> head_profile head \<noteq> profile then None
         else Some (reopen_retained_product (attachment_connection attachment) (image_records r)))"
      using Some r by (simp add: reopen_from_authenticated_head_def)
    have "h = head \<and> R = image_records r"
      using assms cut current opened
      by (simp add: witnessed_reopen_def product_round_trip_preserves_the_durable_projection
          del: witnessed_current_on_flushed_archive split: if_split_asm)
    then show ?thesis using Some r at by auto
  qed
qed

definition once_only where
  "once_only right_of released \<longleftrightarrow>
    (\<forall>k1 r1 k2 r2. (k1, r1) \<in> set released \<longrightarrow> (k2, r2) \<in> set released \<longrightarrow>
       right_of r1 \<noteq> None \<longrightarrow> right_of r1 = right_of r2 \<longrightarrow> k1 = k2)"

lemma two_positions_break_once_only:
  assumes "(k1, r1) \<in> set released" "(k2, r2) \<in> set released" "right_of r1 \<noteq> None"
    "right_of r1 = right_of r2" "k1 \<noteq> k2"
  shows "\<not> once_only right_of released"
  using assms unfolding once_only_def by blast

subsection \<open>A small spending instance used for concrete histories\<close>

datatype toy_action = Toy_Spend | Toy_Look
datatype toy_reply = Toy_Token nat | Toy_Seen nat
datatype twin_action = Twin_Pay | Twin_Echo

definition toy_bump :: "retained_product \<Rightarrow> retained_product" where
  "toy_bump R = R\<lparr>retained_provider := Suc (retained_provider R)\<rparr>"

lemma toy_bump_changes [simp]: "toy_bump R \<noteq> R"
  by (cases R) (simp add: toy_bump_def)

lemma toy_bump_changes' [simp]: "R \<noteq> toy_bump R"
  by (metis toy_bump_changes)

lemma toy_bump_provider [simp]: "retained_provider (toy_bump R) = Suc (retained_provider R)"
  by (simp add: toy_bump_def)

fun toy_step :: "authority_connection \<Rightarrow> toy_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> toy_reply" where
  "toy_step c Toy_Spend R = (toy_bump R, Toy_Token (retained_provider R))"
| "toy_step c Toy_Look R = (R, Toy_Seen (retained_provider R))"

fun twin_step :: "authority_connection \<Rightarrow> twin_action \<Rightarrow> retained_product \<Rightarrow> retained_product \<times> toy_reply" where
  "twin_step c Twin_Pay R = (toy_bump R, Toy_Token (retained_provider R))"
| "twin_step c Twin_Echo R = (toy_bump R, Toy_Seen (retained_provider R))"

fun toy_right :: "toy_reply \<Rightarrow> nat option" where
  "toy_right (Toy_Token n) = Some n"
| "toy_right (Toy_Seen n) = None"

definition toy_digest :: "(nat \<times> nat) persisted_commit \<Rightarrow> nat \<times> nat" where
  "toy_digest r = (image_sequence r, retained_provider (image_records r))"

lemmas boundary_run_simps = request_effect_def stage_step_def witness_fresh_def disk_fresh_def flush_effect_def
  publish_effect_def select_effect_def selection_proposal_def issue_effect_def repair_effect_def system_down_def
  reopen_effect_def roll_back_disk_effect_def roll_back_witness_effect_def disk_only_publish_def disk_only_issue_def
  disk_only_reopen_def genesis_system_def genesis_disk_def genesis_cut_def genesis_record_def staged_commit_def
  flush_commit_record_def publish_recovery_head_def candidate_extends_head_def witnessed_reopen_def disk_cut_def
  reopen_from_authenticated_head_def advance_endpoint_def head_for_record_def toy_digest_def Let_def
  product_round_trip_preserves_the_durable_projection

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms flushed_archive_binding_iff witnessed_current_on_flushed_archive
      witnessed_selection_on_flushed_archive transcript_final_is_the_product_word product_word_append
      transcript_append transcript_prefix product_word_snoc transcript_snoc_last addressed_records_are_unique
      content_at_unique witnessed_reopen_returns_the_witnessed_record two_positions_break_once_only
      toy_bump_changes toy_bump_changes'})
  then () else error "Unexpected oracle in the recovery boundary semantics"
\<close>

end

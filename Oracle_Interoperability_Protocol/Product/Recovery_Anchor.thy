theory Recovery_Anchor
  imports Recovery_Records
begin

section \<open>Flushed records and the independent authoritative head\<close>

record recovery_profile =
  recovery_deployment :: nat
  recovery_format :: nat
  recovery_authority_profile :: nat

record 'digest persisted_commit =
  image_profile :: recovery_profile
  image_sequence :: nat
  image_parent :: "'digest option"
  image_records :: retained_product

record 'digest commit_head =
  head_profile :: recovery_profile
  head_sequence :: nat
  head_digest :: 'digest

record 'digest recovery_store =
  flushed_records :: "'digest commit_head \<Rightarrow> 'digest persisted_commit option"
  committed_head :: "'digest commit_head option"

record current_attachment =
  attachment_profile :: recovery_profile
  attachment_connection :: authority_connection

definition head_for_record where
  "head_for_record digest record =
    \<lparr>head_profile = image_profile record, head_sequence = image_sequence record, head_digest = digest record\<rparr>"

definition flush_commit_record where
  "flush_commit_record digest record s =
    (let address = head_for_record digest record in
      if flushed_records s address = None
      then s\<lparr>flushed_records := (flushed_records s)(address := Some record)\<rparr> else s)"

definition candidate_extends_head where
  "candidate_extends_head before record \<longleftrightarrow>
    (case before of None \<Rightarrow> image_sequence record = 0 \<and> image_parent record = None
     | Some head \<Rightarrow> image_profile record = head_profile head \<and>
          image_sequence record = Suc (head_sequence head) \<and> image_parent record = Some (head_digest head))"

definition publish_recovery_head where
  "publish_recovery_head digest expected record s =
    (if committed_head s = expected \<and> candidate_extends_head expected record \<and>
        flushed_records s (head_for_record digest record) = Some record
     then s\<lparr>committed_head := Some (head_for_record digest record)\<rparr> else s)"

definition reopen_from_authenticated_head where
  "reopen_from_authenticated_head digest profile attachment s =
    (case (attachment, committed_head s) of (Some current, Some head) \<Rightarrow>
       if attachment_profile current \<noteq> profile \<or> head_profile head \<noteq> profile then None
       else (case flushed_records s head of None \<Rightarrow> None
        | Some record \<Rightarrow> if head_for_record digest record = head
            then Some (reopen_retained_product (attachment_connection current) (image_records record)) else None)
     | _ \<Rightarrow> None)"

lemma flushed_candidate_is_not_visible_before_the_head_changes:
  "committed_head (flush_commit_record digest record s) = committed_head s"
  by (simp add: flush_commit_record_def Let_def)

lemma missing_flush_cannot_publish_a_reply_cut:
  assumes "flushed_records s (head_for_record digest record) \<noteq> Some record"
  shows "publish_recovery_head digest expected record s = s"
  using assms by (simp add: publish_recovery_head_def)

lemma losing_a_compare_and_set_does_not_rewrite_the_current_head:
  assumes "committed_head s \<noteq> expected"
  shows "publish_recovery_head digest expected record s = s"
  using assms by (simp add: publish_recovery_head_def)

lemma published_head_identifies_the_flushed_record:
  assumes "committed_head s = expected" "candidate_extends_head expected record"
    "flushed_records s (head_for_record digest record) = Some record"
  shows "committed_head (publish_recovery_head digest expected record s) = Some (head_for_record digest record)"
    "flushed_records (publish_recovery_head digest expected record s) (head_for_record digest record) = Some record"
  using assms by (simp_all add: publish_recovery_head_def)

theorem independently_anchored_records_construct_a_fresh_endpoint:
  assumes "committed_head s = Some (head_for_record digest record)"
    "flushed_records s (head_for_record digest record) = Some record"
    "attachment_profile attachment = image_profile record"
  shows "reopen_from_authenticated_head digest (image_profile record) (Some attachment) s =
    Some (reopen_retained_product (attachment_connection attachment) (image_records record))"
  using assms by (simp add: reopen_from_authenticated_head_def head_for_record_def)

lemma an_old_valid_record_at_the_current_address_is_rejected:
  assumes "committed_head s = Some (head_for_record digest current)"
    "flushed_records s (head_for_record digest current) = Some old"
    "image_sequence old \<noteq> image_sequence current"
  shows "reopen_from_authenticated_head digest profile attachment s = None"
proof -
  have distinct: "head_for_record digest old \<noteq> head_for_record digest current"
    using assms(3) by (simp add: head_for_record_def)
  show ?thesis using assms(1,2) distinct
    by (cases attachment) (simp_all add: reopen_from_authenticated_head_def)
qed

lemma a_changed_body_cannot_match_the_anchored_digest:
  assumes "committed_head s = Some (head_for_record digest current)"
    "flushed_records s (head_for_record digest current) = Some altered"
    "digest altered \<noteq> digest current"
  shows "reopen_from_authenticated_head digest profile attachment s = None"
proof -
  have distinct: "head_for_record digest altered \<noteq> head_for_record digest current"
    using assms(3) by (simp add: head_for_record_def)
  show ?thesis using assms(1,2) distinct
    by (cases attachment) (simp_all add: reopen_from_authenticated_head_def)
qed

lemma a_missing_anchor_record_does_not_restart_from_genesis:
  assumes "committed_head s = Some head" "flushed_records s head = None"
  shows "reopen_from_authenticated_head digest profile attachment s = None"
  using assms by (cases attachment) (simp_all add: reopen_from_authenticated_head_def)

end

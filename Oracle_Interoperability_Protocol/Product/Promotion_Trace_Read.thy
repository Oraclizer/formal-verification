theory Promotion_Trace_Read
  imports Regulated_Program
begin

context source_attestation
begin

definition source_segment where
  "source_segment before after \<longleftrightarrow> (\<exists>word. after = finality_calls.run_calls word before)"

lemma empty_source_segment [simp]:
  "source_segment calls calls"
  unfolding source_segment_def by (intro exI[of _ "[]"]) simp

lemma source_segments_compose:
  assumes "source_segment a b" "source_segment b c"
  shows "source_segment a c"
proof -
  obtain left where b: "b = finality_calls.run_calls left a" using assms(1) by (auto simp: source_segment_def)
  obtain right where c: "c = finality_calls.run_calls right b" using assms(2) by (auto simp: source_segment_def)
  show ?thesis unfolding source_segment_def
    by (intro exI[of _ "left @ right"]) (simp add: b c lock_public_segments_append)
qed

definition read_source_segment where
  "read_source_segment before after \<longleftrightarrow>
    source_segment (exact_calls (read_authority before)) (exact_calls (read_authority after)) \<and>
    (\<forall>key recorded. origin_decisions (settlement_primary (read_authority before)) key = Some recorded \<longrightarrow>
       origin_decisions (settlement_primary (read_authority after)) key = Some recorded)"

lemma read_source_segment_refl [simp]:
  "read_source_segment reads reads"
  by (simp add: read_source_segment_def)

lemma a_read_authority_step_is_a_real_source_segment:
  "read_source_segment reads
    (reads\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack action (read_authority reads)\<rparr>)"
  unfolding read_source_segment_def source_segment_def
  by (simp add: exact_step_has_a_public_segment exact_step_keeps_existing_decision)

lemma checked_execution_is_a_source_segment:
  "read_source_segment reads (fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry actor expected call_id payload reads))"
proof -
  let ?next = "fst (execute_at_checked_cut permitted verified maintainers registered verified_ack entry actor expected call_id payload reads)"
  have "?next = reads \<or> ?next = reads\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
     (Exact_Submit entry actor call_id payload) (read_authority reads)\<rparr>"
    using checked_execution_source_is_stutter_or_actual_submit
      [of permitted verified maintainers registered verified_ack entry actor expected call_id payload reads]
    by (simp only: Let_def)
  then show ?thesis
  proof
    assume same: "?next = reads"
    show ?thesis unfolding same by (rule read_source_segment_refl)
  next
    assume effect: "?next = reads\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
      (Exact_Submit entry actor call_id payload) (read_authority reads)\<rparr>"
    show ?thesis unfolding effect by (rule a_read_authority_step_is_a_real_source_segment)
  qed
qed

lemma product_read_step_has_a_source_segment:
  "read_source_segment reads (product_read_step read_permitted permitted verified maintainers registered verified_ack action reads)"
proof (cases action)
  case (Capture_Read actor session query)
  then show ?thesis by (simp add: capture_product_cache_def Let_def read_source_segment_def split: option.splits if_splits)
next
  case (Execute_Checked entry actor expected call_id payload)
  then show ?thesis by (simp add: checked_execution_is_a_source_segment)
next
  case (Read_Authority_Action internal)
  then show ?thesis by (simp add: a_read_authority_step_is_a_real_source_segment split: if_splits)
qed

end

end

theory Checked_Execution
  imports Read_Source_History
begin

datatype checked_execution_reply =
    Forwarded_At_Checked_Cut
  | Checked_Execution_Busy
  | Checked_Execution_Unavailable
  | Checked_Execution_Rejected

context source_attestation
begin

definition execute_at_checked_cut where
  "execute_at_checked_cut permitted verified maintainers registered verified_ack
     entry who expected call_id payload s =
    (let authority = read_authority s; envelope = payload_envelope payload;
         actual = observed_product_cut authority in
      if \<not> result_access_bound verified who call_id payload (origin_outcomes (settlement_primary authority))
      then (s, Checked_Execution_Rejected)
      else if \<not> read_authority_available s then (s, Checked_Execution_Unavailable)
      else if expected \<noteq> actual \<or> envelope_cut envelope \<noteq> actual
      then (s, Checked_Execution_Busy)
      else (s\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
               (Exact_Submit entry who call_id payload) authority\<rparr>, Forwarded_At_Checked_Cut))"

lemma stale_cut_cannot_authorize_a_product_effect:
  assumes "expected \<noteq> observed_product_cut (read_authority s)"
  shows "fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry who expected call_id payload s) = s"
  using assms by (simp add: execute_at_checked_cut_def Let_def split: if_splits)

lemma stale_cut_at_authorized_live_endpoint_is_busy:
  assumes "result_access_bound verified who call_id payload (origin_outcomes (settlement_primary (read_authority s)))"
    "read_authority_available s"
    "expected \<noteq> observed_product_cut (read_authority s)"
  shows "execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry who expected call_id payload s = (s, Checked_Execution_Busy)"
  using assms by (simp add: execute_at_checked_cut_def Let_def)

lemma changed_authority_epoch_blocks_checked_execution:
  assumes "cut_authority_epoch expected \<noteq> cut_authority_epoch (observed_product_cut (read_authority s))"
  shows "fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry who expected call_id payload s) = s"
  by (rule stale_cut_cannot_authorize_a_product_effect) (use assms in auto)

theorem forwarded_execution_consumes_the_cut_it_checked:
  assumes "execute_at_checked_cut permitted verified maintainers registered verified_ack
    entry who expected call_id payload s = (next, Forwarded_At_Checked_Cut)"
  shows "expected = observed_product_cut (read_authority s) \<and>
    envelope_cut (payload_envelope payload) = expected \<and>
    read_authority next = exact_step permitted verified maintainers registered verified_ack
      (Exact_Submit entry who call_id payload) (read_authority s)"
  using assms by (auto simp: execute_at_checked_cut_def Let_def split: if_splits)

lemma checked_execution_source_is_stutter_or_actual_submit:
  "let next = fst (execute_at_checked_cut permitted verified maintainers registered verified_ack
          entry who expected call_id payload s)
    in next = s \<or> next = s\<lparr>read_authority := exact_step permitted verified maintainers registered verified_ack
       (Exact_Submit entry who call_id payload) (read_authority s)\<rparr>"
  by (simp add: execute_at_checked_cut_def Let_def split: if_splits)

end

end

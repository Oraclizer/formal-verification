(* SPDX-License-Identifier: BSD-3-Clause *)
theory Integration_Transport
  imports Historical_Decision_Projection Integration_Boundaries
begin

section \<open>Lossless Ordered Blocks Are Inputs to the Existing Recovery Check\<close>

definition recovery_from_blocks :: "'state \<Rightarrow>
  ('command,'reply,'environment) authority_call_entry list list \<Rightarrow>
  ('state,'command,'reply,'environment) recovery_candidate" where
  "recovery_from_blocks genesis blocks=\<lparr>candidate_genesis=genesis,candidate_entries=concat blocks\<rparr>"

definition encode_recovery_blocks ::
  "('state,'command,'reply,'environment) recovery_candidate \<Rightarrow>
    'state \<times> ('command,'reply,'environment) authority_call_entry list list" where
  "encode_recovery_blocks candidate=
    (candidate_genesis candidate,map (\<lambda>entry. [entry])(candidate_entries candidate))"

lemma singleton_blocks_decode [simp]:
  "concat(map (\<lambda>entry. [entry])entries)=entries"
  by (induction entries) simp_all

theorem recovery_block_encoding_has_an_actual_decoder:
  "recovery_from_blocks(fst(encode_recovery_blocks candidate))(snd(encode_recovery_blocks candidate))=candidate"
  by (cases candidate) (simp add: recovery_from_blocks_def encode_recovery_blocks_def)

lemma ordered_block_decoding_preserves_concatenation:
  "candidate_entries(recovery_from_blocks genesis(first@second))=
    candidate_entries(recovery_from_blocks genesis first)@
      candidate_entries(recovery_from_blocks genesis second)"
  by (simp add: recovery_from_blocks_def)

theorem three_ordered_blocks_are_associative:
  "recovery_from_blocks genesis((first@second)@third)=
    recovery_from_blocks genesis(first@(second@third))"
  by simp

context durable_call_protocol
begin

theorem decoded_blocks_use_the_original_current_source_check:
  "checked_current_replay source
      (recovery_from_blocks(fst(encode_recovery_blocks candidate))(snd(encode_recovery_blocks candidate)))=
    checked_current_replay source candidate"
  by (simp only: recovery_block_encoding_has_an_actual_decoder)

theorem actual_current_source_has_a_lossless_block_input:
  assumes "authority_replay_contract source"
  shows "checked_current_replay source
    (recovery_from_blocks(fst(encode_recovery_blocks(current_source_candidate source)))
      (snd(encode_recovery_blocks(current_source_candidate source))))=
    Some(call_authority_state source)"
  by (simp only: recovery_block_encoding_has_an_actual_decoder
      actual_source_produces_a_valid_complete_candidate[OF assms])

theorem a_complete_ordered_partition_recovers_the_actual_source:
  assumes contract: "authority_replay_contract source"
    and partition: "concat blocks=call_authority_log source"
  shows "checked_current_replay source(recovery_from_blocks(call_genesis source)blocks)=
    Some(call_authority_state source)"
proof -
  have decoded:
    "recovery_from_blocks(call_genesis source)blocks=current_source_candidate source"
    by (simp add: recovery_from_blocks_def current_source_candidate_def partition)
  show ?thesis by (simp only: decoded actual_source_produces_a_valid_complete_candidate[OF contract])
qed

theorem changed_block_order_is_rejected_by_the_actual_recovery_check:
  assumes "concat changed_blocks\<noteq>call_authority_log source"
  shows "checked_current_replay source(recovery_from_blocks genesis changed_blocks)=None"
  using assms by (simp add: checked_current_replay_def recovery_from_blocks_def)

end

section \<open>Exact Recovery Preserves the Existing Authority and Call Identifiers\<close>

context operational_call_projection
begin

theorem restored_runtime_transports_every_future_call_word:
  assumes contract: "original.authority_replay_contract(recovery_source runtime)"
    and connected: "recovery_connected runtime"
    and recovered: "original.checked_current_replay(recovery_source runtime)candidate=Some restored"
  shows "reduced.run_calls actions(normalize_call_machine(recovery_source
      (original.dispatch_from_recovered_replica call_id command
        (original.restore_current_replica candidate runtime))))=
    normalize_call_machine(original.run_calls actions
      (original.dispatch_client_call call_id command(recovery_source runtime)))"
  by (simp only: original.restored_dispatch_is_the_actual_guarded_call[OF contract connected recovered]
      finite_call_projection)

theorem restored_runtime_preserves_all_future_completed_replies:
  assumes contract: "original.authority_replay_contract(recovery_source runtime)"
    and connected: "recovery_connected runtime"
    and recovered: "original.checked_current_replay(recovery_source runtime)candidate=Some restored"
  shows "call_completions(reduced.run_calls actions(normalize_call_machine(recovery_source
      (original.dispatch_from_recovered_replica call_id command
        (original.restore_current_replica candidate runtime)))))=
    call_completions(original.run_calls actions
      (original.dispatch_client_call call_id command(recovery_source runtime)))"
    "call_history(reduced.run_calls actions(normalize_call_machine(recovery_source
      (original.dispatch_from_recovered_replica call_id command
        (original.restore_current_replica candidate runtime)))))=
    call_history(original.run_calls actions
      (original.dispatch_client_call call_id command(recovery_source runtime)))"
  by (simp_all only: restored_runtime_transports_every_future_call_word[OF contract connected recovered]
      normalized_call_fields)

lemma original_call_word_append:
  "original.run_calls(first@second)machine=
    original.run_calls second(original.run_calls first machine)"
  by (induction first arbitrary:machine) simp_all

lemma reduced_call_word_append:
  "reduced.run_calls(first@second)machine=
    reduced.run_calls second(reduced.run_calls first machine)"
  by (induction first arbitrary:machine) simp_all

theorem ordered_call_composition_commutes_with_projection:
  "reduced.run_calls second
      (reduced.run_calls first(normalize_call_machine machine))=
    normalize_call_machine(original.run_calls(first@second)machine)"
  by (simp only: finite_call_projection original_call_word_append)

theorem recovered_ordered_blocks_transport_finite_completed_calls:
  assumes contract: "original.authority_replay_contract(recovery_source runtime)"
    and connected: "recovery_connected runtime"
    and partition: "concat blocks=call_authority_log(recovery_source runtime)"
  defines "candidate \<equiv> recovery_from_blocks(call_genesis(recovery_source runtime))blocks"
  shows "original.checked_current_replay(recovery_source runtime)candidate=
      Some(call_authority_state(recovery_source runtime)) \<and>
    call_completions(reduced.run_calls(first@second)(normalize_call_machine(recovery_source
      (original.dispatch_from_recovered_replica call_id command
        (original.restore_current_replica candidate runtime)))))=
    call_completions(original.run_calls second(original.run_calls first
      (original.dispatch_client_call call_id command(recovery_source runtime))))"
proof -
  have decoded: "original.checked_current_replay(recovery_source runtime)candidate=
      Some(call_authority_state(recovery_source runtime))"
    unfolding candidate_def
    by (rule original.a_complete_ordered_partition_recovers_the_actual_source[OF contract partition])
  have decisions:
    "call_completions(reduced.run_calls(first@second)(normalize_call_machine(recovery_source
      (original.dispatch_from_recovered_replica call_id command
        (original.restore_current_replica candidate runtime)))))=
    call_completions(original.run_calls second(original.run_calls first
      (original.dispatch_client_call call_id command(recovery_source runtime))))"
    using restored_runtime_preserves_all_future_completed_replies(1)[OF contract connected decoded,
      where actions="first@second" and call_id=call_id and command=command]
    by (simp only: original_call_word_append)
  show ?thesis using decoded decisions by blast
qed

text \<open>The decoder concatenates explicit ordered entry blocks. Its inputs
  contain structured HOL values, not a claimed byte encoding of arbitrary
  function-valued maps. An exact journal partition is an input-structure
  equality, and the existing current-source validator checks the decoded
  candidate. Internal replayability alone does not supply that equality.

  Recovery uses the original full-state replica comparison and the existing
  source machine. The continuation retains its invocation identifiers,
  authority results, complete authority log and earlier completed replies.
  No fresh authority machine is substituted after recovery. The projection
  is applied only after the actual restore-and-dispatch operation has used
  its original checks.\<close>

end

end

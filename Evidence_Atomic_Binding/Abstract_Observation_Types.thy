(* SPDX-License-Identifier: BSD-3-Clause *)
theory Abstract_Observation_Types
  imports Observed_Protocol_Link
begin

section \<open>Observation Information Beyond Transfer Quantities\<close>

record observation_target =
  target_transfer :: transfer_ledger
  target_regulatory :: global_state
  target_application :: "nat \<Rightarrow> nat"
  target_records :: "source_key \<Rightarrow> terminal_record option"
  target_published :: "source_key set"
  target_phase :: "source_key \<Rightarrow> reservation_phase option"
  target_owner :: "nat \<Rightarrow> source_key option"
  target_journal :: "reservation_event list"
  target_revision :: nat

definition observation_alpha :: "finality_core \<Rightarrow> observation_target" where
  "observation_alpha s=\<lparr>target_transfer=transfer_projection(core_parent s),
    target_regulatory=receiver_snapshot(core_regulatory s),
    target_application=asset_value(machine_state(core_parent s)),
    target_records=core_records s,target_published=core_published s,
    target_phase=phase_at(machine_state(core_parent s)),target_owner=asset_owner(machine_state(core_parent s)),
    target_journal=machine_journal(core_parent s),target_revision=core_epoch s\<rparr>"

fun abstract_query_value :: "application_query \<Rightarrow> observation_target \<Rightarrow> application_value" where
  "abstract_query_value(Source_Balance account)target=Units_Value(ledger_source(target_transfer target)account)"
| "abstract_query_value(Destination_Balance account)target=Units_Value(ledger_destination(target_transfer target)account)"
| "abstract_query_value(Root_Balance key account)target=Units_Value(ledger_funding(target_transfer target)(key,account))"
| "abstract_query_value(Application_Value asset)target=Units_Value(target_application target asset)"
| "abstract_query_value(Regulatory_State domain asset)target=Regulatory_Value(get_reg_state(target_regulatory target)domain asset)"
| "abstract_query_value(Terminal_Receipt key)target=Receipt_Value(target_records target key)"

definition abstract_query_ready :: "application_query \<Rightarrow> observation_target \<Rightarrow> bool" where
  "abstract_query_ready query target \<longleftrightarrow>
    (\<forall>b\<in>set(ledger_debits(target_transfer target)).
      query_touches_binding query b \<longrightarrow> binding_key b\<in>target_published target) \<and>
    (\<forall>key entry. target_records target key=Some entry \<longrightarrow>
      query_touches_binding query(terminal_binding entry) \<longrightarrow> key\<in>target_published target) \<and>
    (case query of Application_Value asset \<Rightarrow> target_owner target asset=None | _ \<Rightarrow> True)"

definition snapshot_correspondence :: "endpoint_snapshot \<Rightarrow> observation_target \<Rightarrow> bool" where
  "snapshot_correspondence cache target \<longleftrightarrow>
    source_units(snapshot_financial cache)=ledger_source(target_transfer target) \<and>
    destination_units(snapshot_financial cache)=ledger_destination(target_transfer target) \<and>
    funded_units(snapshot_financial cache)=ledger_funding(target_transfer target) \<and>
    source_effects(snapshot_financial cache)=ledger_debits(target_transfer target) \<and>
    asset_value(snapshot_financial cache)=target_application target \<and>
    asset_owner(snapshot_financial cache)=target_owner target \<and>
    snapshot_regulatory cache=target_regulatory target \<and>
    snapshot_records cache=target_records target \<and>
    snapshot_published cache=target_published target \<and>
    snapshot_revision cache=target_revision target"

lemma captured_state_supplies_snapshot_correspondence:
  "snapshot_correspondence(capture_snapshot s)(observation_alpha s)"
  by (simp add: snapshot_correspondence_def capture_snapshot_def observation_alpha_def transfer_projection_def)

theorem independent_stored_and_abstract_query_readers_agree:
  assumes "snapshot_correspondence cache target"
  shows "stored_query query cache=abstract_query_value query target"
  using assms by (cases query) (auto simp: snapshot_correspondence_def)

theorem snapshot_readiness_matches_abstract_readiness:
  assumes "snapshot_correspondence cache target"
  shows "snapshot_query_ready query cache=abstract_query_ready query target"
  using assms by (cases query)
    (simp_all add: snapshot_correspondence_def snapshot_query_ready_def abstract_query_ready_def)

lemma observation_target_retains_the_independent_product:
  "(target_transfer(observation_alpha s),target_regulatory(observation_alpha s))=finality_alpha s"
  by (simp add: observation_alpha_def finality_alpha_def)

context source_attestation
begin

theorem public_current_response_preserves_all_its_observation_fields:
  assumes "snd(execute_observed(Read_Current endpoint query)s)=Current_Value revision value"
  shows "value=abstract_query_value query(observation_alpha(observed_core s)) \<and>
    revision=target_revision(observation_alpha(observed_core s)) \<and>
    abstract_query_ready query(observation_alpha(observed_core s))"
proof -
  have source: "value=stored_query query(capture_snapshot(observed_core s))"
    and revision: "revision=core_epoch(observed_core s)"
    and ready: "snapshot_query_ready query(capture_snapshot(observed_core s))"
    using successful_current_reply_has_actual_authority_state[OF assms] by blast+
  show ?thesis using source revision ready
    independent_stored_and_abstract_query_readers_agree[OF captured_state_supplies_snapshot_correspondence]
    snapshot_readiness_matches_abstract_readiness[OF captured_state_supplies_snapshot_correspondence]
    by (simp add: observation_alpha_def)
qed

theorem protected_current_response_preserves_its_independent_value:
  assumes "snd(execute_observed(Read_Protected_Current endpoint index r query)s)=Current_Value revision value"
  shows "value=abstract_query_value query(observation_alpha(observed_core s)) \<and>
    revision=target_revision(observation_alpha(observed_core s)) \<and>
    protected_read_access endpoint index r query s"
proof -
  have source: "value=stored_query query(capture_snapshot(observed_core s))"
    and revision: "revision=core_epoch(observed_core s)"
    and access: "protected_read_access endpoint index r query s"
    using protected_current_response_has_revision[of endpoint index r query s revision "value"] assms by auto
  show ?thesis using source revision access
    independent_stored_and_abstract_query_readers_agree[OF captured_state_supplies_snapshot_correspondence]
    by (simp add: observation_alpha_def)
qed

theorem raw_response_preserves_its_exact_intermediate_value:
  "snd(execute_observed(Read_Raw query)s)=
    Raw_Value(abstract_query_value query(observation_alpha(observed_core s)))"
  using independent_stored_and_abstract_query_readers_agree[OF captured_state_supplies_snapshot_correspondence]
  by simp

theorem operational_and_journal_observations_keep_their_separate_meanings:
  "snd(execute_observed(Read_Operation endpoint key)s)=
    Operation_Status(target_phase(observation_alpha(observed_core s))key)(secondary_progress s endpoint)"
  "snd(execute_observed Read_Raw_Journal s)=Journal_Events(target_journal(observation_alpha(observed_core s)))"
  by (simp_all add: observation_alpha_def)

end

text \<open>The quantity-and-regulation product is retained. Application
  values, terminal receipts, lifecycle status and raw journal observations
  require additional information. The concrete reader continues to read a
  stored endpoint snapshot; the abstract reader uses separate ledger and
  application fields. Snapshot correspondence is proved from the captured
  authoritative state and then used to relate those readers. It is not a
  definition of concrete observation as observation of an abstraction.
  This file concerns instantaneous observations. Historical source cuts,
  rejection conditions and durable invocation/completion records require
  their corresponding response and history relations.\<close>

end

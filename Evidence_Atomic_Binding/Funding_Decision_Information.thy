(* SPDX-License-Identifier: BSD-3-Clause *)
theory Funding_Decision_Information
  imports Root_Information
begin

section \<open>Funding Observed by the Actual Descendant Consumer\<close>

definition funding_probe_metadata :: "transfer_binding \<Rightarrow> global_state" where
  "funding_probe_metadata root=
    \<lparr>gs_chains=(\<lambda>domain asset.
      if domain=binding_destination root \<and> asset=binding_asset root
      then Some \<lparr>as_reg_state=ACTIVE\<rparr> else None),
      gs_locks=(\<lambda>_.False)\<rparr>"

definition funding_probe_request :: "source_certificate \<Rightarrow> transfer_binding \<Rightarrow>
  nat \<Rightarrow> nat \<Rightarrow> execution_request" where
  "funding_probe_request certificate root recipient amount=
    \<lparr>request_binding=descendant_binding root recipient amount Ordinary_Transfer_Effect,
      request_certificate=certificate,request_caller=0,
      request_authority_epoch=0,request_version=0\<rparr>"

definition funding_probe_context :: "transfer_binding \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
  \<Rightarrow> lock_context" where
  "funding_probe_context root sender recipient amount=
    \<lparr>lock_authority=
      \<lparr>context_endpoint=binding_destination root,context_relay_epoch=0,
        context_authority_epoch=0,context_version=0,
        context_permissions={(0,descendant_binding root recipient amount Ordinary_Transfer_Effect)},
        context_readers={0}\<rparr>,
      lock_metadata=funding_probe_metadata root,lock_restrictions=(\<lambda>_.True),
      lock_dependencies=(\<lambda>_.[]),lock_write_permissions={},
      lock_spend_permissions={(0,binding_key root,sender,recipient,amount,Ordinary_Transfer_Effect)}\<rparr>"

lemma funding_probe_metadata_valid:
  "valid_state(funding_probe_metadata root)"
  by (auto simp: valid_state_def consistent_state_def no_locked_without_reason_def
      funding_probe_metadata_def get_reg_state_def get_asset_state_def is_locked_def
      split: if_splits)

lemma funding_probe_uses_actual_current_authorization:
  "current_use_allowed(lock_authority(funding_probe_context root sender recipient amount))
    (funding_probe_request certificate root recipient amount)"
  "metadata_permission(funding_probe_context root sender recipient amount)
    (funding_probe_request certificate root recipient amount)(binding_destination root)"
  "context_endpoint(lock_authority(funding_probe_context root sender recipient amount))=
    binding_destination root"
  "valid_state(lock_metadata(funding_probe_context root sender recipient amount))"
  by (simp_all add: funding_probe_context_def funding_probe_request_def current_use_allowed_def
      metadata_permission_def funding_probe_metadata_def get_reg_state_def get_asset_state_def
      descendant_binding_def ordinary_transfer_allowed_def
      funding_probe_metadata_valid valid_state_def consistent_state_def no_locked_without_reason_def
      is_locked_def)

lemma actual_probe_reply_is_the_funding_threshold:
  assumes financial: "financial_history_agreement balances machine"
    and credited: "root\<in>set(credit_history(received_messages(machine_state machine)))"
  shows "snd(execute_descendant(funding_probe_context root sender recipient amount)
      (funding_probe_request certificate root recipient amount)root sender recipient amount machine)=
    (if 0<amount \<and>
       amount\<le>funded_units(machine_state machine)(binding_key root,holder_account root sender)
     then Descendant_Executed else Request_Rejected)"
proof -
  note actual = actual_descendant_reply_ignores_redundant_pooled_bound
    [OF financial, where c="funding_probe_context root sender recipient amount"
      and r="funding_probe_request certificate root recipient amount" and root=root
      and sender=sender and recipient=recipient and amount=amount]
  show ?thesis
    using actual credited
    by (simp add: funding_probe_context_def funding_probe_request_def
        funding_probe_metadata_def current_use_allowed_def metadata_permission_def
        get_reg_state_def get_asset_state_def descendant_binding_def ordinary_transfer_allowed_def)
qed

theorem equal_holder_funding_preserves_every_actual_reply:
  assumes first: "financial_history_agreement balances first_machine"
    and second: "financial_history_agreement balances second_machine"
    and first_credit: "root\<in>set(credit_history(received_messages(machine_state first_machine)))"
    and second_credit: "root\<in>set(credit_history(received_messages(machine_state second_machine)))"
    and funding: "\<forall>holder.
      funded_units(machine_state first_machine)(binding_key root,holder_account root holder)=
      funded_units(machine_state second_machine)(binding_key root,holder_account root holder)"
  shows "snd(execute_descendant context request root sender recipient amount first_machine)=
    snd(execute_descendant context request root sender recipient amount second_machine)"
proof -
  have at_sender:
    "funded_units(machine_state first_machine)(binding_key root,holder_account root sender)=
      funded_units(machine_state second_machine)(binding_key root,holder_account root sender)"
    using funding by blast
  show ?thesis
    by (simp only: actual_descendant_reply_ignores_redundant_pooled_bound[OF first]
        actual_descendant_reply_ignores_redundant_pooled_bound[OF second]
        first_credit second_credit at_sender)
qed

lemma minimum_successor_separates_distinct_funding:
  fixes first second :: nat
  assumes "first\<noteq>second"
  shows "(Suc(min first second)\<le>first)\<noteq>(Suc(min first second)\<le>second)"
proof (cases "first\<le>second")
  case True
  have strict: "first<second" using True assms by arith
  show ?thesis using strict by (simp add: min_def)
next
  case False
  have strict: "second<first" using False by arith
  show ?thesis using strict by (simp add: min_def)
qed

theorem distinct_holder_funding_has_an_actual_current_probe:
  fixes certificate :: source_certificate
  assumes first: "financial_history_agreement balances first_machine"
    and second: "financial_history_agreement balances second_machine"
    and first_credit: "root\<in>set(credit_history(received_messages(machine_state first_machine)))"
    and second_credit: "root\<in>set(credit_history(received_messages(machine_state second_machine)))"
    and different:
      "funded_units(machine_state first_machine)(binding_key root,holder_account root holder)\<noteq>
       funded_units(machine_state second_machine)(binding_key root,holder_account root holder)"
  defines "amount \<equiv> Suc(min
    (funded_units(machine_state first_machine)(binding_key root,holder_account root holder))
    (funded_units(machine_state second_machine)(binding_key root,holder_account root holder)))"
  shows "0<amount \<and>
    current_use_allowed(lock_authority(funding_probe_context root holder(Suc holder)amount))
      (funding_probe_request certificate root(Suc holder)amount) \<and>
    metadata_permission(funding_probe_context root holder(Suc holder)amount)
      (funding_probe_request certificate root(Suc holder)amount)(binding_destination root) \<and>
    snd(execute_descendant(funding_probe_context root holder(Suc holder)amount)
      (funding_probe_request certificate root(Suc holder)amount)root holder(Suc holder)amount first_machine)\<noteq>
    snd(execute_descendant(funding_probe_context root holder(Suc holder)amount)
      (funding_probe_request certificate root(Suc holder)amount)root holder(Suc holder)amount second_machine)"
proof -
  have cut:
    "(amount\<le>funded_units(machine_state first_machine)(binding_key root,holder_account root holder))\<noteq>
     (amount\<le>funded_units(machine_state second_machine)(binding_key root,holder_account root holder))"
    unfolding amount_def by (rule minimum_successor_separates_distinct_funding[OF different])
  have positive: "0<amount" by (simp add: amount_def)
  have replies:
    "snd(execute_descendant(funding_probe_context root holder(Suc holder)amount)
      (funding_probe_request certificate root(Suc holder)amount)root holder(Suc holder)amount first_machine)\<noteq>
     snd(execute_descendant(funding_probe_context root holder(Suc holder)amount)
      (funding_probe_request certificate root(Suc holder)amount)root holder(Suc holder)amount second_machine)"
    using cut positive
    by (simp only: actual_probe_reply_is_the_funding_threshold[OF first first_credit]
        actual_probe_reply_is_the_funding_threshold[OF second second_credit];
        auto split: if_splits)
  show ?thesis using positive replies funding_probe_uses_actual_current_authorization by blast
qed

theorem holder_funding_equality_iff_all_actual_descendant_decisions:
  assumes first: "financial_history_agreement balances first_machine"
    and second: "financial_history_agreement balances second_machine"
    and first_credit: "root\<in>set(credit_history(received_messages(machine_state first_machine)))"
    and second_credit: "root\<in>set(credit_history(received_messages(machine_state second_machine)))"
  shows "(\<forall>holder.
    funded_units(machine_state first_machine)(binding_key root,holder_account root holder)=
    funded_units(machine_state second_machine)(binding_key root,holder_account root holder)) \<longleftrightarrow>
    (\<forall>context request sender recipient amount.
      snd(execute_descendant context request root sender recipient amount first_machine)=
      snd(execute_descendant context request root sender recipient amount second_machine))"
proof
  assume funding: "\<forall>holder.
    funded_units(machine_state first_machine)(binding_key root,holder_account root holder)=
    funded_units(machine_state second_machine)(binding_key root,holder_account root holder)"
  show "\<forall>context request sender recipient amount.
    snd(execute_descendant context request root sender recipient amount first_machine)=
    snd(execute_descendant context request root sender recipient amount second_machine)"
    by (intro allI, rule equal_holder_funding_preserves_every_actual_reply
        [OF first second first_credit second_credit funding])
next
  assume decisions: "\<forall>context request sender recipient amount.
    snd(execute_descendant context request root sender recipient amount first_machine)=
    snd(execute_descendant context request root sender recipient amount second_machine)"
  show "\<forall>holder.
    funded_units(machine_state first_machine)(binding_key root,holder_account root holder)=
    funded_units(machine_state second_machine)(binding_key root,holder_account root holder)"
  proof (rule allI, rule ccontr)
    fix holder
    assume different:
      "funded_units(machine_state first_machine)(binding_key root,holder_account root holder)\<noteq>
       funded_units(machine_state second_machine)(binding_key root,holder_account root holder)"
    note probe = distinct_holder_funding_has_an_actual_current_probe
      [OF first second first_credit second_credit different, where certificate="sample_certificate 17"]
    show False using decisions probe by blast
  qed
qed

section \<open>A Restricted Policy Does Not Determine Funding\<close>

lemma empty_spend_permission_rejects_every_actual_descendant:
  "snd(execute_descendant(context\<lparr>lock_spend_permissions:={}\<rparr>)
    request root sender recipient amount machine)=Request_Rejected"
  by (simp add: execute_descendant_def record_observation_def Let_def)

lemma existing_lineage_pair_has_financial_history:
  "financial_history_agreement sample_balances(lineage_history 17)"
  "financial_history_agreement sample_balances(lineage_history 23)"
  using lineage_history_supplies_parent_contract[of 17]
    lineage_history_supplies_parent_contract[of 23]
  by (simp_all add: sample.reservation_contract_def)

lemma existing_lineage_pair_has_the_same_credited_root:
  "sample_binding 17\<in>set(credit_history(received_messages(machine_state(lineage_history 17))))"
  "sample_binding 17\<in>set(credit_history(received_messages(machine_state(lineage_history 23))))"
  by (simp_all add: lineage_trace_defs)

theorem empty_policy_hides_the_actual_two_root_funding_difference:
  "funded_units(machine_state(lineage_history 17))((0,17),(2,17,4))=5 \<and>
    funded_units(machine_state(lineage_history 23))((0,17),(2,17,4))=0 \<and>
    (\<forall>request sender recipient amount.
      snd(execute_descendant((sample_context ACTIVE)\<lparr>lock_spend_permissions:={}\<rparr>)
        request(sample_binding 17)sender recipient amount(lineage_history 17))=
      snd(execute_descendant((sample_context ACTIVE)\<lparr>lock_spend_permissions:={}\<rparr>)
        request(sample_binding 17)sender recipient amount(lineage_history 23)))"
  using witness_has_equal_pooled_balances_and_different_root_funding
  by (simp add: empty_spend_permission_rejects_every_actual_descendant)

theorem actual_probe_distinguishes_the_existing_lineage_pair:
  "snd(execute_descendant(funding_probe_context(sample_binding 17)4 3 1)
      (funding_probe_request(sample_certificate 17)(sample_binding 17)3 1)
      (sample_binding 17)4 3 1(lineage_history 17))=Descendant_Executed \<and>
    snd(execute_descendant(funding_probe_context(sample_binding 17)4 3 1)
      (funding_probe_request(sample_certificate 17)(sample_binding 17)3 1)
      (sample_binding 17)4 3 1(lineage_history 23))=Request_Rejected"
proof -
  have first_units: "funded_units(machine_state(lineage_history 17))
    (binding_key(sample_binding 17),holder_account(sample_binding 17)4)=5"
    and second_units: "funded_units(machine_state(lineage_history 23))
      (binding_key(sample_binding 17),holder_account(sample_binding 17)4)=0"
    using witness_has_equal_pooled_balances_and_different_root_funding
    by (simp_all add: sample_binding_def example_binding_def holder_account_def)
  note first_reply = actual_probe_reply_is_the_funding_threshold
    [OF existing_lineage_pair_has_financial_history(1) existing_lineage_pair_has_the_same_credited_root(1),
      where sender=4 and recipient=3 and amount=1 and certificate="sample_certificate 17"]
  note second_reply = actual_probe_reply_is_the_funding_threshold
    [OF existing_lineage_pair_has_financial_history(2) existing_lineage_pair_has_the_same_credited_root(2),
      where sender=4 and recipient=3 and amount=1 and certificate="sample_certificate 17"]
  show ?thesis using first_reply second_reply first_units second_units by simp
qed

text \<open>The equivalence quantifies over every common context, request and
  transfer quantity for this existing consumer. It does not infer funding
  from one fixed restrictive policy. The separating probe constructs a
  current singleton authorization, a current singleton spend permission and
  valid ACTIVE metadata, then calls the actual descendant operation.

  A descendant request's certificate field is not read by that operation:
  the root's existing credit and the current execution permissions are the
  relevant admission inputs. The probe therefore preserves an arbitrary
  typed certificate parameter without asserting new certificate authenticity.
  This result concerns decision replies for one credited root. It does not
  characterize whole-machine state, every operation family, physical source
  APIs or a globally minimal representation.\<close>

end

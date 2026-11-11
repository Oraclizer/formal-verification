theory Maintenance_Selection_Replay_Link
  imports "OIP_Ordered_Maintenance_G0_Core.Ordered_Maintenance_G0" "HOL-Library.Code_Target_Nat"
begin

text \<open>
  The ABI starts after exact source-byte extraction. Curve verification,
  the typed provider read and the stable no-op confirmation are explicit facts.
  The diagnostic omits only equality of signed and observed selection bindings.
\<close>

definition msr_dispatch_auth where
  "msr_dispatch_auth msr_policy msr_verify msr_token msr_request msr_signature \<longleftrightarrow>
    msr_token = Some (om_principal msr_request) \<and>
    om_profile msr_request = om_current_profile msr_policy \<and>
    cut_authority_epoch (om_cut msr_request) = om_current_epoch msr_policy \<and>
    (case om_role_key msr_policy (om_principal msr_request) Ordered_Queue_Key of None \<Rightarrow> False
     | Some msr_key \<Rightarrow> msr_verify msr_key msr_request msr_signature)"

lemma msr_dispatch_auth_matches_checked_authentication:
  assumes "om_action msr_request = Ordered_Dispatch msr_slot"
  shows "msr_dispatch_auth msr_policy msr_verify msr_token msr_request msr_signature =
    ordered_maintenance_authenticated msr_policy msr_verify msr_token msr_request msr_signature"
  using assms by (auto simp: msr_dispatch_auth_def ordered_maintenance_authenticated_def split: option.splits)

definition msr_common_gate where
  "msr_common_gate msr_policy msr_verify msr_token msr_request msr_signature
      msr_opened msr_current_head msr_cut msr_revoked \<longleftrightarrow>
    msr_dispatch_auth msr_policy msr_verify msr_token msr_request msr_signature \<and>
    om_principal msr_request \<in> om_local_maintainers msr_policy \<and>
    om_principal msr_request \<notin> msr_revoked \<and>
    msr_current_head = Some msr_opened \<and> om_cut msr_request = msr_cut"

lemma msr_selection_projection_is_the_checked_rule:
  assumes "om_action msr_request = Ordered_Dispatch msr_slot"
  shows "select_ordered_maintenance (\<lambda>_. msr_binding) msr_policy msr_verify msr_token msr_request
      msr_signature msr_opened msr_observed =
    (let msr_frame = witness_control msr_observed; msr_control = image_ordered_control msr_frame in
      if msr_common_gate msr_policy msr_verify msr_token msr_request msr_signature msr_opened
           (control_head msr_control) (reference_observed_cut (image_read_history msr_frame)) (control_revoked msr_control)
         \<and> om_selection msr_request = msr_binding then Some msr_observed else None)"
proof -
  have msr_auth_eq:
    "msr_dispatch_auth msr_policy msr_verify msr_token msr_request msr_signature =
     ordered_maintenance_authenticated msr_policy msr_verify msr_token msr_request msr_signature"
    by (rule msr_dispatch_auth_matches_checked_authentication[OF assms])
  show ?thesis
    by (simp only: select_ordered_maintenance_def ordered_maintenance_current_authority_def
      msr_common_gate_def Let_def msr_auth_eq)
qed

lemma msr_other_principal_revoke_keeps_current_authority:
  assumes "msr_other \<noteq> om_principal msr_request"
  shows "ordered_maintenance_current_authority msr_policy msr_verify msr_token msr_request msr_signature msr_opened
     (msr_observed\<lparr>witness_control := (witness_control msr_observed)\<lparr>image_ordered_control :=
       reference_order_revoke msr_other (image_ordered_control (witness_control msr_observed))\<rparr>\<rparr>) =
    ordered_maintenance_current_authority msr_policy msr_verify msr_token msr_request msr_signature msr_opened msr_observed"
proof -
  have "om_principal msr_request \<noteq> msr_other" using assms by auto
  then show ?thesis
    by (simp add: ordered_maintenance_current_authority_def reference_order_revoke_def Let_def)
qed

definition msr_slot_none :: "secondary_status \<Rightarrow> nat \<Rightarrow> bool" where
  "msr_slot_none msr_state msr_attempts \<longleftrightarrow>
    msr_state = Secondary_Completed \<or> 2^64 - 1 \<le> msr_attempts"

lemma msr_slot_none_reuses_the_queue_step:
  "msr_slot_none (secondary_state msr_job) (secondary_attempts msr_job) =
    (snd (step_one_slot msr_verify_ack (Slot_Dispatch msr_slot) (Some msr_job)) = Settlement_Dispatched None)"
  by (simp add: msr_slot_none_def Let_def split: if_splits)

lemma msr_completed_dispatch_has_no_effect:
  assumes "om_action msr_request = Ordered_Dispatch msr_slot"
    "retained_secondary msr_records msr_slot = Some msr_job"
    "secondary_state msr_job = Secondary_Completed"
  shows "maintenance_dispatch_effect msr_verify_ack msr_request msr_records =
    Some (msr_records, Settlement_Dispatched None)"
proof -
  have msr_same_slot:
    "(retained_secondary msr_records)(msr_slot := Some msr_job) = retained_secondary msr_records"
    using assms(2) by (metis fun_upd_idem)
  show ?thesis using assms msr_same_slot
    by (simp add: maintenance_dispatch_effect_def step_settlement_slot_def Let_def)
qed

lemma msr_completed_dispatch_releases_only_after_unchanged_readback:
  assumes "om_action msr_request = Ordered_Dispatch msr_slot"
    "retained_secondary (ordered_maintenance_records msr_live) msr_slot = Some msr_job"
    "secondary_state msr_job = Secondary_Completed"
    "\<exists>msr_bound \<in> msr_archives. msr_archive_bound msr_bound msr_live"
  shows "consume_selected_dispatch msr_archive_bound msr_archives msr_archive True (Some msr_live)
     msr_verify_ack msr_request msr_live msr_new_head = (msr_live, Some (Settlement_Dispatched None))"
proof -
  have msr_effect:
    "maintenance_dispatch_effect msr_verify_ack msr_request (ordered_maintenance_records msr_live) =
      Some (ordered_maintenance_records msr_live, Settlement_Dispatched None)"
    by (rule msr_completed_dispatch_has_no_effect[OF assms(1,2,3)])
  have msr_readback:
    "witnessed_current msr_archive_bound msr_archives msr_live msr_live = Some (witness_control msr_live)"
    using assms(4) by (simp add: witnessed_current_def)
  show ?thesis
    by (simp add: consume_selected_dispatch_def publish_maintenance_dispatch_def msr_effect msr_readback)
qed

lemma msr_stale_binding_rejects_before_the_dispatch_effect:
  assumes "om_selection msr_request \<noteq> msr_selection_of msr_live"
  shows "consume_selected_dispatch msr_archive_bound msr_archives msr_archive msr_reauthenticated
    (select_ordered_maintenance msr_selection_of msr_policy msr_verify msr_token msr_request msr_signature
      msr_opened msr_live) msr_verify_ack msr_request msr_live msr_new_head = (msr_live, None)"
  using assms by (simp add: select_ordered_maintenance_def consume_selected_dispatch_def)

definition msr_noop_current where
  "msr_noop_current msr_archive_ok msr_stable msr_mod msr_gen (msr_raw::wire_bytes) \<longleftrightarrow>
    (let msr_observed = \<lparr>witness_version = msr_mod, witness_generation = msr_gen, witness_control = msr_raw\<rparr>
     in msr_stable \<and> witnessed_current (\<lambda>_ _. msr_archive_ok) {()} msr_observed msr_observed = Some msr_raw)"

lemma msr_noop_current_finite [code]:
  "msr_noop_current msr_archive_ok msr_stable msr_mod msr_gen msr_raw = (msr_stable \<and> msr_archive_ok)"
  by (simp add: msr_noop_current_def witnessed_current_def Let_def)

definition msr_bit :: "bool \<Rightarrow> nat" where
  "msr_bit msr_value = (if msr_value then 1 else 0)"

definition msr_coordinates where
  "msr_coordinates msr_request =
    (let msr_profile = om_profile msr_request; msr_cut = om_cut msr_request in
       [recovery_deployment msr_profile,recovery_format msr_profile,recovery_authority_profile msr_profile,
        om_principal msr_request,cut_authority_epoch msr_cut,cut_revision msr_cut] @
        (case om_action msr_request of Ordered_Dispatch ((msr_domain,msr_event),msr_position) \<Rightarrow>
           [1,msr_domain,msr_event,msr_position] | _ \<Rightarrow> []))"

definition msr_external_curve where
  "msr_external_curve msr_fact msr_expected_key msr_expected_request msr_expected_signature
      msr_key msr_request msr_signature \<longleftrightarrow>
    msr_fact \<and> msr_key = msr_expected_key \<and> msr_signature = msr_expected_signature \<and>
    msr_coordinates msr_request = msr_coordinates msr_expected_request \<and>
    om_selection msr_request = om_selection msr_expected_request"

definition msr_branch_rows where
  "msr_branch_rows msr_selected msr_slot_noop msr_reauthenticated msr_readback =
    (if msr_selected then [1,1,msr_bit (msr_slot_noop \<and> msr_reauthenticated \<and> msr_readback),msr_bit msr_slot_noop]
     else [0,0,0,1])"

fun msr_natural_abi :: "nat list list \<Rightarrow> nat list list option" where
  "msr_natural_abi [[msr_id,msr_actor,msr_token_actor,msr_queue_actor,msr_signed_epoch,msr_signed_revision,
      msr_config_epoch,msr_epoch,msr_revision,msr_domain,msr_event,msr_position,msr_status,msr_attempts,msr_target,
      msr_clock,msr_mod,msr_generation],
      [msr_sd,msr_sf,msr_sp,msr_cd,msr_cf,msr_cp],
      [msr_token_fact,msr_curve_fact,msr_read_ok,msr_archive_ok,msr_stable],
      msr_opened,msr_observed_head,msr_maintainers,msr_revoked,msr_signed_binding,msr_observed_binding,
      msr_queue_key,msr_signature,msr_selector_raw] =
    (if msr_status \<noteq> 2 \<or> \<not> list_all (\<lambda>msr_flag. msr_flag \<le> 1)
        [msr_token_fact,msr_curve_fact,msr_read_ok,msr_archive_ok,msr_stable] \<or>
        length msr_opened \<noteq> 38 \<or> length msr_observed_head \<noteq> 38 \<or>
        length msr_signed_binding \<noteq> 32 \<or> length msr_observed_binding \<noteq> 32 \<or>
        length msr_queue_key \<noteq> 32 \<or> length msr_signature \<noteq> 64 \<or> msr_selector_raw = [] \<or>
        \<not> list_all (\<lambda>msr_byte. msr_byte < 256)
          (msr_signed_binding @ msr_observed_binding @ msr_queue_key @ msr_signature @ msr_selector_raw)
     then None else
      let msr_signed_profile = \<lparr>recovery_deployment = msr_sd, recovery_format = msr_sf, recovery_authority_profile = msr_sp\<rparr>;
          msr_profile = \<lparr>recovery_deployment = msr_cd, recovery_format = msr_cf, recovery_authority_profile = msr_cp\<rparr>;
          msr_cut = \<lparr>cut_authority_epoch = msr_epoch, cut_revision = msr_revision\<rparr>;
          msr_request = \<lparr>om_profile = msr_signed_profile, om_principal = msr_actor,
            om_cut = \<lparr>cut_authority_epoch = msr_signed_epoch, cut_revision = msr_signed_revision\<rparr>,
            om_selection = msr_signed_binding, om_action = Ordered_Dispatch ((msr_domain,msr_event),msr_position)\<rparr>;
          msr_policy = \<lparr>om_current_profile = msr_profile, om_current_epoch = msr_config_epoch,
            om_local_maintainers = set msr_maintainers, om_role_key =
              (\<lambda>msr_who msr_role. if msr_who = msr_queue_actor \<and> msr_role = Ordered_Queue_Key then Some msr_queue_key else None),
            om_trusted_now = Some msr_clock\<rparr>;
          msr_token = (if msr_token_fact = 1 then Some msr_token_actor else None);
          msr_verify = msr_external_curve (msr_curve_fact = 1) msr_queue_key msr_request msr_signature;
          msr_auth = msr_dispatch_auth msr_policy msr_verify msr_token msr_request msr_signature;
          msr_common = msr_common_gate msr_policy msr_verify msr_token msr_request msr_signature
            msr_opened (Some msr_observed_head) msr_cut (set msr_revoked);
          msr_binding_equal = (msr_signed_binding = msr_observed_binding);
          msr_base = (msr_common \<and> msr_read_ok = 1);
          msr_noop = msr_slot_none Secondary_Completed msr_attempts;
          msr_readback = msr_noop_current (msr_archive_ok = 1) (msr_stable = 1) msr_mod msr_generation msr_selector_raw
      in Some [[msr_id,msr_mod,msr_generation,msr_epoch,msr_revision,msr_attempts,msr_target],
          [msr_bit msr_auth, msr_bit (msr_actor \<in> set msr_maintainers), msr_bit (msr_actor \<notin> set msr_revoked),
           msr_bit (msr_opened = msr_observed_head), msr_bit (om_cut msr_request = msr_cut), msr_read_ok, msr_bit msr_binding_equal],
          msr_branch_rows (msr_base \<and> msr_binding_equal) msr_noop msr_auth msr_readback,
          msr_branch_rows msr_base msr_noop msr_auth msr_readback,
          msr_signed_binding,msr_observed_binding])"
| "msr_natural_abi _ = None"

definition msr_integer_abi :: "integer list list \<Rightarrow> integer list list option" where
  "msr_integer_abi msr_input =
    (if list_all (list_all (\<lambda>msr_number. 0 \<le> msr_number \<and> msr_number < 18446744073709551616)) msr_input
     then map_option (map (map integer_of_nat)) (msr_natural_abi (map (map nat_of_integer) msr_input)) else None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms msr_dispatch_auth_matches_checked_authentication
      msr_selection_projection_is_the_checked_rule msr_other_principal_revoke_keeps_current_authority
      msr_slot_none_reuses_the_queue_step msr_completed_dispatch_has_no_effect
      msr_completed_dispatch_releases_only_after_unchanged_readback msr_stale_binding_rejects_before_the_dispatch_effect
      msr_noop_current_finite})
  then () else error "Unexpected oracle in maintenance selection replay projection"
\<close>

export_code msr_integer_abi in SML
  module_name OIP_Maintenance_Selection_Replay file_prefix "oip_maintenance_selection_replay"

end

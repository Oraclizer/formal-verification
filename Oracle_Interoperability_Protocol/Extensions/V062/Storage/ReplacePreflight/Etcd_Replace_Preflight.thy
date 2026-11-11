theory Etcd_Replace_Preflight
  imports "OIP_Etcd_Control_Confirmation.Etcd_Control_Confirmation"
begin

section \<open>Control replacement preflight and the comparison boundary\<close>

text \<open>
  Each optional byte list represents stdout accepted by the corresponding
  client command boundary. A missing command result is distinct from a present
  malformed response. The observation does not execute a client command or
  decide the store effect of an unconfirmed transaction. The store's atomic
  MOD and value comparison is a separate boundary.
\<close>

datatype ep_outcome =
  EP_Invalid_Arguments | EP_Preflight_Error | EP_Txn_Command_Error |
  EP_Txn_Reply_Error | EP_Compare_Failed | EP_Readback_Error | EP_Confirmed nat

definition ep_request_valid :: "nat \<Rightarrow> nat \<times> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "ep_request_valid cap expected candidate \<longleftrightarrow>
    0 < fst expected \<and> fst expected < 2^63 \<and>
    length (snd expected) \<le> cap \<and> length candidate \<le> cap"

definition ep_preflight_ok where
  "ep_preflight_ok cluster key cap preflight \<longleftrightarrow>
    Option.bind preflight (ec_range_control cluster key cap) \<noteq> None"

definition ep_postflight where
  "ep_postflight cluster key cap expected candidate txn readback =
    (case txn of None \<Rightarrow> EP_Txn_Command_Error | Some raw_txn \<Rightarrow>
      (case ec_txn_revision cluster expected raw_txn of
        None \<Rightarrow> EP_Txn_Reply_Error | Some None \<Rightarrow> EP_Compare_Failed
      | Some (Some revision) \<Rightarrow>
          (case readback of None \<Rightarrow> EP_Readback_Error | Some raw_readback \<Rightarrow>
            if ec_confirm_write True cluster expected key cap candidate raw_txn raw_readback = Some (Some revision)
            then EP_Confirmed revision else EP_Readback_Error)))"

definition ep_replace where
  "ep_replace check_preflight cluster key cap expected candidate preflight txn readback =
    (if \<not> ep_request_valid cap expected candidate then EP_Invalid_Arguments
     else if check_preflight \<and> \<not> ep_preflight_ok cluster key cap preflight then EP_Preflight_Error
     else ep_postflight cluster key cap (fst expected) candidate txn readback)"

fun ep_return where
  "ep_return (EP_Confirmed revision) = Some (Some revision)"
| "ep_return EP_Compare_Failed = Some None"
| "ep_return _ = None"

definition ep_server_compare :: "nat \<times> nat list \<Rightarrow> (nat \<times> nat list) option \<Rightarrow> bool" where
  "ep_server_compare expected at_compare \<longleftrightarrow> at_compare = Some expected"

lemma ep_rejects_invalid_arguments_first:
  assumes "\<not> ep_request_valid cap expected candidate"
  shows "ep_replace check cluster key cap expected candidate preflight txn readback = EP_Invalid_Arguments"
  using assms by (simp add: ep_replace_def)

lemma ep_read_validity_precedes_any_transaction_response:
  assumes "ep_request_valid cap expected candidate"
    "\<not> ep_preflight_ok cluster key cap preflight"
  shows "ep_replace True cluster key cap expected candidate preflight txn readback = EP_Preflight_Error"
  using assms by (simp add: ep_replace_def)

lemma ep_valid_read_does_not_require_expected_value_or_revision:
  assumes "ep_request_valid cap expected candidate"
    "ec_range_control cluster key cap raw_read = Some seen" "seen \<noteq> expected"
  shows "ep_replace True cluster key cap expected candidate (Some raw_read) txn readback =
    ep_postflight cluster key cap (fst expected) candidate txn readback"
    "\<not> ep_server_compare expected (Some seen)"
  using assms by (simp_all add: ep_replace_def ep_preflight_ok_def ep_server_compare_def)

lemma ep_definite_compare_failure_does_not_consume_readback:
  assumes "ep_request_valid cap expected candidate"
    "ep_preflight_ok cluster key cap preflight"
    "ec_txn_revision cluster (fst expected) raw_txn = Some None"
  shows "ep_replace True cluster key cap expected candidate preflight (Some raw_txn) readback = EP_Compare_Failed"
  using assms by (simp add: ep_replace_def ep_postflight_def)

lemma ep_removing_only_preflight_can_expose_a_definite_compare_failure:
  assumes "ep_request_valid cap expected candidate"
    "\<not> ep_preflight_ok cluster key cap preflight"
    "ec_txn_revision cluster (fst expected) raw_txn = Some None"
  shows "ep_replace True cluster key cap expected candidate preflight (Some raw_txn) readback = EP_Preflight_Error"
    "ep_replace False cluster key cap expected candidate preflight (Some raw_txn) readback = EP_Compare_Failed"
  using assms by (simp_all add: ep_replace_def ep_postflight_def)

lemma ep_removing_only_preflight_can_expose_an_unconfirmed_transaction:
  assumes "ep_request_valid cap expected candidate"
    "\<not> ep_preflight_ok cluster key cap preflight"
    "ec_txn_revision cluster (fst expected) raw_txn = None"
  shows "ep_replace True cluster key cap expected candidate preflight (Some raw_txn) readback = EP_Preflight_Error"
    "ep_replace False cluster key cap expected candidate preflight (Some raw_txn) readback = EP_Txn_Reply_Error"
  using assms by (simp_all add: ep_replace_def ep_postflight_def)

lemma ep_postflight_retains_existing_projection:
  "ep_return (ep_postflight cluster key cap expected candidate (Some raw_txn) (Some raw_readback)) =
    ec_confirm_write True cluster expected key cap candidate raw_txn raw_readback"
  by (auto simp: ep_postflight_def ec_confirm_write_def split: option.splits prod.splits if_splits)

lemma ep_confirmed_retains_exact_selected_revision_and_bytes:
  assumes confirmed:
    "ep_postflight cluster key cap expected candidate (Some raw_txn) (Some raw_readback) = EP_Confirmed revision"
  shows "ec_txn_revision cluster expected raw_txn = Some (Some revision)"
    "ec_range_control cluster key cap raw_readback = Some (revision,candidate)"
proof -
  from ep_postflight_retains_existing_projection[of cluster key cap expected candidate raw_txn raw_readback]
    confirmed have exact:
    "ec_confirm_write True cluster expected key cap candidate raw_txn raw_readback = Some (Some revision)"
    by simp
  from ec_success_requires_exact_selected_revision_and_bytes[OF exact]
  show "ec_txn_revision cluster expected raw_txn = Some (Some revision)"
    "ec_range_control cluster key cap raw_readback = Some (revision,candidate)"
    by simp_all
qed

fun ep_words where
  "ep_words EP_Invalid_Arguments = [0]"
| "ep_words EP_Preflight_Error = [1]"
| "ep_words EP_Txn_Command_Error = [2]"
| "ep_words EP_Txn_Reply_Error = [3]"
| "ep_words EP_Compare_Failed = [4]"
| "ep_words EP_Readback_Error = [5]"
| "ep_words (EP_Confirmed revision) = [6,revision]"

definition ep_wire_option where
  "ep_wire_option present bytes = (if present = (0::integer) then None else Some (map nat_of_integer bytes))"

definition ep_observe :: "bool \<Rightarrow> integer list \<Rightarrow> integer list list \<Rightarrow> integer list" where
  "ep_observe check header blobs =
    (case (header,blobs) of
      ([cluster,cap,expected_rev,has_read,has_txn,has_readback],
       [key,expected_bytes,candidate,raw_read,raw_txn,raw_readback]) \<Rightarrow>
        if list_all (\<lambda>n. 0 \<le> n) header \<and>
           list_all (\<lambda>n. 0 \<le> n \<and> n < 256) (concat blobs) \<and>
           has_read \<le> 1 \<and> has_txn \<le> 1 \<and> has_readback \<le> 1 \<and>
           (has_read = 0 \<longrightarrow> raw_read = []) \<and>
           (has_txn = 0 \<longrightarrow> raw_txn = []) \<and>
           (has_readback = 0 \<longrightarrow> raw_readback = [])
        then map integer_of_nat (ep_words
          (ep_replace check (nat_of_integer cluster) (map nat_of_integer key) (nat_of_integer cap)
            (nat_of_integer expected_rev,map nat_of_integer expected_bytes) (map nat_of_integer candidate)
            (ep_wire_option has_read raw_read) (ep_wire_option has_txn raw_txn)
            (ep_wire_option has_readback raw_readback)))
        else []
    | _ \<Rightarrow> [])"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ep_rejects_invalid_arguments_first
    ep_read_validity_precedes_any_transaction_response ep_valid_read_does_not_require_expected_value_or_revision
    ep_definite_compare_failure_does_not_consume_readback
    ep_removing_only_preflight_can_expose_a_definite_compare_failure
    ep_removing_only_preflight_can_expose_an_unconfirmed_transaction
    ep_postflight_retains_existing_projection ep_confirmed_retains_exact_selected_revision_and_bytes}) then ()
  else error "Unexpected oracle in control replacement preflight"
\<close>

export_code ep_observe in SML module_name OIP_Etcd_Replace_Preflight file_prefix "oip_etcd_replace_preflight"

end

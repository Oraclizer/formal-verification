theory Negotiation_Authenticated_Model
  imports "OIP_V062_Negotiation_Core.Negotiation_List_Model"
begin

text \<open>Draft of the exact signing-input construction and field guards.
The verifier is an explicit parameter. This theory does not prove Ed25519,
key registration, or the host's challenge-generation discipline.\<close>

type_synonym n_bytes = "nat list"

fun n_be_width :: "nat \<Rightarrow> nat \<Rightarrow> n_bytes" where
  "n_be_width 0 number = []"
| "n_be_width (Suc width) number = n_be_width width (number div 256) @ [number mod 256]"

definition n_words :: "nat list \<Rightarrow> n_bytes" where
  "n_words items = concat (map (n_be_width 8) items)"

definition n_counted :: "nat list \<Rightarrow> n_bytes" where
  "n_counted items = n_be_width 8 (length items) @ n_words items"

definition n_offer_domain :: n_bytes where
  "n_offer_domain = [79,73,80,0,72,69,65,82,84,66,69,65,84,45,79,70,70,69,82,0]"

definition n_confirmation_domain :: n_bytes where
  "n_confirmation_domain = [79,73,80,0,72,69,65,82,84,66,69,65,84,45,80,82,79,70,73,76,69,0]"

definition n_offer_bytes :: "n_offer \<Rightarrow> n_bytes" where
  "n_offer_bytes offer = n_offer_domain @
    n_words [n_deployment offer, n_sender offer, n_receiver offer, n_challenge offer, n_expires offer] @
    n_counted (n_versions offer) @ n_counted (n_families offer) @
    n_counted (n_atomicities offer) @ n_counted (n_schemes offer)"

definition n_confirmation_bytes :: "n_offer \<Rightarrow> n_offer \<Rightarrow> n_profile \<Rightarrow> n_bytes" where
  "n_confirmation_bytes local remote profile = n_confirmation_domain @
    n_be_width 8 (length (n_offer_bytes local)) @ n_offer_bytes local @
    n_be_width 8 (length (n_offer_bytes remote)) @ n_offer_bytes remote @
    n_be_width 8 (n_version profile) @
    n_counted (n_profile_families profile) @ n_counted (n_profile_atomicities profile) @
    n_counted (n_profile_schemes profile)"

definition n_u64_offer :: "n_offer \<Rightarrow> bool" where
  "n_u64_offer offer \<longleftrightarrow>
    (\<forall>x \<in> set ([n_deployment offer, n_sender offer, n_receiver offer, n_challenge offer, n_expires offer] @
      n_versions offer @ n_families offer @ n_atomicities offer @ n_schemes offer). x < 2^64) \<and>
    (\<forall>xs \<in> {n_versions offer, n_families offer, n_atomicities offer, n_schemes offer}. length xs < 2^64)"

record n_context =
  nc_deployment :: nat
  nc_local :: nat
  nc_remote :: nat
  nc_challenge :: nat
  nc_now :: nat
  nc_floor :: nat
  nc_legacy :: bool
  nc_local_key :: n_bytes
  nc_remote_key :: n_bytes

record n_channel =
  nch_profile :: n_profile
  nch_deployment :: nat
  nch_local :: nat
  nch_remote :: nat
  nch_expires :: nat
  nch_challenge :: nat
  nch_local_key :: n_bytes
  nch_remote_key :: n_bytes

definition n_fields_match :: "n_context \<Rightarrow> n_offer \<Rightarrow> n_offer \<Rightarrow> bool" where
  "n_fields_match context local remote \<longleftrightarrow>
    n_deployment local = nc_deployment context \<and> n_deployment remote = nc_deployment context \<and>
    n_sender local = nc_local context \<and> n_receiver local = nc_remote context \<and>
    n_sender remote = nc_remote context \<and> n_receiver remote = nc_local context \<and>
    n_challenge local = nc_challenge context \<and> n_challenge remote = nc_challenge context \<and>
    nc_now context \<le> n_expires local \<and> nc_now context \<le> n_expires remote"

definition n_channel_from :: "n_context \<Rightarrow> n_offer \<Rightarrow> n_offer \<Rightarrow> n_profile \<Rightarrow> n_channel" where
  "n_channel_from context local remote profile = \<lparr>nch_profile = profile,
    nch_deployment = nc_deployment context, nch_local = nc_local context, nch_remote = nc_remote context,
    nch_expires = min (n_expires local) (n_expires remote), nch_challenge = nc_challenge context,
    nch_local_key = nc_local_key context, nch_remote_key = nc_remote_key context\<rparr>"

datatype n_auth_result = N_Source_Refusal | N_Signature_Refusal |
  N_Format_Refusal | N_Version_Refusal | N_Accepted n_channel

definition n_negotiate :: "(n_bytes \<Rightarrow> n_bytes \<Rightarrow> n_bytes \<Rightarrow> bool) \<Rightarrow>
    n_context \<Rightarrow> n_offer \<Rightarrow> n_offer \<Rightarrow> n_bytes \<Rightarrow> n_bytes \<Rightarrow> n_bytes \<Rightarrow> n_auth_result" where
  "n_negotiate verify context local remote local_signature remote_signature confirmation =
    (if \<not> n_fields_match context local remote then N_Source_Refusal
     else if \<not> (verify (nc_local_key context) (n_offer_bytes local) local_signature \<and>
       verify (nc_remote_key context) (n_offer_bytes remote) remote_signature) then N_Signature_Refusal
     else case n_select (nc_floor context) (nc_legacy context) local remote of
       N_Invalid_Format \<Rightarrow> N_Format_Refusal
     | N_Unsupported_Version \<Rightarrow> N_Version_Refusal
     | N_Selected profile \<Rightarrow>
       if verify (nc_remote_key context) (n_confirmation_bytes local remote profile) confirmation
       then N_Accepted (n_channel_from context local remote profile)
       else N_Signature_Refusal)"

lemma n_fixed_width_has_fixed_length [simp]:
  "length (n_be_width width number) = width"
  by (induction width arbitrary: number) simp_all

lemma n_words_have_counted_length [simp]:
  "length (n_words items) = 8 * length items"
  by (induction items) (simp_all add: n_words_def)

lemma n_counted_has_length [simp]:
  "length (n_counted items) = 8 + 8 * length items"
  by (simp add: n_counted_def)

lemma n_offer_bytes_have_exact_length:
  "length (n_offer_bytes offer) = 92 + 8 *
    (length (n_versions offer) + length (n_families offer) +
     length (n_atomicities offer) + length (n_schemes offer))"
  by (simp add: n_offer_bytes_def n_offer_domain_def algebra_simps)

lemma n_confirmation_bytes_have_exact_length:
  "length (n_confirmation_bytes local remote profile) =
    70 + length (n_offer_bytes local) + length (n_offer_bytes remote) +
    8 * (length (n_profile_families profile) + length (n_profile_atomicities profile) +
      length (n_profile_schemes profile))"
  by (simp add: n_confirmation_bytes_def n_confirmation_domain_def algebra_simps)

lemma n_admission_uses_exact_authoritative_signing_inputs:
  assumes "n_negotiate verify context local remote ls rs confirmation = N_Accepted channel"
  shows "n_fields_match context local remote"
    "verify (nc_local_key context) (n_offer_bytes local) ls"
    "verify (nc_remote_key context) (n_offer_bytes remote) rs"
    "n_select (nc_floor context) (nc_legacy context) local remote = N_Selected (nch_profile channel)"
    "verify (nc_remote_key context) (n_confirmation_bytes local remote (nch_profile channel)) confirmation"
  using assms
  by (auto simp: n_negotiate_def n_channel_from_def split: n_selection.splits if_splits)

lemma n_accepted_channel_records_exact_context_and_expiry:
  assumes "n_negotiate verify context local remote ls rs confirmation = N_Accepted channel"
  shows "nch_deployment channel = nc_deployment context"
    "nch_local channel = nc_local context" "nch_remote channel = nc_remote context"
    "nch_challenge channel = nc_challenge context"
    "nch_expires channel = min (n_expires local) (n_expires remote)"
    "nch_local_key channel = nc_local_key context" "nch_remote_key channel = nc_remote_key context"
  using assms
  by (auto simp: n_negotiate_def n_channel_from_def split: n_selection.splits if_splits)

lemma n_expired_or_wrong_challenge_is_rejected_before_verification:
  assumes "n_challenge local \<noteq> nc_challenge context \<or>
    n_challenge remote \<noteq> nc_challenge context \<or>
    n_expires local < nc_now context \<or> n_expires remote < nc_now context"
  shows "n_negotiate verify context local remote ls rs confirmation = N_Source_Refusal"
  using assms by (auto simp: n_negotiate_def n_fields_match_def)

lemma n_expiry_equal_to_now_is_still_fresh:
  fixes now remote_expiry :: nat
  shows "(now \<le> now \<and> now \<le> remote_expiry) = (now \<le> remote_expiry)"
  by simp

lemma n_accepted_channel_is_not_expired_at_selection:
  assumes "n_negotiate verify context local remote ls rs confirmation = N_Accepted channel"
  shows "nc_now context \<le> nch_expires channel"
  using n_admission_uses_exact_authoritative_signing_inputs(1)[OF assms]
    n_accepted_channel_records_exact_context_and_expiry(5)[OF assms]
  by (simp add: n_fields_match_def)

thm_oracles n_admission_uses_exact_authoritative_signing_inputs
  n_accepted_channel_records_exact_context_and_expiry
  n_expired_or_wrong_challenge_is_rejected_before_verification
  n_accepted_channel_is_not_expired_at_selection

ML \<open>
  if null (Thm_Deps.all_oracles @{thms n_fixed_width_has_fixed_length
      n_words_have_counted_length n_counted_has_length n_offer_bytes_have_exact_length
      n_confirmation_bytes_have_exact_length n_admission_uses_exact_authoritative_signing_inputs
      n_accepted_channel_records_exact_context_and_expiry
      n_expired_or_wrong_challenge_is_rejected_before_verification
      n_accepted_channel_is_not_expired_at_selection})
  then writeln "NEGOTIATION_AUTHENTICATION_ORACLES_EMPTY"
  else error "Negotiation authentication model unexpectedly depends on an oracle"
\<close>

end

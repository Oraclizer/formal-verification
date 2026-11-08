theory Wire_Code_Session_Authentication
  imports Wire_Code_Session_Claim_Bytes
begin

record code_source_session_peer =
  source_session_identity :: registered_identity
  source_session_serialized_grants :: "(nat \<times> wire_bytes) list"

record code_source_session_config =
  source_session_profile :: "nat \<times> nat \<times> nat"
  source_session_epoch :: nat
  source_session_issuer :: wire_bytes
  source_session_max_seconds :: nat
  source_session_peers :: "(nat \<times> code_source_session_peer) list"

definition code_source_session_time_current :: "nat option \<Rightarrow> nat \<Rightarrow> code_source_session_claim \<Rightarrow> bool" where
  "code_source_session_time_current now maximum claim =
    (case now of None \<Rightarrow> False | Some instant \<Rightarrow>
      token_claim_issued claim \<le> instant \<and> instant \<le> token_claim_expires claim \<and>
      token_claim_expires claim - token_claim_issued claim \<le> maximum)"

definition code_source_authenticate_session_bytes ::
  "code_source_session_config \<Rightarrow> (wire_bytes \<Rightarrow> wire_bytes) \<Rightarrow>
    (wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow> bool) \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes \<Rightarrow>
    session_proof \<Rightarrow> nat option \<Rightarrow> registered_identity option" where
  "code_source_authenticate_session_bytes session_config sha256 verify_curve preimage signature proof now =
    (case code_decode_session_claim_preimage preimage of None \<Rightarrow> None | Some claim \<Rightarrow>
      if token_claim_epoch claim \<noteq> proof_epoch proof \<or> token_claim_session claim \<noteq> proof_session proof then None
      else case map_of (source_session_peers session_config) (identity_principal (token_claim_identity claim)) of
        None \<Rightarrow> None | Some peer \<Rightarrow>
          (case map_of (source_session_serialized_grants peer) (token_claim_session claim) of
             None \<Rightarrow> None | Some grants_json \<Rightarrow>
               if token_claim_profile claim \<noteq> source_session_profile session_config \<or>
                  token_claim_epoch claim \<noteq> source_session_epoch session_config \<or>
                  token_claim_identity claim \<noteq> source_session_identity peer \<or>
                  token_claim_issuer claim \<noteq> source_session_issuer session_config \<or>
                  token_claim_grants_digest claim \<noteq> sha256 (code_session_grants_domain @ grants_json) \<or>
                  \<not> code_source_session_time_current now (source_session_max_seconds session_config) claim \<or>
                  \<not> verify_curve (source_session_issuer session_config) preimage signature
               then None else Some (token_claim_identity claim)))"

theorem source_session_authentication_keeps_the_current_record_grants_time_and_curve_inputs:
  assumes authenticated: "code_source_authenticate_session_bytes session_config sha256 verify_curve preimage signature proof now = Some identity"
  obtains claim :: code_source_session_claim and peer :: code_source_session_peer and grants_json :: wire_bytes
  where "code_decode_session_claim_preimage preimage = Some claim"
    "map_of (source_session_peers session_config) (identity_principal (token_claim_identity claim)) = Some peer"
    "map_of (source_session_serialized_grants peer) (token_claim_session claim) = Some grants_json"
    "identity = token_claim_identity claim" "identity = source_session_identity peer"
    "token_claim_epoch claim = proof_epoch proof" "token_claim_session claim = proof_session proof"
    "token_claim_profile claim = source_session_profile session_config"
    "token_claim_epoch claim = source_session_epoch session_config"
    "token_claim_issuer claim = source_session_issuer session_config"
    "token_claim_grants_digest claim = sha256 (code_session_grants_domain @ grants_json)"
    "code_source_session_time_current now (source_session_max_seconds session_config) claim"
    "verify_curve (source_session_issuer session_config) preimage signature"
proof -
  obtain claim
    where decoded: "code_decode_session_claim_preimage preimage = Some claim"
  proof (cases "code_decode_session_claim_preimage preimage")
    case None
    with authenticated show thesis by (simp add: code_source_authenticate_session_bytes_def)
  next
    case (Some claim)
    show thesis by (rule that[OF Some])
  qed
  have proof_matches: "token_claim_epoch claim = proof_epoch proof \<and> token_claim_session claim = proof_session proof"
  proof (rule ccontr)
    assume "\<not> (token_claim_epoch claim = proof_epoch proof \<and> token_claim_session claim = proof_session proof)"
    then have mismatch: "token_claim_epoch claim \<noteq> proof_epoch proof \<or> token_claim_session claim \<noteq> proof_session proof" by auto
    with authenticated decoded show False by (simp add: code_source_authenticate_session_bytes_def)
  qed
  have proof_epoch: "token_claim_epoch claim = proof_epoch proof"
    and proof_session: "token_claim_session claim = proof_session proof" using proof_matches by auto
  obtain peer
    where peer: "map_of (source_session_peers session_config) (identity_principal (token_claim_identity claim)) = Some peer"
  proof (cases "map_of (source_session_peers session_config) (identity_principal (token_claim_identity claim))")
    case None
    with authenticated decoded proof_matches show thesis by (simp add: code_source_authenticate_session_bytes_def)
  next
    case (Some peer)
    show thesis by (rule that[OF Some])
  qed
  obtain grants_json
    where grants: "map_of (source_session_serialized_grants peer) (token_claim_session claim) = Some grants_json"
  proof (cases "map_of (source_session_serialized_grants peer) (token_claim_session claim)")
    case None
    with authenticated decoded proof_matches peer show thesis by (simp add: code_source_authenticate_session_bytes_def)
  next
    case (Some grants_json)
    show thesis by (rule that[OF Some])
  qed
  have profile: "token_claim_profile claim = source_session_profile session_config"
    and epoch: "token_claim_epoch claim = source_session_epoch session_config"
    and selected_identity: "token_claim_identity claim = source_session_identity peer"
    and issuer: "token_claim_issuer claim = source_session_issuer session_config"
    and digest: "token_claim_grants_digest claim = sha256 (code_session_grants_domain @ grants_json)"
    and clock: "code_source_session_time_current now (source_session_max_seconds session_config) claim"
    and curve: "verify_curve (source_session_issuer session_config) preimage signature"
    using authenticated decoded proof_matches peer grants
    by (auto simp: code_source_authenticate_session_bytes_def split: if_splits)
  have observed: "code_source_authenticate_session_bytes session_config sha256 verify_curve preimage signature proof now =
      Some (token_claim_identity claim)"
    using decoded proof_epoch proof_session peer grants profile epoch selected_identity issuer digest clock curve
    by (simp add: code_source_authenticate_session_bytes_def)
  have identity: "identity = token_claim_identity claim" using authenticated observed by simp
  have current_identity: "identity = source_session_identity peer" using identity selected_identity by simp
  show thesis by (rule that[OF decoded peer grants identity current_identity proof_epoch proof_session profile epoch issuer digest clock curve])
qed

lemma session_authentication_cannot_use_another_session_from_the_same_principal:
  assumes decoded: "code_decode_session_claim_preimage preimage = Some claim"
    and session: "token_claim_session claim \<noteq> proof_session proof"
  shows "code_source_authenticate_session_bytes session_config sha256 verify_curve preimage signature proof now = None"
  using decoded session by (simp add: code_source_authenticate_session_bytes_def)

lemma the_session_clock_and_token_lifetime_are_explicit_checks:
  "code_source_session_time_current None maximum claim = False"
  "code_source_session_time_current (Some instant) maximum claim \<longleftrightarrow>
    token_claim_issued claim \<le> instant \<and> instant \<le> token_claim_expires claim \<and>
    token_claim_expires claim - token_claim_issued claim \<le> maximum"
  by (simp_all add: code_source_session_time_current_def)

lemma a_stale_config_epoch_cannot_authenticate_an_otherwise_signed_session:
  assumes decoded: "code_decode_session_claim_preimage preimage = Some claim"
    and epoch: "token_claim_epoch claim \<noteq> source_session_epoch session_config"
  shows "code_source_authenticate_session_bytes session_config sha256 verify_curve preimage signature proof now = None"
  using decoded epoch
  by (auto simp: code_source_authenticate_session_bytes_def split: option.splits if_splits)

text \<open>
  Source: Ed25519Security.authenticate_session/authenticate/session_claims/
  current_token. The claim is parsed from the exact bytes passed to the
  curve primitive, and the full current session-grants digest is recomputed
  from the same selected peer/session row. No whole authenticated=true
  callback replaces the profile/epoch/identity/session/issuer/grants/time
  checks. The raw trusted config row must be the actual current serialized
  full SessionGrants value, not an arbitrary preimage supplied by a caller.
  Its source producer/config-to-call-grants relation remains a reception
  obligation; these bytes are not asserted to be a newly proved serializer.
  SHA256 and strict Ed25519 are named mathematical primitives. Wire clock
  and financial ledger clock remain different values. The source current
  directory/session check follows separately in code_source_active_identity.
\<close>

end

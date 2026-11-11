theory Negotiation_Export
  imports "OIP_V062_Negotiation_Authentication.Negotiation_Authenticated_Model"
    "HOL-Library.Code_Target_Nat"
begin

text \<open>The ABI receives only authoritative input fields and signatures.
It has no expected profile, expected bytes, expected status, or case selector.
The verifier remains a function of the exact key/message/signature triple.\<close>

record n_abi_input =
  ni_context :: n_context
  ni_local :: n_offer
  ni_remote :: n_offer
  ni_local_signature :: n_bytes
  ni_remote_signature :: n_bytes
  ni_confirmation :: n_bytes

definition n_abi_u64 :: "integer \<Rightarrow> bool" where
  "n_abi_u64 word \<longleftrightarrow> 0 \<le> word \<and> word < 18446744073709551616"

definition n_abi_octet :: "integer \<Rightarrow> bool" where
  "n_abi_octet octet \<longleftrightarrow> 0 \<le> octet \<and> octet < 256"

fun n_decode_integer_input :: "integer list list \<Rightarrow> n_abi_input option" where
  "n_decode_integer_input
    [[deployment, local_peer, remote_peer, challenge, now, floor, legacy],
     [ld, ls, lr, lc, le], lv, lf, la, lsc,
     [rd, rs, rr, rc, re], rv, rf, ra, rsc,
     local_key, remote_key, local_signature, remote_signature, confirmation] =
    (if list_all n_abi_u64
       ([deployment, local_peer, remote_peer, challenge, now, floor, legacy,
         ld, ls, lr, lc, le, rd, rs, rr, rc, re] @ lv @ lf @ la @ lsc @ rv @ rf @ ra @ rsc) \<and>
        (legacy = 0 \<or> legacy = 1) \<and>
        length local_key = 32 \<and> length remote_key = 32 \<and>
        list_all (list_all n_abi_octet)
          [local_key, remote_key, local_signature, remote_signature, confirmation]
     then Some \<lparr>ni_context = \<lparr>nc_deployment = nat_of_integer deployment,
         nc_local = nat_of_integer local_peer, nc_remote = nat_of_integer remote_peer,
         nc_challenge = nat_of_integer challenge, nc_now = nat_of_integer now,
         nc_floor = nat_of_integer floor, nc_legacy = (legacy = 1),
         nc_local_key = map nat_of_integer local_key, nc_remote_key = map nat_of_integer remote_key\<rparr>,
       ni_local = \<lparr>n_deployment = nat_of_integer ld, n_sender = nat_of_integer ls,
         n_receiver = nat_of_integer lr, n_challenge = nat_of_integer lc, n_expires = nat_of_integer le,
         n_versions = map nat_of_integer lv, n_families = map nat_of_integer lf,
         n_atomicities = map nat_of_integer la, n_schemes = map nat_of_integer lsc\<rparr>,
       ni_remote = \<lparr>n_deployment = nat_of_integer rd, n_sender = nat_of_integer rs,
         n_receiver = nat_of_integer rr, n_challenge = nat_of_integer rc, n_expires = nat_of_integer re,
         n_versions = map nat_of_integer rv, n_families = map nat_of_integer rf,
         n_atomicities = map nat_of_integer ra, n_schemes = map nat_of_integer rsc\<rparr>,
       ni_local_signature = map nat_of_integer local_signature,
       ni_remote_signature = map nat_of_integer remote_signature,
       ni_confirmation = map nat_of_integer confirmation\<rparr>
     else None)"
| "n_decode_integer_input other = None"

definition n_abi_flag :: "bool \<Rightarrow> nat" where
  "n_abi_flag predicate = (if predicate then 1 else 0)"

definition n_profile_rows :: "n_profile \<Rightarrow> nat list list" where
  "n_profile_rows profile = [[n_version profile], n_profile_families profile,
    n_profile_atomicities profile, n_profile_schemes profile]"

fun n_selection_rows :: "n_selection \<Rightarrow> nat list list" where
  "n_selection_rows N_Invalid_Format = [[1], [], [], [], []]"
| "n_selection_rows N_Unsupported_Version = [[2], [], [], [], []]"
| "n_selection_rows (N_Selected profile) = [3] # n_profile_rows profile"

fun n_selected_confirmation :: "n_offer \<Rightarrow> n_offer \<Rightarrow> n_selection \<Rightarrow> n_bytes" where
  "n_selected_confirmation local remote (N_Selected profile) = n_confirmation_bytes local remote profile"
| "n_selected_confirmation local remote other = []"

fun n_auth_rows :: "n_auth_result \<Rightarrow> nat list list" where
  "n_auth_rows N_Source_Refusal = [[1], [], [], [], [], [], [], []]"
| "n_auth_rows N_Signature_Refusal = [[2], [], [], [], [], [], [], []]"
| "n_auth_rows N_Format_Refusal = [[3], [], [], [], [], [], [], []]"
| "n_auth_rows N_Version_Refusal = [[4], [], [], [], [], [], [], []]"
| "n_auth_rows (N_Accepted channel) =
    [[5], [nch_deployment channel, nch_local channel, nch_remote channel,
      nch_challenge channel, nch_expires channel]] @ n_profile_rows (nch_profile channel) @
      [nch_local_key channel, nch_remote_key channel]"

definition n_structural_rows :: "n_abi_input \<Rightarrow> nat list list" where
  "n_structural_rows input =
    (let context = ni_context input; local = ni_local input; remote = ni_remote input;
         selected = n_select (nc_floor context) (nc_legacy context) local remote
     in [[1, n_abi_flag (n_offer_canonical local), n_abi_flag (n_offer_canonical remote),
          n_abi_flag (n_fields_match context local remote)],
         n_offer_bytes local, n_offer_bytes remote] @ n_selection_rows selected @
         [n_selected_confirmation local remote selected])"

definition n_model_rows :: "(n_bytes \<Rightarrow> n_bytes \<Rightarrow> n_bytes \<Rightarrow> bool) \<Rightarrow>
    n_abi_input \<Rightarrow> nat list list" where
  "n_model_rows verify input = n_structural_rows input @
    n_auth_rows (n_negotiate verify (ni_context input) (ni_local input) (ni_remote input)
      (ni_local_signature input) (ni_remote_signature input) (ni_confirmation input))"

definition n_integer_primitive :: "(integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> bool) \<Rightarrow>
    n_bytes \<Rightarrow> n_bytes \<Rightarrow> n_bytes \<Rightarrow> bool" where
  "n_integer_primitive primitive key message signature =
    primitive (map integer_of_nat key) (map integer_of_nat message) (map integer_of_nat signature)"

definition n_probe_integer :: "integer list list \<Rightarrow> integer list list" where
  "n_probe_integer input_rows =
    (case n_decode_integer_input input_rows of None \<Rightarrow> [[0]]
     | Some input \<Rightarrow> map (map integer_of_nat) (n_structural_rows input))"

definition n_observe_integer :: "(integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> bool) \<Rightarrow>
    integer list list \<Rightarrow> integer list list" where
  "n_observe_integer primitive input_rows =
    (case n_decode_integer_input input_rows of None \<Rightarrow> [[0]]
     | Some input \<Rightarrow> map (map integer_of_nat) (n_model_rows (n_integer_primitive primitive) input))"

lemma n_selection_rows_have_fixed_shape [simp]:
  "length (n_selection_rows selected) = 5"
  by (cases selected) (simp_all add: n_profile_rows_def)

lemma n_authentication_rows_have_fixed_shape [simp]:
  "length (n_auth_rows res) = 8"
  by (cases res) (simp_all add: n_profile_rows_def)

lemma n_structural_rows_have_fixed_shape [simp]:
  "length (n_structural_rows input) = 9"
  by (simp add: n_structural_rows_def Let_def)

lemma n_model_rows_have_fixed_shape [simp]:
  "length (n_model_rows verify input) = 17"
  by (simp add: n_model_rows_def)

lemma n_probe_returns_exact_offer_bytes:
  "n_structural_rows input ! 1 = n_offer_bytes (ni_local input)"
  "n_structural_rows input ! 2 = n_offer_bytes (ni_remote input)"
  by (simp_all add: n_structural_rows_def Let_def)

lemma n_probe_builds_confirmation_from_actual_selection:
  assumes "n_select (nc_floor (ni_context input)) (nc_legacy (ni_context input))
    (ni_local input) (ni_remote input) = N_Selected profile"
  shows "n_structural_rows input ! 8 = n_confirmation_bytes (ni_local input) (ni_remote input) profile"
  using assms by (simp add: n_structural_rows_def n_profile_rows_def Let_def)

lemma n_model_result_suffix_is_the_actual_authentication_result:
  "drop 9 (n_model_rows verify input) =
    n_auth_rows (n_negotiate verify (ni_context input) (ni_local input) (ni_remote input)
      (ni_local_signature input) (ni_remote_signature input) (ni_confirmation input))"
  by (simp add: n_model_rows_def drop_append)

lemma n_integer_observer_uses_the_decoded_input:
  assumes "n_decode_integer_input input_rows = Some input"
  shows "n_observe_integer primitive input_rows =
    map (map integer_of_nat) (n_model_rows (n_integer_primitive primitive) input)"
  using assms by (simp add: n_observe_integer_def)

lemma n_invalid_abi_input_does_not_enter_negotiation:
  assumes "n_decode_integer_input input_rows = None"
  shows "n_probe_integer input_rows = [[0]]" "n_observe_integer primitive input_rows = [[0]]"
  using assms by (simp_all add: n_probe_integer_def n_observe_integer_def)

lemma n_primitive_receives_the_exact_three_byte_sequences:
  "n_integer_primitive primitive key message signature =
    primitive (map integer_of_nat key) (map integer_of_nat message) (map integer_of_nat signature)"
  by (simp add: n_integer_primitive_def)

thm_oracles n_probe_returns_exact_offer_bytes n_probe_builds_confirmation_from_actual_selection
  n_model_result_suffix_is_the_actual_authentication_result n_integer_observer_uses_the_decoded_input
  n_invalid_abi_input_does_not_enter_negotiation n_primitive_receives_the_exact_three_byte_sequences

ML \<open>
  if null (Thm_Deps.all_oracles @{thms n_probe_returns_exact_offer_bytes
      n_probe_builds_confirmation_from_actual_selection
      n_model_result_suffix_is_the_actual_authentication_result
      n_integer_observer_uses_the_decoded_input n_invalid_abi_input_does_not_enter_negotiation
      n_primitive_receives_the_exact_three_byte_sequences})
  then writeln "NEGOTIATION_EXPORT_ORACLES_EMPTY"
  else error "Negotiation export unexpectedly depends on an oracle"
\<close>

export_code n_probe_integer n_observe_integer
  in SML module_name OIP_Negotiation_ABI file_prefix "oip_negotiation_abi"

end

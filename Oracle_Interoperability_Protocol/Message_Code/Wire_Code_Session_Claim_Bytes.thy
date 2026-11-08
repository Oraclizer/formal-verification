theory Wire_Code_Session_Claim_Bytes
  imports Wire_Code_Source_Call_Signature Wire_Code_JSON_Contexts
begin

definition code_json_source_profile :: "wire_bytes \<Rightarrow> ((nat \<times> nat \<times> nat) \<times> wire_bytes) option" where
  "code_json_source_profile bytes =
    Option.bind (code_json_first_field ''deployment'' code_json_u64 bytes) (\<lambda>(deployment,r0).
      Option.bind (code_json_next_field ''format'' code_json_u64 r0) (\<lambda>(format,r1).
        Option.bind (code_json_next_field ''authority_profile'' code_json_u64 r1) (\<lambda>(authority,r2).
          if format \<ge> 2^32 then None else
          map_option (\<lambda>rest. ((deployment,format,authority),rest)) (code_json_expect [125] r2))))"

definition code_json_source_identity :: "wire_bytes \<Rightarrow> (registered_identity \<times> wire_bytes) option" where
  "code_json_source_identity bytes =
    Option.bind (code_json_first_field ''principal'' code_json_u64 bytes) (\<lambda>(caller_principal,r0).
      Option.bind (code_json_next_field ''domain'' code_json_u64 r0) (\<lambda>(domain,r1).
        Option.bind (code_json_next_field ''ocid'' code_json_u64 r1) (\<lambda>(ocid,r2).
          Option.bind (code_json_next_field ''rai'' code_json_u64 r2) (\<lambda>(rai,r3).
            map_option (\<lambda>rest. (\<lparr>identity_principal = caller_principal,identity_domain = domain,
              identity_ocid = ocid,identity_rai = rai\<rparr>,rest)) (code_json_expect [125] r3)))))"

definition code_json_octets32 :: "wire_bytes \<Rightarrow> (wire_bytes \<times> wire_bytes) option" where
  "code_json_octets32 bytes = Option.bind (code_json_array code_json_u64 bytes) (\<lambda>(octets,rest).
    if length octets = 32 \<and> list_all (\<lambda>octet. octet < 256) octets then Some (octets,rest) else None)"

record code_source_session_claim =
  token_claim_profile :: "nat \<times> nat \<times> nat"
  token_claim_epoch :: nat
  token_claim_identity :: registered_identity
  token_claim_session :: nat
  token_claim_issuer :: wire_bytes
  token_claim_grants_digest :: wire_bytes
  token_claim_issued :: nat
  token_claim_expires :: nat

definition code_json_session_claim :: "wire_bytes \<Rightarrow> (code_source_session_claim \<times> wire_bytes) option" where
  "code_json_session_claim bytes =
    Option.bind (code_json_first_field ''profile'' code_json_source_profile bytes) (\<lambda>(profile,r0).
      Option.bind (code_json_next_field ''epoch'' code_json_u64 r0) (\<lambda>(epoch,r1).
        Option.bind (code_json_next_field ''identity'' code_json_source_identity r1) (\<lambda>(identity,r2).
          Option.bind (code_json_next_field ''session'' code_json_u64 r2) (\<lambda>(session,r3).
            Option.bind (code_json_next_field ''issuer'' code_json_octets32 r3) (\<lambda>(issuer,r4).
              Option.bind (code_json_next_field ''grants_sha256'' code_json_octets32 r4) (\<lambda>(digest,r5).
                Option.bind (code_json_next_field ''issued_seconds'' code_json_u64 r5) (\<lambda>(issued,r6).
                  Option.bind (code_json_next_field ''expires_seconds'' code_json_u64 r6) (\<lambda>(expires,r7).
                    map_option (\<lambda>rest. (\<lparr>token_claim_profile = profile,token_claim_epoch = epoch,
                      token_claim_identity = identity,token_claim_session = session,token_claim_issuer = issuer,
                      token_claim_grants_digest = digest,token_claim_issued = issued,token_claim_expires = expires\<rparr>,rest))
                      (code_json_expect [125] r7)))))))))"

definition code_session_claim_domain :: wire_bytes where
  "code_session_claim_domain = code_json_ascii ''oip/reference-session/v1'' @ [0]"

definition code_session_grants_domain :: wire_bytes where
  "code_session_grants_domain = code_json_ascii ''oip/reference-session-grants/v1'' @ [0]"

definition code_decode_session_claim_preimage :: "wire_bytes \<Rightarrow> code_source_session_claim option" where
  "code_decode_session_claim_preimage bytes =
    Option.bind (code_json_expect code_session_claim_domain bytes) (code_json_complete code_json_session_claim)"

definition code_interpret_session_claim_bytes ::
  "wire_bytes \<Rightarrow> (registered_identity \<times> wire_bytes \<times> wire_bytes) option" where
  "code_interpret_session_claim_bytes bytes = map_option (\<lambda>claim.
    (token_claim_identity claim,token_claim_issuer claim,token_claim_grants_digest claim))
      (code_decode_session_claim_preimage bytes)"

lemma the_claim_byte_interpretation_preserves_identity_and_both_separate_crypto_byte_fields:
  assumes "code_decode_session_claim_preimage bytes = Some claim"
  shows "code_interpret_session_claim_bytes bytes =
    Some (token_claim_identity claim,token_claim_issuer claim,token_claim_grants_digest claim)"
  using assms by (simp add: code_interpret_session_claim_bytes_def)

lemma an_exact_json_prefix_is_the_original_prefix_and_remaining_bytes:
  assumes "code_json_expect token bytes = Some rest"
  shows "bytes = token @ rest"
proof -
  have prefix: "take (length token) bytes = token" and suffix: "drop (length token) bytes = rest"
    using assms by (auto simp: code_json_expect_def split: if_splits)
  have "bytes = take (length token) bytes @ drop (length token) bytes" by simp
  then show ?thesis by (simp only: prefix suffix)
qed

theorem a_decoded_session_signature_preimage_has_the_exact_domain_and_whole_claim:
  assumes decoded: "code_decode_session_claim_preimage bytes = Some claim"
  obtains json
  where "bytes = code_session_claim_domain @ json"
    "code_json_session_claim json = Some (claim,[])"
proof -
  obtain json
    where prefix: "code_json_expect code_session_claim_domain bytes = Some json"
      and complete: "code_json_complete code_json_session_claim json = Some claim"
    using decoded by (auto simp: code_decode_session_claim_preimage_def bind_eq_Some_conv)
  have bytes: "bytes = code_session_claim_domain @ json"
    by (rule an_exact_json_prefix_is_the_original_prefix_and_remaining_bytes[OF prefix])
  have parsed: "code_json_session_claim json = Some (claim,[])"
    using complete by (auto simp: code_json_complete_def split: option.splits prod.splits list.splits)
  show thesis by (rule that[OF bytes parsed])
qed

lemma a_source_digest_or_issuer_array_is_exactly_32_octets:
  assumes "code_json_octets32 bytes = Some (octets,rest)"
  shows "length octets = 32" "\<forall>octet \<in> set octets. octet < 256"
  using assms by (auto simp: code_json_octets32_def list_all_iff bind_eq_Some_conv split: if_splits)

text \<open>
  This parser follows the declared Rust RecoveryProfile/Identity/SessionClaims
  serde field order and fixed JSON spelling. It does not discard unknown
  properties, whitespace, suffix data or nonminimal decimal representations.
  The literal source signing domain is part of the checked raw bytes.
  SHA/curve verification still need their primitive boundary; the source
  serde producer relation is separately reviewed and sampled in the actual
 15-stimulus input-only reconstruction receipt, not assumed by this parser.
  The interpretation returns a registered_identity record whose four nat
  values represent source u64 identifiers, followed by two distinct byte
  arrays for issuer and grants SHA256. No cryptographic digest is encoded
  into or identified with any one of those nat identity identifiers.
\<close>

end

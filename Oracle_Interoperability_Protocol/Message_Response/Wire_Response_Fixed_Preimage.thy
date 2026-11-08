theory Wire_Response_Fixed_Preimage
  imports Wire_Response_Fixed_Fields
begin

record response_fixed_config =
  response_config_deployment :: nat
  response_config_local_endpoints :: "nat set"
  response_config_peers :: "(nat \<times> wire_bytes) set"
  response_config_principal :: nat
  response_config_key :: nat
  response_config_epoch :: nat
  response_config_route :: nat
  response_config_ttl :: nat
  response_config_max_nesting :: nat
  response_config_public_key :: wire_bytes
  response_config_policy_binding :: wire_bytes

definition response_fixed_channel_current where
  "response_fixed_channel_current config channel \<longleftrightarrow>
    negotiated_version (response_channel_profile channel) = 6 \<and>
    response_channel_deployment channel = response_config_deployment config \<and>
    response_channel_local channel \<in> response_config_local_endpoints config \<and>
    response_channel_local_key channel = response_config_public_key config \<and>
    (response_channel_remote channel,response_channel_remote_key channel) \<in> response_config_peers config"

definition response_fixed_be64 :: "nat \<Rightarrow> wire_bytes" where
  "response_fixed_be64 number = rev (put_le_octets 8 number)"

definition response_fixed_binding_preimage where
  "response_fixed_binding_preimage original atomicity words =
    [111,105,112,47,114,101,102,101,114,101,110,99,101,45,114,101,115,112,111,110,115,101,45,98,105,110,100,105,110,103,47,118,49,0] @
    response_fixed_be64 (length original) @ original @ response_fixed_be64 atomicity @
    response_fixed_be64 (length words) @ concat (map response_fixed_be64 words)"

lemma response_fixed_binding_preimage_uses_the_same_original_atomicity_and_words:
  "response_fixed_binding_preimage (encode_wire_core original) atomicity words =
    [111,105,112,47,114,101,102,101,114,101,110,99,101,45,114,101,115,112,111,110,115,101,45,98,105,110,100,105,110,103,47,118,49,0] @
    rev (put_le_octets 8 (length (encode_wire_core original))) @ encode_wire_core original @
    rev (put_le_octets 8 atomicity) @ rev (put_le_octets 8 (length words)) @
    concat (map (\<lambda>word. rev (put_le_octets 8 word)) words)"
proof -
  have mapped_words: "map response_fixed_be64 words = map (\<lambda>word. rev (put_le_octets 8 word)) words"
    by (rule map_cong[OF refl]) (simp add: response_fixed_be64_def)
  show ?thesis
    by (simp only: response_fixed_binding_preimage_def mapped_words response_fixed_be64_def)
qed

definition response_fixed_uuid_preimage where
  "response_fixed_uuid_preimage config response_binding issued =
    [111,105,112,47,114,101,102,101,114,101,110,99,101,45,114,101,115,112,111,110,115,101,45,117,117,105,100,47,118,49,0] @
    response_config_policy_binding config @ response_binding @ response_fixed_be64 issued"

definition response_fixed_uuid where
  "response_fixed_uuid digest =
    ((take 16 digest)[6 := digest ! 6 mod 16 + 64])[8 := digest ! 8 mod 64 + 128]"

lemma response_fixed_uuid_has_the_source_version_and_variant:
  fixes digest :: wire_bytes
  assumes "length digest = 32"
  shows "length (response_fixed_uuid digest) = 16"
    "response_fixed_uuid digest ! 6 div 16 = 4"
    "response_fixed_uuid digest ! 8 div 64 = 2"
proof -
  have version_remainder: "(digest ! 6 mod 16) div 16 = 0" by (rule mod_div_trivial)
  have variant_remainder: "(digest ! 8 mod 64) div 64 = 0" by (rule mod_div_trivial)
  have version_quotient: "(digest ! 6 mod 16 + 64) div 16 = 4"
    using div_mult_self1[of "16::nat" "digest ! 6 mod 16" 4] version_remainder by simp
  have variant_quotient: "(digest ! 8 mod 64 + 128) div 64 = 2"
    using div_mult_self1[of "64::nat" "digest ! 8 mod 64" 2] variant_remainder by simp
  show "length (response_fixed_uuid digest) = 16"
    using assms by (simp add: response_fixed_uuid_def)
  show "response_fixed_uuid digest ! 6 div 16 = 4"
    using assms version_quotient by (simp add: response_fixed_uuid_def)
  show "response_fixed_uuid digest ! 8 div 64 = 2"
    using assms variant_quotient by (simp add: response_fixed_uuid_def)
qed

definition response_fixed_parameters_from where
  "response_fixed_parameters_from hash config channel clock response_binding =
    (if \<not> response_fixed_channel_current config channel then None
     else map_option (\<lambda>issued.
       \<lparr>response_parameter_principal = response_config_principal config,
        response_parameter_key = response_config_key config,response_parameter_epoch = response_config_epoch config,
        response_parameter_issued = issued,response_parameter_ttl = response_config_ttl config,
        response_parameter_uuid = response_fixed_uuid (hash (response_fixed_uuid_preimage config response_binding issued)),
        response_parameter_route = response_config_route config\<rparr>) clock)"

lemma response_fixed_parameters_forward_the_immutable_config_and_clock_read:
  assumes "response_fixed_parameters_from hash config channel clock binding = Some parameters"
  shows "response_fixed_channel_current config channel"
    "clock = Some (response_parameter_issued parameters)"
    "response_parameter_principal parameters = response_config_principal config"
    "response_parameter_key parameters = response_config_key config"
    "response_parameter_epoch parameters = response_config_epoch config"
    "response_parameter_ttl parameters = response_config_ttl config"
    "response_parameter_route parameters = response_config_route config"
    "response_parameter_uuid parameters = response_fixed_uuid
       (hash (response_fixed_uuid_preimage config binding (response_parameter_issued parameters)))"
  using assms by (auto simp: response_fixed_parameters_from_def split: option.splits if_splits)

definition response_fixed_unframe where
  "response_fixed_unframe preimage =
    (if length preimage < 17 \<or> take 13 preimage \<noteq> [79,73,80,0,69,78,86,69,76,79,80,69,0] then None
     else let framed = drop 13 preimage; bytes = drop 4 framed;
              declared = get_le_octets (rev (take 4 framed))
          in if declared \<noteq> length bytes then None else decode_wire_core bytes)"

lemma response_fixed_unframe_recovers_exactly_the_core_that_was_signed:
  assumes formed: "wire_core_wellformed core"
    and width: "length (encode_wire_core core) < 256^4"
  shows "response_fixed_unframe (envelope_signing_bytes core) = Some core"
  using get_le_octets_reads_every_representable_word[OF width]
    wellformed_canonical_core_has_a_two_way_encoding[OF formed]
  by (simp add: response_fixed_unframe_def envelope_signing_bytes_def Let_def)

definition response_fixed_signable where
  "response_fixed_signable config now core \<longleftrightarrow>
    wire_sent_seconds core \<le> now \<and>
    wire_sent_seconds core + response_config_ttl config < 2^64 \<and>
    now \<le> wire_sent_seconds core + response_config_ttl config \<and>
    wire_version core = 6 \<and> wire_purpose core = 1 \<and>
    wire_deployment core = response_config_deployment config \<and>
    wire_source_domain core \<in> response_config_local_endpoints config \<and>
    wire_target_domain core \<in> fst ` response_config_peers config \<and>
    wire_principal core = response_config_principal config \<and> wire_key_number core = response_config_key config \<and>
    wire_authority_epoch core = response_config_epoch config \<and> wire_route_scope core = response_config_route config \<and>
    wire_ttl_seconds core = response_config_ttl config \<and> wire_signature_scheme core = 1 \<and>
    code_decode_operand_tree (response_config_max_nesting config) core = Code_Tree_Ready Code_Nested_Response"

definition response_fixed_sign ::
  "('key \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes) \<Rightarrow> 'key \<Rightarrow> response_fixed_config \<Rightarrow>
    nat option \<Rightarrow> wire_bytes \<Rightarrow> wire_bytes option" where
  "response_fixed_sign curve_sign signing_key config clock preimage =
    (case response_fixed_unframe preimage of None \<Rightarrow> None | Some core \<Rightarrow>
      case clock of None \<Rightarrow> None | Some now \<Rightarrow>
        if response_fixed_signable config now core then Some (curve_sign signing_key preimage) else None)"

theorem response_fixed_sign_forwards_the_exact_framed_bytes_to_the_curve_primitive:
  assumes "response_fixed_sign curve_sign signing_key config clock preimage = Some signature"
  obtains core now where "response_fixed_unframe preimage = Some core" "clock = Some now"
    "response_fixed_signable config now core" "curve_sign signing_key preimage = signature"
  using assms by (auto simp: response_fixed_sign_def split: option.splits if_splits)

lemma response_fixed_sign_refuses_an_unframed_or_unavailable_clock_input:
  "response_fixed_unframe preimage = None \<Longrightarrow>
    response_fixed_sign curve_sign signing_key config clock preimage = None"
  "response_fixed_sign curve_sign signing_key config None preimage = None"
  by (simp_all add: response_fixed_sign_def split: option.splits)

lemma response_fixed_source_uuid_never_uses_a_supplied_uuid_as_its_binding:
  "response_parameter_uuid parameters = response_fixed_uuid
      (hash (response_fixed_uuid_preimage config
        (hash (response_fixed_binding_preimage original atomicity words)) issued)) \<Longrightarrow>
    response_parameter_uuid parameters = response_fixed_uuid
      (hash ([111,105,112,47,114,101,102,101,114,101,110,99,101,45,114,101,115,112,111,110,115,101,45,117,117,105,100,47,118,49,0] @
        response_config_policy_binding config @ hash (response_fixed_binding_preimage original atomicity words) @
        response_fixed_be64 issued))"
  by (simp add: response_fixed_uuid_preimage_def)

text \<open>
  Source: ed25519.rs channel_current, ResponseSigner::parameters and sign.
  Hash and curve_sign are named primitive interfaces, not arbitrary product
  runners. SHA256 output length/octet range and key/curve laws remain primitive
  boundaries. The exact policy-binding bytes are the immutable provider field;
  its source producer is owned by the identity/configuration link. Parameters
  and signing read distinct clocks; no equality between those reads is assumed.
  The positive source core must pass the actual recursive response operand
  decoder before these exact framed bytes reach the signing primitive.
\<close>

end

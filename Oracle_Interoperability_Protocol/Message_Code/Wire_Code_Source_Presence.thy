theory Wire_Code_Source_Presence
  imports Wire_Code_Encoder
begin

record code_source_core =
  source_version :: "nat option"
  source_purpose :: "nat option"
  source_deployment :: "nat option"
  source_source_domain :: "nat option"
  source_target_domain :: "nat option"
  source_principal :: "nat option"
  source_key_id :: "nat option"
  source_authority_epoch :: "nat option"
  source_issued_seconds :: "nat option"
  source_ttl_seconds :: "nat option"
  source_uuid :: "wire_bytes option"
  source_family :: "nat option"
  source_primary :: "nat option"
  source_secondary :: "nat option"
  source_signature_scheme :: "nat option"
  source_atomicity :: "nat option"
  source_priority :: "nat option"
  source_route_scope :: "nat option"
  source_body :: "(wire_family \<times> code_source_operation) option"

definition code_required_core_numbers :: "code_source_core \<Rightarrow> nat option list" where
  "code_required_core_numbers source =
    [source_version source,source_purpose source,source_deployment source,
     source_source_domain source,source_target_domain source,source_principal source,
     source_key_id source,source_authority_epoch source,source_issued_seconds source,
     source_ttl_seconds source,source_family source,source_primary source,
     source_signature_scheme source,source_atomicity source,source_priority source,source_route_scope source]"

definition code_numbers_present where
  "code_numbers_present numbers \<longleftrightarrow> (\<forall>value \<in> set numbers. value \<noteq> None)"

definition code_numbers_are_u64 where
  "code_numbers_are_u64 numbers \<longleftrightarrow>
    (\<forall>value \<in> set numbers. \<forall>number. value = Some number \<longrightarrow> number < 2^64)"

lemma present_u64_fields_have_bounded_projected_values:
  assumes "code_numbers_present numbers" "code_numbers_are_u64 numbers"
  shows "\<forall>value \<in> set numbers. the value < 2^64"
proof (intro ballI)
  fix optional
  assume member: "optional \<in> set numbers"
  obtain number where exact: "optional = Some number"
    using assms(1) member by (cases optional) (auto simp: code_numbers_present_def)
  show "the optional < 2^64"
    using assms(2) member exact by (auto simp: code_numbers_are_u64_def)
qed

definition code_operation_machine_domain :: "code_source_operation \<Rightarrow> bool" where
  "code_operation_machine_domain source \<longleftrightarrow>
    code_numbers_are_u64 [source_opcode source] \<and>
    length (source_words source) < 2^64 \<and> length (source_blobs source) < 2^64 \<and>
    (\<forall>word \<in> set (source_words source). word < 2^64) \<and>
    (\<forall>blob \<in> set (source_blobs source). wire_octets blob \<and> length blob < 2^64) \<and>
    (case source_deadline source of Some (Code_Finite seconds) \<Rightarrow> seconds < 2^64 | _ \<Rightarrow> True)"

lemma a_projected_source_operation_has_the_machine_field_domain:
  assumes "code_operation_machine_domain source" "code_project_operation source = Some body"
  shows "wire_body_wellformed body"
proof (cases "source_opcode source")
  case None
  then show ?thesis using assms(2) by (simp add: code_project_operation_def)
next
  case (Some operation)
  then have opcode: "source_opcode source = Some operation" .
  show ?thesis
  proof (cases "source_deadline source")
    case None
    then show ?thesis using opcode assms
      by (auto simp: code_operation_machine_domain_def code_numbers_are_u64_def
        code_project_operation_def wire_body_wellformed_def body_fields_def)
  next
    case (Some ending)
    then have deadline: "source_deadline source = Some ending" .
    show ?thesis
    proof (cases ending)
      case (Code_Indefinite valid)
      then show ?thesis using opcode deadline assms
        by (cases valid)
          (auto simp: code_operation_machine_domain_def code_numbers_are_u64_def
            code_project_operation_def wire_body_wellformed_def body_fields_def)
    next
      case (Code_Finite seconds)
      then show ?thesis using opcode deadline assms
        by (auto simp: code_operation_machine_domain_def code_numbers_are_u64_def
          code_project_operation_def wire_body_wellformed_def body_fields_def)
    qed
  qed
qed

definition code_source_core_machine_domain :: "code_source_core \<Rightarrow> bool" where
  "code_source_core_machine_domain source \<longleftrightarrow>
    code_numbers_are_u64 (code_required_core_numbers source @ [source_secondary source]) \<and>
    (case source_uuid source of None \<Rightarrow> True | Some uuid \<Rightarrow> wire_octets uuid \<and> length uuid < 2^64) \<and>
    (case source_body source of None \<Rightarrow> True | Some (family,body) \<Rightarrow> code_operation_machine_domain body)"

definition code_project_core :: "code_source_core \<Rightarrow> wire_core option" where
  "code_project_core source =
    (if \<not> code_numbers_present (code_required_core_numbers source) then None
     else case (source_uuid source,source_body source) of (Some uuid,Some (family,operation)) \<Rightarrow>
       if source_family source \<noteq> Some (family_number family) then None
       else map_option (\<lambda>body.
         \<lparr>wire_version = the (source_version source), wire_purpose = the (source_purpose source),
          wire_deployment = the (source_deployment source), wire_source_domain = the (source_source_domain source),
          wire_target_domain = the (source_target_domain source), wire_principal = the (source_principal source),
          wire_key_number = the (source_key_id source), wire_authority_epoch = the (source_authority_epoch source),
          wire_sent_seconds = the (source_issued_seconds source), wire_ttl_seconds = the (source_ttl_seconds source),
          wire_uuid = uuid,wire_message_family = family,wire_primary_code = the (source_primary source),
          wire_secondary_code = source_secondary source,wire_signature_scheme = the (source_signature_scheme source),
          wire_operation_body = body,wire_atomicity = the (source_atomicity source),
          wire_priority = the (source_priority source),wire_route_scope = the (source_route_scope source)\<rparr>)
         (code_project_operation operation)
     | _ \<Rightarrow> None)"

lemma a_missing_required_scalar_has_no_semantic_source_projection:
  assumes "None \<in> set (code_required_core_numbers source)"
  shows "code_project_core source = None"
  using assms by (simp add: code_project_core_def code_numbers_present_def)

lemma a_missing_core_uuid_or_body_has_no_semantic_source_projection:
  "source_uuid source = None \<Longrightarrow> code_project_core source = None"
  "source_body source = None \<Longrightarrow> code_project_core source = None"
  by (auto simp: code_project_core_def split: option.splits)

lemma a_conflicting_declared_family_has_no_semantic_source_projection:
  assumes "source_body source = Some (family,operation)"
    "source_family source \<noteq> Some (family_number family)"
  shows "code_project_core source = None"
  using assms by (simp add: code_project_core_def split: option.splits)

lemma source_projection_preserves_the_complete_unsigned_header:
  assumes "code_project_core source = Some core"
  shows "Some (wire_version core) = source_version source"
    "Some (wire_purpose core) = source_purpose source"
    "Some (wire_deployment core) = source_deployment source"
    "Some (wire_source_domain core) = source_source_domain source"
    "Some (wire_target_domain core) = source_target_domain source"
    "Some (wire_principal core) = source_principal source"
    "Some (wire_key_number core) = source_key_id source"
    "Some (wire_authority_epoch core) = source_authority_epoch source"
    "Some (wire_sent_seconds core) = source_issued_seconds source"
    "Some (wire_ttl_seconds core) = source_ttl_seconds source"
    "Some (wire_uuid core) = source_uuid source"
    "Some (family_number (wire_message_family core)) = source_family source"
    "Some (wire_primary_code core) = source_primary source"
    "wire_secondary_code core = source_secondary source"
    "Some (wire_signature_scheme core) = source_signature_scheme source"
    "Some (wire_atomicity core) = source_atomicity source"
    "Some (wire_priority core) = source_priority source"
    "Some (wire_route_scope core) = source_route_scope source"
  using assms
  by (auto simp: code_project_core_def code_numbers_present_def code_required_core_numbers_def
    split: option.splits prod.splits if_splits)

lemma a_projected_source_core_has_the_machine_field_domain:
  assumes typed: "code_source_core_machine_domain source"
    and projected: "code_project_core source = Some core"
  shows "code_core_machine_domain core"
proof -
  obtain uuid family operation body where parts:
      "source_uuid source = Some uuid" "source_body source = Some (family,operation)"
      "code_project_operation operation = Some body"
      "wire_uuid core = uuid" "wire_operation_body core = body"
    using projected by (auto simp: code_project_core_def split: option.splits prod.splits if_splits)
  have operation_domain: "code_operation_machine_domain operation"
    using typed parts(2) by (simp add: code_source_core_machine_domain_def)
  have body: "wire_body_wellformed (wire_operation_body core)"
    using a_projected_source_operation_has_the_machine_field_domain[OF operation_domain parts(3)] parts(5) by simp
  have body_octets: "wire_octets (encode_wire_body (wire_operation_body core))"
    unfolding encode_wire_body_def
    by (rule encoded_wire_fields_are_octets) (use body in \<open>simp add: wire_body_wellformed_def\<close>)
  note exact = source_projection_preserves_the_complete_unsigned_header[OF projected]
  have numbers: "code_numbers_are_u64
      [Some (wire_version core),Some (wire_purpose core),Some (wire_deployment core),
       Some (wire_source_domain core),Some (wire_target_domain core),Some (wire_principal core),
       Some (wire_key_number core),Some (wire_authority_epoch core),Some (wire_sent_seconds core),
       Some (wire_ttl_seconds core),Some (family_number (wire_message_family core)),Some (wire_primary_code core),
       Some (wire_signature_scheme core),Some (wire_atomicity core),Some (wire_priority core),Some (wire_route_scope core),
       wire_secondary_code core]"
    using typed exact by (simp add: code_source_core_machine_domain_def code_required_core_numbers_def)
  have uuid: "wire_octets (wire_uuid core)"
    using typed parts(1,4) by (simp add: code_source_core_machine_domain_def)
  have family_bound: "family_number (wire_message_family core) < 8"
    by (cases "wire_message_family core") simp_all
  show ?thesis using body body_octets numbers uuid family_bound
    by (cases "wire_secondary_code core")
      (auto simp: code_core_machine_domain_def core_fields_def secondary_field_def code_numbers_are_u64_def)
qed

definition code_source_encode_core :: "code_source_core \<Rightarrow> wire_bytes option" where
  "code_source_encode_core source =
    Option.bind (code_project_core source) code_encode_core"

theorem a_typed_generated_core_encoding_has_the_exact_model_value_and_bytes:
  assumes typed: "code_source_core_machine_domain source"
    and encoded: "code_source_encode_core source = Some bytes"
  obtains core where "code_project_core source = Some core"
    "wire_core_wellformed core" "encode_wire_core core = bytes"
proof -
  obtain core where projected: "code_project_core source = Some core"
    and accepted: "code_encode_core core = Some bytes"
  proof (cases "code_project_core source")
    case None
    then show thesis using encoded by (simp add: code_source_encode_core_def)
  next
    case (Some core)
    then have result: "code_encode_core core = Some bytes"
      using encoded by (simp add: code_source_encode_core_def)
    show thesis by (rule that[OF Some result])
  qed
  have domain: "code_core_machine_domain core"
    by (rule a_projected_source_core_has_the_machine_field_domain[OF typed projected])
  have "code_typed_encode_core core = Some bytes"
    using domain accepted by (simp add: code_typed_encode_core_def)
  then have "wire_core_wellformed core" "encode_wire_core core = bytes"
    using the_typed_source_core_encoder_discharges_the_reencoding_obligation
    by (auto simp: code_core_encoder_sound_def)
  then show thesis by (rule that[OF projected])
qed

theorem reencoding_a_typed_generated_core_gives_the_received_model_value:
  assumes typed: "code_source_core_machine_domain source"
    and accepted: "code_reencoding_decode shape parse code_source_encode_core bytes = Some source"
  obtains core where "code_project_core source = Some core"
    "decode_wire_core bytes = Some core" "encode_wire_core core = bytes"
proof -
  have encoded: "code_source_encode_core source = Some bytes"
    by (rule an_accepted_generated_value_passes_the_exact_encoder(3)[OF accepted])
  obtain core where projected: "code_project_core source = Some core"
    and valid: "wire_core_wellformed core" and exact: "encode_wire_core core = bytes"
    by (rule a_typed_generated_core_encoding_has_the_exact_model_value_and_bytes[OF typed encoded])
  have decoded: "decode_wire_core bytes = Some core"
    using wellformed_canonical_core_has_a_two_way_encoding[OF valid] exact by simp
  show thesis by (rule that[OF projected decoded exact])
qed

end

theory Wire_Code_Prechecks
  imports Wire_Code_Varint_Read "OIP_Product.Wire_Admission"
begin

definition code_declared_version :: "wire_bytes \<Rightarrow> nat option" where
  "code_declared_version bytes =
    Option.bind (code_take_varint bytes) (\<lambda>(packet_tag,packet_tail).
      if packet_tag \<noteq> 10 then None
      else Option.bind (code_take_varint packet_tail) (\<lambda>(declared_length,packet_body).
        if declared_length > length packet_body then None
        else Option.bind (code_take_varint (take declared_length packet_body)) (\<lambda>(core_tag,version_tail).
          if core_tag \<noteq> 8 then None else map_option fst (code_take_varint version_tail))))"

definition code_check_declared_version :: "wire_bytes \<Rightarrow> nat \<Rightarrow> wire_refusal option" where
  "code_check_declared_version bytes max_frame =
    (if length bytes > max_frame then Some Invalid_Wire_Format
     else case code_declared_version bytes of Some version \<Rightarrow>
       if version \<noteq> 6 then Some Unsupported_Wire_Version else None
     | None \<Rightarrow> None)"

definition code_core_suffix :: "wire_core \<Rightarrow> wire_bytes" where
  "code_core_suffix core = put_proto_fields (tl (core_fields core))"

lemma canonical_core_starts_with_its_exact_declared_version:
  "encode_wire_core core = put_wire_varint 8 @ put_wire_varint (wire_version core) @ code_core_suffix core"
  by (simp add: encode_wire_core_def core_fields_def code_core_suffix_def put_proto_fields_def
    make_proto_tag_def)

theorem the_source_declared_version_reads_the_canonical_core_version:
  fixes packet :: wire_packet
  assumes packet: "wire_packet_wellformed packet"
  shows "code_declared_version (encode_wire_packet packet @ suffix) = Some (wire_version (packet_core packet))"
proof -
  let ?core = "packet_core packet"
  let ?encoded = "encode_wire_core ?core"
  let ?tail = "put_proto_field (Proto_Bytes 2 (packet_signature packet)) @ suffix"
  have version_bound: "wire_version ?core < 2^64"
    using packet
    by (simp add: wire_packet_wellformed_def wire_core_wellformed_def core_fields_def)
  have length_bound: "length ?encoded < 2^64"
    using packet by (simp add: wire_packet_wellformed_def; arith)
  have header: "code_take_varint (encode_wire_packet packet @ suffix) =
      Some (10,put_wire_varint (length ?encoded) @ ?encoded @ ?tail)"
    by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def make_proto_tag_def
      the_source_reader_accepts_every_canonical_u64_prefix)
  have size: "code_take_varint (put_wire_varint (length ?encoded) @ ?encoded @ ?tail) =
      Some (length ?encoded,?encoded @ ?tail)"
    by (rule the_source_reader_accepts_every_canonical_u64_prefix[OF length_bound])
  note normalized_size = size[unfolded put_proto_field.simps append_assoc]
  have first: "code_take_varint ?encoded =
      Some (8,put_wire_varint (wire_version ?core) @ code_core_suffix ?core)"
    by (subst canonical_core_starts_with_its_exact_declared_version)
      (simp add: the_source_reader_accepts_every_canonical_u64_prefix)
  have version: "code_take_varint (put_wire_varint (wire_version ?core) @ code_core_suffix ?core) =
      Some (wire_version ?core,code_core_suffix ?core)"
    by (rule the_source_reader_accepts_every_canonical_u64_prefix[OF version_bound])
  show ?thesis
    by (simp add: code_declared_version_def header normalized_size first version
      the_source_reader_accepts_every_canonical_u64_prefix length_bound)
qed

lemma unsupported_declared_versions_are_refused_without_reading_later_fields:
  assumes "length bytes \<le> max_frame" "code_declared_version bytes = Some version" "version \<noteq> 6"
  shows "code_check_declared_version bytes max_frame = Some Unsupported_Wire_Version"
  using assms by (simp add: code_check_declared_version_def)

lemma a_canonical_current_packet_passes_the_declared_version_precheck:
  fixes packet :: wire_packet
  assumes "wire_packet_wellformed packet" "wire_version (packet_core packet) = 6"
    "length (encode_wire_packet packet) \<le> max_frame"
  shows "code_check_declared_version (encode_wire_packet packet) max_frame = None"
  using assms the_source_declared_version_reads_the_canonical_core_version[OF assms(1), of "[]"]
  by (simp add: code_check_declared_version_def)

lemma the_size_refusal_precedes_the_version_refusal:
  "length bytes > max_frame \<Longrightarrow>
    code_check_declared_version bytes max_frame = Some Invalid_Wire_Format"
  by (simp add: code_check_declared_version_def)

fun code_reference_accepts :: "wire_family \<Rightarrow> nat \<Rightarrow> bool" where
  "code_reference_accepts Wire_State_Sync operation = (operation \<in> {1..6})"
| "code_reference_accepts Wire_Regulatory operation = (operation \<in> {1..3})"
| "code_reference_accepts Wire_Lock operation = (operation \<in> {1..6})"
| "code_reference_accepts Wire_Query operation = (operation \<in> {1..8})"
| "code_reference_accepts Wire_Ack operation = (operation = 1)"
| "code_reference_accepts Wire_Heartbeat operation = False"
| "code_reference_accepts Wire_Governance operation = (operation = 1)"

lemma every_accepted_reference_operation_is_a_protocol_operation:
  "code_reference_accepts family operation \<Longrightarrow> valid_family_opcode family operation"
  by (cases family) auto

definition code_check_operation where
  "code_check_operation accepts core =
    (if accepts (wire_message_family core) (wire_opcode (wire_operation_body core))
     then None else Some Unsupported_Wire_Version)"

lemma unsupported_reference_operations_cannot_reach_a_signature_consumer:
  assumes "\<not> code_reference_accepts (wire_message_family core) (wire_opcode (wire_operation_body core))"
  shows "code_check_operation code_reference_accepts core = Some Unsupported_Wire_Version"
  using assms by (simp add: code_check_operation_def)

definition code_run_after_precheck where
  "code_run_after_precheck check execute bytes state =
    (case check bytes of Some refusal \<Rightarrow> (state,Inl refusal) | None \<Rightarrow> execute bytes state)"

lemma every_precheck_refusal_is_before_any_state_effect:
  "check bytes = Some refusal \<Longrightarrow>
    code_run_after_precheck check execute bytes state = (state,Inl refusal)"
  by (simp add: code_run_after_precheck_def)

end

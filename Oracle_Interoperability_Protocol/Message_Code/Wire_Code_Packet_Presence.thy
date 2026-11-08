theory Wire_Code_Packet_Presence
  imports Wire_Code_Source_Presence
begin

record code_source_packet =
  source_packet_core :: "code_source_core option"
  source_packet_signature :: "wire_bytes option"

definition code_source_packet_machine_domain :: "code_source_packet \<Rightarrow> bool" where
  "code_source_packet_machine_domain source \<longleftrightarrow>
    (case source_packet_core source of None \<Rightarrow> True | Some core \<Rightarrow> code_source_core_machine_domain core) \<and>
    (case source_packet_signature source of None \<Rightarrow> True | Some signature \<Rightarrow>
      wire_octets signature \<and> length signature < 2^64)"

definition code_project_packet :: "code_source_packet \<Rightarrow> wire_packet option" where
  "code_project_packet source =
    (case (source_packet_core source,source_packet_signature source) of (Some core,Some signature) \<Rightarrow>
      map_option (\<lambda>value. \<lparr>packet_core = value,packet_signature = signature\<rparr>) (code_project_core core)
     | _ \<Rightarrow> None)"

definition code_source_encode_packet :: "code_source_packet \<Rightarrow> wire_bytes option" where
  "code_source_encode_packet source =
    (case (source_packet_core source,source_packet_signature source) of (Some core,Some signature) \<Rightarrow>
      if (source_signature_scheme core = Some 1 \<and> length signature \<noteq> 64) \<or>
         (source_signature_scheme core = Some 2 \<and> signature = []) then None
      else (case code_source_encode_core core of None \<Rightarrow> None | Some encoded \<Rightarrow>
        if length encoded \<ge> 2^32 then None
        else Some (code_field_bytes 1 encoded @ code_field_bytes 2 signature))
     | _ \<Rightarrow> None)"

lemma a_missing_packet_core_or_signature_has_no_source_encoding:
  "source_packet_core source = None \<Longrightarrow> code_source_encode_packet source = None"
  "source_packet_signature source = None \<Longrightarrow> code_source_encode_packet source = None"
  by (auto simp: code_source_encode_packet_def split: option.splits)

theorem a_typed_generated_packet_encoding_has_the_exact_model_value_and_bytes:
  assumes typed: "code_source_packet_machine_domain source"
    and encoded: "code_source_encode_packet source = Some bytes"
  obtains packet where "code_project_packet source = Some packet"
    "wire_packet_wellformed packet" "encode_wire_packet packet = bytes"
proof -
  obtain raw signature core_bytes where fields:
      "source_packet_core source = Some raw" "source_packet_signature source = Some signature"
      "code_source_encode_core raw = Some core_bytes"
      "\<not> (source_signature_scheme raw = Some 1 \<and> length signature \<noteq> 64)"
      "\<not> (source_signature_scheme raw = Some 2 \<and> signature = [])"
      "length core_bytes < 2^32"
      "bytes = code_field_bytes 1 core_bytes @ code_field_bytes 2 signature"
    using encoded
    by (auto simp: code_source_encode_packet_def split: option.splits prod.splits if_splits)
  have core_domain: "code_source_core_machine_domain raw"
    and signature_octets: "wire_octets signature"
    using typed fields(1,2) by (simp_all add: code_source_packet_machine_domain_def)
  obtain core where projected: "code_project_core raw = Some core"
    and core_valid: "wire_core_wellformed core" and core_bytes: "encode_wire_core core = core_bytes"
    by (rule a_typed_generated_core_encoding_has_the_exact_model_value_and_bytes[OF core_domain fields(3)])
  let ?packet = "\<lparr>packet_core = core,packet_signature = signature\<rparr>"
  have scheme: "Some (wire_signature_scheme core) = source_signature_scheme raw"
    by (rule source_projection_preserves_the_complete_unsigned_header(15)[OF projected])
  have known_scheme: "wire_signature_scheme core \<in> {1,2}"
    using core_valid by (simp add: wire_core_wellformed_def)
  have valid: "wire_packet_wellformed ?packet"
    using core_valid core_bytes signature_octets fields(4,5,6) scheme known_scheme
    by (auto simp: wire_packet_wellformed_def)
  have projection: "code_project_packet source = Some ?packet"
    using fields(1,2) projected by (simp add: code_project_packet_def)
  have exact: "encode_wire_packet ?packet = bytes"
    using core_bytes fields(7)
    by (simp add: encode_wire_packet_def packet_fields_def put_proto_fields_def
      source_field_emitters_are_the_model_field_emitters)
  show thesis by (rule that[OF projection valid exact])
qed

theorem reencoding_a_typed_generated_packet_gives_the_received_model_value:
  assumes typed: "code_source_packet_machine_domain source"
    and accepted: "code_reencoding_decode shape parse code_source_encode_packet bytes = Some source"
  obtains packet where "code_project_packet source = Some packet"
    "decode_wire_packet bytes = Some packet" "encode_wire_packet packet = bytes"
proof -
  have encoded: "code_source_encode_packet source = Some bytes"
    by (rule an_accepted_generated_value_passes_the_exact_encoder(3)[OF accepted])
  obtain packet where projected: "code_project_packet source = Some packet"
    and valid: "wire_packet_wellformed packet" and exact: "encode_wire_packet packet = bytes"
    by (rule a_typed_generated_packet_encoding_has_the_exact_model_value_and_bytes[OF typed encoded])
  have decoded: "decode_wire_packet bytes = Some packet"
    using the_exact_wire_message_decodes_from_its_canonical_bytes[OF valid] exact by simp
  show thesis by (rule that[OF projected decoded exact])
qed

end

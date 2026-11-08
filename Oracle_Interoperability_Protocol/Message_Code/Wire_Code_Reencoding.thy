theory Wire_Code_Reencoding
  imports "OIP_Product.Wire_Packet"
begin

text \<open>
  The generated decoder is an arbitrary function.  The hand-written encoder
  remains a separate parameter: its soundness obligation is explicit below.
  These results isolate the re-encoding checks in codec.rs::decode_core and
  codec.rs::decode_packet.  They do not assert that an unverified source
  encoder has already met that obligation.
\<close>

definition code_reencoding_decode ::
  "(wire_bytes \<Rightarrow> bool) \<Rightarrow> (wire_bytes \<Rightarrow> 'a option) \<Rightarrow>
   ('a \<Rightarrow> wire_bytes option) \<Rightarrow> wire_bytes \<Rightarrow> 'a option" where
  "code_reencoding_decode shape parse encode bytes =
    (if \<not> shape bytes then None
     else case parse bytes of None \<Rightarrow> None | Some value \<Rightarrow>
       (case encode value of None \<Rightarrow> None | Some canonical \<Rightarrow>
          if canonical = bytes then Some value else None))"

lemma an_accepted_generated_value_passes_the_exact_encoder:
  assumes accepted: "code_reencoding_decode shape parse encode bytes = Some value"
  shows "shape bytes" "parse bytes = Some value" "encode value = Some bytes"
proof -
  have allowed: "shape bytes"
    using accepted by (cases "shape bytes") (simp_all add: code_reencoding_decode_def)
  obtain candidate where parsed: "parse bytes = Some candidate"
    using accepted allowed by (cases "parse bytes") (auto simp: code_reencoding_decode_def)
  obtain canonical where encoded: "encode candidate = Some canonical"
    using accepted allowed parsed by (cases "encode candidate") (auto simp: code_reencoding_decode_def)
  have same: "canonical = bytes" "candidate = value"
    using accepted allowed parsed encoded
    by (auto simp: code_reencoding_decode_def split: if_splits)
  show "shape bytes" by (rule allowed)
  show "parse bytes = Some value" using parsed same(2) by simp
  show "encode value = Some bytes" using encoded same by simp
qed

lemma changing_the_generated_decoder_cannot_bypass_the_encoding_check:
  assumes "encode value \<noteq> Some bytes"
  shows "code_reencoding_decode shape parse encode bytes \<noteq> Some value"
proof
  assume accepted: "code_reencoding_decode shape parse encode bytes = Some value"
  have exact: "encode value = Some bytes"
    by (rule an_accepted_generated_value_passes_the_exact_encoder(3)[OF accepted])
  show False by (rule notE[OF assms exact])
qed

definition code_core_encoder_sound :: "(wire_core \<Rightarrow> wire_bytes option) \<Rightarrow> bool" where
  "code_core_encoder_sound encode \<longleftrightarrow>
    (\<forall>core bytes. encode core = Some bytes \<longrightarrow>
      wire_core_wellformed core \<and> encode_wire_core core = bytes)"

theorem every_checked_core_is_the_model_decoding_of_the_received_bytes:
  assumes encoder: "code_core_encoder_sound encode"
    and accepted: "code_reencoding_decode shape parse encode bytes = Some core"
  shows "decode_wire_core bytes = Some core"
    "wire_core_wellformed core"
    "encode_wire_core core = bytes"
proof -
  have encoded: "encode core = Some bytes"
    by (rule an_accepted_generated_value_passes_the_exact_encoder(3)[OF accepted])
  have exact: "wire_core_wellformed core" "encode_wire_core core = bytes"
    using encoder[unfolded code_core_encoder_sound_def, rule_format, OF encoded] by auto
  have decoded: "decode_wire_core (encode_wire_core core) = Some core"
    by (rule wellformed_canonical_core_has_a_two_way_encoding[OF exact(1)])
  show "decode_wire_core bytes = Some core"
    using decoded by (simp only: exact(2))
  show "wire_core_wellformed core" by (rule exact(1))
  show "encode_wire_core core = bytes" by (rule exact(2))
qed

definition code_packet_encoder_sound :: "(wire_packet \<Rightarrow> wire_bytes option) \<Rightarrow> bool" where
  "code_packet_encoder_sound encode \<longleftrightarrow>
    (\<forall>packet bytes. encode packet = Some bytes \<longrightarrow>
      wire_packet_wellformed packet \<and> encode_wire_packet packet = bytes)"

theorem every_checked_packet_is_the_model_decoding_of_the_received_bytes:
  assumes encoder: "code_packet_encoder_sound encode"
    and accepted: "code_reencoding_decode shape parse encode bytes = Some packet"
  shows "decode_wire_packet bytes = Some packet"
    "wire_packet_wellformed packet"
    "encode_wire_packet packet = bytes"
proof -
  have encoded: "encode packet = Some bytes"
    by (rule an_accepted_generated_value_passes_the_exact_encoder(3)[OF accepted])
  have exact: "wire_packet_wellformed packet" "encode_wire_packet packet = bytes"
    using encoder[unfolded code_packet_encoder_sound_def, rule_format, OF encoded] by auto
  have decoded: "decode_wire_packet (encode_wire_packet packet) = Some packet"
    by (rule the_exact_wire_message_decodes_from_its_canonical_bytes[OF exact(1)])
  show "decode_wire_packet bytes = Some packet"
    using decoded by (simp only: exact(2))
  show "wire_packet_wellformed packet" by (rule exact(1))
  show "encode_wire_packet packet = bytes" by (rule exact(2))
qed

theorem two_checked_generated_decoders_cannot_disagree_on_the_core:
  assumes first_sound: "code_core_encoder_sound first_encoder"
    and second_sound: "code_core_encoder_sound second_encoder"
    and first: "code_reencoding_decode first_shape first_parser first_encoder bytes = Some first"
    and second: "code_reencoding_decode second_shape second_parser second_encoder bytes = Some second"
  shows "first = second"
  using every_checked_core_is_the_model_decoding_of_the_received_bytes(1)[OF first_sound first]
    every_checked_core_is_the_model_decoding_of_the_received_bytes(1)[OF second_sound second]
  by simp

theorem two_checked_generated_decoders_cannot_disagree_on_the_packet:
  assumes first_sound: "code_packet_encoder_sound first_encoder"
    and second_sound: "code_packet_encoder_sound second_encoder"
    and first: "code_reencoding_decode first_shape first_parser first_encoder bytes = Some first"
    and second: "code_reencoding_decode second_shape second_parser second_encoder bytes = Some second"
  shows "first = second"
  using every_checked_packet_is_the_model_decoding_of_the_received_bytes(1)[OF first_sound first]
    every_checked_packet_is_the_model_decoding_of_the_received_bytes(1)[OF second_sound second]
  by simp

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      every_checked_core_is_the_model_decoding_of_the_received_bytes
      every_checked_packet_is_the_model_decoding_of_the_received_bytes
      two_checked_generated_decoders_cannot_disagree_on_the_core
      two_checked_generated_decoders_cannot_disagree_on_the_packet})
  then () else error "Unexpected oracle in generated-decoder re-encoding checks"
\<close>

end

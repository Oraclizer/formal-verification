theory Reference_Write_Raw_Ack_Seed
  imports "OIP_Reference_Write_Core_Seed.Reference_Write_Core_Seed"
    "OIP_Message_Code.Wire_Code_Typed_Summary_Check"
begin

definition write_fixture_ack_core where
  "write_fixture_ack_core = write_fixture_core\<lparr>
    wire_principal := 42, wire_key_number := 3,
    wire_uuid := [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,16],
    wire_message_family := Wire_Ack,
    wire_operation_body := \<lparr>wire_opcode = 2, wire_words = [7,1,1,20,1,0],
      wire_blobs = [encode_wire_core write_fixture_core], wire_deadline = Deadline_Absent\<rparr>\<rparr>"

lemma the_write_ack_seed_embeds_the_proved_core_and_its_success_result:
  "wire_blobs (wire_operation_body write_fixture_ack_core) = [encode_wire_core write_fixture_core]"
  "response_result_words (wire_words (wire_operation_body write_fixture_ack_core)) = Some ((7,1),Recorded_Result,20,Some 0)"
  by (simp_all add: write_fixture_ack_core_def response_result_words_def response_kind_at_def)

text \<open>The repeated signature octets give the packet its canonical shape.
  The typed operand observation here stops before envelope authentication.\<close>

definition write_fixture_raw_ack_vector where
  "write_fixture_raw_ack_vector =
    (map integer_of_nat (encode_wire_packet
       \<lparr>packet_core = write_fixture_ack_core, packet_signature = replicate 64 177\<rparr>),
     map_option (map integer_of_nat) (code_typed_operand_ir 4 write_fixture_ack_core))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_write_ack_seed_embeds_the_proved_core_and_its_success_result})
  then () else error "Unexpected oracle in the raw Write response seed"
\<close>

export_code write_fixture_raw_ack_vector
  in SML module_name Reference_Write_Raw_Ack_Seed file_prefix "reference_write_raw_ack_seed"

end

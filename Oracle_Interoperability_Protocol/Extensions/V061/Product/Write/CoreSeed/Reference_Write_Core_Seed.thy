theory Reference_Write_Core_Seed
  imports "OIP_Reference_Write_Vector_Export.Reference_Write_Vector_Export"
begin

definition write_fixture_core where
  "write_fixture_core =
    \<lparr>wire_version = 6, wire_purpose = 1, wire_deployment = 7,
      wire_source_domain = 0, wire_target_domain = 0, wire_principal = 7,
      wire_key_number = 9, wire_authority_epoch = 9, wire_sent_seconds = 100,
      wire_ttl_seconds = 5, wire_uuid = [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
      wire_message_family = Wire_Lock, wire_primary_code = 1, wire_secondary_code = None,
      wire_signature_scheme = 1,
      wire_operation_body =
        \<lparr>wire_opcode = 7,
          wire_words = [1,1,1,0,9,0,17,17,3,2,3,1,17,0,17,7,0,9,1,17,0,0,9],
          wire_blobs = [replicate 31 0 @ [5]], wire_deadline = Deadline_Absent\<rparr>,
      wire_atomicity = 3, wire_priority = 3, wire_route_scope = 1\<rparr>"

lemma the_write_seed_selects_the_proved_product_input:
  "select_reference_write (\<lambda>_. Some (sample_request 17)) write_fixture_core =
    Some ((7,1),write_fixture_payload)"
  by code_simp

lemma the_write_seed_is_admitted_with_its_existing_layout:
  "decode_wire_core (encode_wire_core write_fixture_core) = Some write_fixture_core"
  "code_check_operation code_reference_accepts write_fixture_core = Some Unsupported_Wire_Version"
  "code_check_operation reference_accepts_write write_fixture_core = None"
  by code_simp+

definition write_fixture_integer_core where
  "write_fixture_integer_core = map integer_of_nat (encode_wire_core write_fixture_core)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms the_write_seed_selects_the_proved_product_input
      the_write_seed_is_admitted_with_its_existing_layout})
  then () else error "Unexpected oracle in the Write Core seed"
\<close>

export_code write_fixture_integer_core reference_write_vector_rows
  in SML module_name Reference_Write_Core_Seed file_prefix "reference_write_core_seed"

end

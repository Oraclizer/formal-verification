theory Reference_Write_Vector_Export
  imports "OIP_Reference_Write_ChecksV9.Reference_Write_Checks"
begin

definition reference_write_vector_rows :: "integer list list" where
  "reference_write_vector_rows = map (\<lambda>(case_number, result, stored_value, asset_version, revision).
    let status = (case result of None \<Rightarrow> [0,0,0,0]
      | Some (code, position) \<Rightarrow> [1,code,(if position = None then 0 else 1),
          (case position of None \<Rightarrow> 0 | Some offset \<Rightarrow> offset)])
    in map integer_of_nat ([case_number] @ status @ [stored_value,asset_version,revision]))
    reference_write_observation_table"

export_code reference_write_vector_rows
  in SML module_name Reference_Write_Vectors file_prefix "reference_write_vectors"

end

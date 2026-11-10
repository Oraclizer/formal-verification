theory Current_Read_Vector_Export
  imports "OIP_Current_Read_G0_V9.Current_Read_G0" "HOL-Library.Code_Target_Nat"
begin

definition current_read_vector_cases :: "(nat \<times> bool \<times> bool \<times> nat) list" where
  "current_read_vector_cases =
    [(1, True, False, 0), (2, True, True, 0), (3, False, False, 0), (4, True, False, 2)]"

definition current_read_vector_packet :: "unit \<Rightarrow> integer list" where
  "current_read_vector_packet call_unit = map integer_of_nat replay_first_bytes"

definition current_read_vector_inputs :: "unit \<Rightarrow> integer list list" where
  "current_read_vector_inputs call_unit =
    map (\<lambda>(vector_id, grant_current, advanced_prefix, visible_head).
      map integer_of_nat [vector_id, (if grant_current then 1 else 0),
        (if advanced_prefix then 1 else 0), visible_head])
      current_read_vector_cases"

fun current_read_vector_reply_fields :: "scheduled_service_reply option \<Rightarrow> nat list" where
  "current_read_vector_reply_fields None = [0,0,0,0,0,0,0]"
| "current_read_vector_reply_fields (Some (Scheduled_Endpoint (Service_Read_Result
      (Authorized_Data (Current_Cut_Value reply_cut (Units_Value units)))))) =
    [1,1,1,units,1,cut_authority_epoch reply_cut,cut_revision reply_cut]"
| "current_read_vector_reply_fields (Some (Scheduled_Endpoint (Service_Read_Result
      (Authorized_Data Product_Read_Busy)))) = [1,2,0,0,0,0,0]"
| "current_read_vector_reply_fields (Some (Scheduled_Endpoint (Service_Read_Result
      Identity_Read_Rejected))) = [1,3,0,0,0,0,0]"
| "current_read_vector_reply_fields (Some _) = [1,4,0,0,0,0,0]"

definition current_read_vector_project where
  "current_read_vector_project vector_id result =
    (case result of (read_reply, actual_cut, obs_head, obs_order, obs_core) \<Rightarrow>
      [vector_id] @ current_read_vector_reply_fields read_reply @
      [cut_authority_epoch actual_cut,cut_revision actual_cut] @
      (case obs_head of None \<Rightarrow> [0,0] | Some head_value \<Rightarrow> [1,head_value]) @
      [obs_order] @
      (case obs_core of None \<Rightarrow> [0,0]
        | Some binding_octets \<Rightarrow> [1,length binding_octets] @ binding_octets))"

definition current_read_vector_observations :: "unit \<Rightarrow> integer list list" where
  "current_read_vector_observations call_unit =
    map (\<lambda>(vector_id, grant_current, advanced_prefix, visible_head).
      map integer_of_nat (current_read_vector_project vector_id
        (current_read_g0_observe grant_current (Some visible_head)
          (if advanced_prefix then read_example_after else read_example_before))))
      current_read_vector_cases"

declare [[code drop: current_read_vector_observations]]

lemma current_read_vector_observations_code [code]:
  "current_read_vector_observations call_unit = map (map integer_of_nat)
    [[1,1,1,1,0,1,9,0,9,0,1,1,1,1,159] @ replay_first_core_bytes,
     [2,1,2,0,0,0,0,0,9,3,1,1,1,1,159] @ replay_first_core_bytes,
     [3,1,3,0,0,0,0,0,9,0,1,0,0,0,0],
     [4,0,0,0,0,0,0,0,9,0,1,0,0,0,0]]"
proof -
  have core_length: "length replay_first_core_bytes = 159"
    by (simp add: replay_first_core_bytes_def)
  show ?thesis
    by (simp only: current_read_vector_observations_def current_read_vector_cases_def
      list.map prod.case if_True if_False current_read_g0_observations
      current_read_vector_project_def current_read_vector_reply_fields.simps
      product_cut.select_convs option.case core_length append.simps)
qed

export_code current_read_vector_packet current_read_vector_inputs current_read_vector_observations
  in SML module_name OIP_Current_Read_Vectors file_prefix "oip_current_read_vectors"

thm_oracles current_read_vector_observations_code

end

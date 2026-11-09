theory Response_Code_Export
  imports "OIP_Response_Code_Extension.Response_Code_Extension"
    "HOL-Library.Code_Target_Nat"
begin

definition response_observation_flag :: "bool \<Rightarrow> nat" where
  "response_observation_flag predicate = (if predicate then 1 else 0)"

fun response_status_observation :: "code_response_status option \<Rightarrow> nat list" where
  "response_status_observation None = [0,0,0]"
| "response_status_observation (Some (Code_Known_Response kind number)) =
    [1,reference_response_kind_number kind,number]"
| "response_status_observation (Some (Code_Unknown_Response kind number)) =
    [2,reference_response_kind_number kind,number]"

definition response_code_observation :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "response_code_observation source_family_code source_operation_code encoded_words =
    (case response_result_words encoded_words of None \<Rightarrow> [0]
     | Some (call_id,kind,number,position) \<Rightarrow>
       (let committed = (position \<noteq> None);
            call_checks =
              (case family_at_number source_family_code of None \<Rightarrow> [0,0,0]
               | Some family \<Rightarrow> map response_observation_flag
                  [code_response_call_shape family source_operation_code,
                   code_response_compatible family source_operation_code kind number committed,
                   response_extended_compatible sync_response_allocations [sync_response_operation]
                     family source_operation_code kind number committed])
        in [1,fst call_id,snd call_id,reference_response_kind_number kind,number,
             response_observation_flag committed,(case position of None \<Rightarrow> 0 | Some revision \<Rightarrow> revision)] @
           response_status_observation (code_decode_response_status kind number committed) @
           response_status_observation (response_extended_status sync_response_allocations kind number committed) @
           call_checks))"

definition response_code_observe_integer :: "integer \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list" where
  "response_code_observe_integer source_family_code source_operation_code encoded_words =
    (if list_all (\<lambda>word. 0 \<le> word \<and> word < 2 ^ 64)
          (source_family_code # source_operation_code # encoded_words)
     then map integer_of_nat (response_code_observation (nat_of_integer source_family_code)
            (nat_of_integer source_operation_code) (map nat_of_integer encoded_words))
     else [0])"

definition response_allocation_observation :: "response_allocations \<Rightarrow> nat list" where
  "response_allocation_observation allocations =
    map response_observation_flag
      [distinct (map fst allocations), response_allocations_fresh allocations,
       response_allocations_in_range allocations, response_allocations_valid allocations]"

definition response_allocation_observe_integer :: "integer \<Rightarrow> integer list" where
  "response_allocation_observe_integer variant =
    (if variant = 0 then map integer_of_nat (response_allocation_observation sync_response_allocations)
     else if variant = 1 then map integer_of_nat
       (response_allocation_observation (response_replace_number 41 40 sync_response_allocations))
     else if variant = 2 then map integer_of_nat
       (response_allocation_observation (response_replace_number 29 28 sync_response_allocations))
     else if variant = 3 then map integer_of_nat
       (response_allocation_observation (response_change_commit 29 False sync_response_allocations))
     else [])"

lemma response_observation_reads_the_actual_result_words:
  assumes "response_result_words encoded_words = Some (call_id,kind,number,position)"
  shows "take 7 (response_code_observation source_family_code source_operation_code encoded_words) =
    [1,fst call_id,snd call_id,reference_response_kind_number kind,number,
      response_observation_flag (position \<noteq> None),(case position of None \<Rightarrow> 0 | Some revision \<Rightarrow> revision)]"
  using assms by (simp add: response_code_observation_def Let_def)

lemma response_observation_rejects_an_unreadable_result_word_sequence:
  assumes "response_result_words encoded_words = None"
  shows "response_code_observation source_family_code source_operation_code encoded_words = [0]"
  using assms by (simp add: response_code_observation_def)

thm_oracles response_observation_reads_the_actual_result_words response_observation_rejects_an_unreadable_result_word_sequence

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms response_observation_reads_the_actual_result_words
      response_observation_rejects_an_unreadable_result_word_sequence})
  then () else error "Unexpected oracle in response code observations"
\<close>

export_code response_code_observe_integer response_allocation_observe_integer
  in SML module_name OIP_Response_Code_Extension file_prefix "oip_response_code_extension"

end

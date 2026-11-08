theory Wire_Code_Response_List_Atomicity
  imports Wire_Code_Response_Full_Check
begin

definition code_response_list_atomicity :: "nat list \<Rightarrow> nat option" where
  "code_response_list_atomicity = (\<lambda>oip_exec_modes.
    case oip_exec_modes of [] \<Rightarrow> None
     | oip_exec_first # oip_exec_rest \<Rightarrow> Some (fold min oip_exec_rest oip_exec_first))"

lemma the_list_atomicity_is_the_existing_list_boundary_value:
  fixes oip_exec_modes :: "nat list"
  shows "code_response_list_atomicity oip_exec_modes = code_rbound_atomicity oip_exec_modes"
proof (cases oip_exec_modes)
  case Nil
  then show ?thesis by (simp add: code_response_list_atomicity_def code_rbound_atomicity_def)
next
  case (Cons oip_exec_first oip_exec_rest)
  have "code_response_list_atomicity oip_exec_modes = Some (fold min oip_exec_rest oip_exec_first)"
    using Cons by (simp add: code_response_list_atomicity_def)
  also have "... = Some (Min (set (oip_exec_first # oip_exec_rest)))"
    by (rule arg_cong[where f=Some], rule sym, rule Min.set_eq_fold)
  also have "... = code_rbound_atomicity oip_exec_modes"
    using Cons by (simp add: code_rbound_atomicity_def)
  finally show ?thesis .
qed

lemma the_constructed_channel_uses_exactly_the_list_atomicity:
  fixes oip_exec_rows :: "nat list list"
  shows "response_fixed_atomicity (code_full_channel oip_exec_rows) =
    code_response_list_atomicity (oip_exec_rows ! 2)"
proof -
  have source: "code_rbound_atomicity (oip_exec_rows ! 2) =
      response_fixed_atomicity (code_full_channel oip_exec_rows)"
    by (rule the_boundary_mode_is_the_existing_finite_channel_atomicity)
      (simp add: code_full_channel_def code_full_profile_def)
  show ?thesis
    using source the_list_atomicity_is_the_existing_list_boundary_value[of "oip_exec_rows ! 2"] by simp
qed

lemma a_constructed_context_has_the_same_exact_atomicity:
  fixes oip_exec_rows :: "nat list list"
    and oip_exec_parameters_clock oip_exec_signing_clock :: "nat option"
  shows "response_fixed_atomicity (full_response_channel
      (code_full_build_context oip_exec_rows oip_exec_parameters_clock oip_exec_signing_clock)) =
    code_response_list_atomicity (oip_exec_rows ! 2)"
  by (simp add: code_full_build_context_def the_constructed_channel_uses_exactly_the_list_atomicity)

lemma a_parsed_context_has_the_same_exact_atomicity:
  fixes oip_exec_rows :: "nat list list" and oip_exec_context :: code_response_full_context
  assumes "code_full_parse_context oip_exec_rows = Some oip_exec_context"
  shows "response_fixed_atomicity (full_response_channel oip_exec_context) =
    code_response_list_atomicity (oip_exec_rows ! 2)"
proof -
  obtain oip_exec_parameters_clock oip_exec_signing_clock where built:
      "oip_exec_context = code_full_build_context oip_exec_rows oip_exec_parameters_clock oip_exec_signing_clock"
    using assms by (auto simp: code_full_parse_context_def bind_eq_Some_conv
      split: if_splits option.splits)
  show ?thesis by (simp add: built a_constructed_context_has_the_same_exact_atomicity)
qed

lemma an_integer_context_has_the_same_exact_atomicity:
  fixes oip_exec_rows :: "integer list list" and oip_exec_context :: code_response_full_context
  assumes "code_full_context_from_integer oip_exec_rows = Some oip_exec_context"
  shows "response_fixed_atomicity (full_response_channel oip_exec_context) =
    code_response_list_atomicity ((map (map nat_of_integer) oip_exec_rows) ! 2)"
proof -
  have parsed: "code_full_parse_context (map (map nat_of_integer) oip_exec_rows) = Some oip_exec_context"
    using assms by (auto simp: code_full_context_from_integer_def split: if_splits)
  show ?thesis by (rule a_parsed_context_has_the_same_exact_atomicity[OF parsed])
qed

lemma a_parsed_sender_supplies_the_same_exact_atomicity:
  fixes oip_exec_rows :: "integer list list" and oip_exec_mode :: integer
    and oip_exec_reply oip_exec_retained oip_exec_original :: "integer list"
    and oip_exec_retained_present :: bool
    and oip_exec_hash_rows oip_exec_sign_rows oip_exec_verify_rows :: "integer list list"
    and oip_exec_context :: code_response_full_context and oip_exec_observation :: "response_fixed_observation option"
    and oip_exec_bytes :: wire_bytes and oip_exec_hashes :: code_full_hash_table
    and oip_exec_signatures :: code_full_sign_table and oip_exec_verifications :: code_full_verify_table
  assumes "code_full_sender_input oip_exec_rows oip_exec_mode oip_exec_reply oip_exec_retained_present oip_exec_retained
    oip_exec_original oip_exec_hash_rows oip_exec_sign_rows oip_exec_verify_rows =
      Some (oip_exec_context,oip_exec_observation,oip_exec_bytes,oip_exec_hashes,oip_exec_signatures,oip_exec_verifications)"
  shows "response_fixed_atomicity (full_response_channel oip_exec_context) =
    code_response_list_atomicity ((map (map nat_of_integer) oip_exec_rows) ! 2)"
proof -
  have parsed: "code_full_context_from_integer oip_exec_rows = Some oip_exec_context"
    using assms by (auto simp: code_full_sender_input_def bind_eq_Some_conv
      split: if_splits option.splits prod.splits)
  show ?thesis by (rule an_integer_context_has_the_same_exact_atomicity[OF parsed])
qed

definition code_response_list_atomicity_integer :: "integer list \<Rightarrow> (integer \<times> bool \<times> integer)" where
  "code_response_list_atomicity_integer = (\<lambda>oip_exec_modes.
    if \<not> code_integer_u64_values oip_exec_modes then (-1,False,0)
    else case code_response_list_atomicity (map nat_of_integer oip_exec_modes) of
      None \<Rightarrow> (0,False,0) | Some oip_exec_mode \<Rightarrow> (0,True,integer_of_nat oip_exec_mode))"

text \<open>
  The list is the finite provider getter already used to construct the
  channel. Fold-min keeps every value, duplicate and ordering case without
  a nat finite/enum instance. The conditional parser facts above are derived
  from the existing constructors, not new assumptions on accepted inputs.
  No existing definition, code equation, target instance or library changes.
\<close>

end

theory Wire_Code_Precheck_Canary
  imports Wire_Code_Prechecks
begin

lemma an_entire_declared_core_can_select_another_version_before_later_checks:
  "code_declared_version [10,5,8,7,208,1,0] = Some 7"
  "code_check_declared_version [10,5,8,7,208,1,0] 64 = Some Unsupported_Wire_Version"
  by code_simp+

lemma a_version_prefix_in_a_truncated_core_is_not_a_declared_version:
  "code_declared_version [10,5,8,7] = None"
  "code_check_declared_version [10,5,8,7] 64 = None"
  by code_simp+

lemma nonshortest_packet_tags_and_lengths_do_not_select_a_version:
  "code_declared_version [138,0,2,8,7] = None"
  "code_declared_version [10,130,0,8,7] = None"
  by code_simp+

lemma nonshortest_core_tags_and_versions_do_not_select_a_version:
  "code_declared_version [10,3,136,0,7] = None"
  "code_declared_version [10,3,8,135,0] = None"
  by code_simp+

lemma a_different_first_packet_or_core_tag_does_not_select_a_version:
  "code_declared_version [18,2,8,7] = None"
  "code_declared_version [10,2,16,7] = None"
  by code_simp+

lemma lack_of_a_selector_is_not_an_acceptance_of_a_current_version:
  assumes "length bytes \<le> max_frame" "code_declared_version bytes = None"
  shows "code_check_declared_version bytes max_frame = None"
  using assms by (simp add: code_check_declared_version_def)

lemma a_large_frame_still_precedes_an_otherwise_complete_version_selector:
  "code_check_declared_version [10,5,8,7,208,1,0] 6 = Some Invalid_Wire_Format"
  by (simp add: code_check_declared_version_def)

end

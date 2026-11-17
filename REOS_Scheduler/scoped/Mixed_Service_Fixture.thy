theory Mixed_Service_Fixture
  imports Main
begin

text \<open>Small synthetic inputs for the mixed-service examples.
  The observation tags are illustrative values.\<close>

definition fixture_authority :: "nat" where
  "fixture_authority = 12"

definition fixture_time_at_start :: "nat" where
  "fixture_time_at_start = 23"

definition fixture_ordinary_epoch :: "nat" where
  "fixture_ordinary_epoch = 7"

definition fixture_ordinary_identity :: "nat" where
  "fixture_ordinary_identity = 201"

definition fixture_delivered_identity :: "nat" where
  "fixture_delivered_identity = 201"

definition fixture_ordinary_digest :: "nat" where
  "fixture_ordinary_digest = 77"

definition fixture_ordinary_bytes :: "nat list" where
  "fixture_ordinary_bytes = [11,22,33]"

definition fixture_delivered_bytes :: "nat list" where
  "fixture_delivered_bytes = [11,22,33]"

definition fixture_case_a :: "nat" where
  "fixture_case_a = 23"

definition fixture_case_b :: "nat" where
  "fixture_case_b = 29"

definition fixture_actor_a :: "nat" where
  "fixture_actor_a = 202"

definition fixture_actor_b :: "nat" where
  "fixture_actor_b = 203"

definition fixture_epoch_a :: "nat" where
  "fixture_epoch_a = 8"

definition fixture_epoch_b :: "nat" where
  "fixture_epoch_b = 10"

definition fixture_priority_a :: "nat" where
  "fixture_priority_a = 2"

definition fixture_priority_b :: "nat" where
  "fixture_priority_b = 5"

definition fixture_level_a :: "nat" where
  "fixture_level_a = 2"

definition fixture_level_b :: "nat" where
  "fixture_level_b = 3"

definition fixture_limit_a :: "nat" where
  "fixture_limit_a = 7"

definition fixture_limit_b :: "nat" where
  "fixture_limit_b = 9"

definition fixture_raise_a :: "nat" where
  "fixture_raise_a = 4"

definition fixture_raise_b :: "nat" where
  "fixture_raise_b = 6"

definition fixture_new_epoch_a :: "nat" where
  "fixture_new_epoch_a = 11"

definition fixture_race_epoch_a :: "nat" where
  "fixture_race_epoch_a = 13"

definition fixture_new_epoch_b :: "nat" where
  "fixture_new_epoch_b = 10"

definition fixture_served_level_a :: "nat" where
  "fixture_served_level_a = 2"

definition fixture_served_level_b :: "nat" where
  "fixture_served_level_b = 6"

definition fixture_before_selected :: "nat" where
  "fixture_before_selected = 202"

definition fixture_after_selected :: "nat" where
  "fixture_after_selected = 203"

definition fixture_priority_receipt_identity :: "nat" where
  "fixture_priority_receipt_identity = 203"

definition fixture_a_status :: "nat list" where
  "fixture_a_status = [1]"

definition fixture_a_receipt_absent :: "bool" where
  "fixture_a_receipt_absent = True"

definition fixture_conflict :: "nat list" where
  "fixture_conflict = [2]"

definition fixture_recovery :: "nat list" where
  "fixture_recovery = [3]"

definition fixture_replay :: "nat list" where
  "fixture_replay = [4]"

definition fixture_first_lane :: "nat list" where
  "fixture_first_lane = [5]"

definition fixture_second_lane :: "nat list" where
  "fixture_second_lane = [6]"

definition fixture_exact_regulation_receipt :: "nat list list" where
  "fixture_exact_regulation_receipt = [[10,20],[30,40]]"

definition fixture_recovery_receipt :: "nat list list" where
  "fixture_recovery_receipt = [[10,20],[30,40]]"

definition fixture_replay_receipt :: "nat list list" where
  "fixture_replay_receipt = [[10,20],[30,40]]"

definition fixture_reopened_regulation_receipt :: "nat list list" where
  "fixture_reopened_regulation_receipt = [[10,20],[30,40]]"

definition fixture_receipts_match :: "bool" where
  "fixture_receipts_match = (fixture_exact_regulation_receipt = fixture_recovery_receipt \<and> fixture_exact_regulation_receipt = fixture_replay_receipt \<and> fixture_exact_regulation_receipt = fixture_reopened_regulation_receipt)"

end

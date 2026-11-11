theory P19_Threshold_Raw_G0
  imports P19_Threshold_G0
begin

text \<open>
  Pending local G0 extension: raw payload nonvacuity and mutation reach.
  It does not change the threshold rules or the symbolic crypto boundary.
\<close>

lemma p19_encoded_word_octets [simp]: "wire_octets (p19_word i)"
  using put_le_octets_are_valid_bytes[where width = 8 and n = i]
  by (simp add: wire_octets_def)

lemma p19_empty_octets [simp]: "wire_octets []"
  by (simp add: wire_octets_def)

lemma p19_read_exact_big_endian_prefix:
  assumes "i < 2^64"
  shows "p19_read_word (p19_word i @ suffix) = i"
proof -
  have range: "i < 256^8" using assms by simp
  show ?thesis
    using get_le_octets_reads_every_representable_word[OF range]
    by (simp add: take_append)
qed

lemma p19_parse_encoded_records:
  assumes "\<forall>(i,s) \<in> set votes. i < 2^64 \<and> length s = 64"
  shows "p19_parse_records (length votes)
    (concat (map (\<lambda>(i,s). p19_word i @ s) votes) @ suffix) = votes"
  using assms
proof (induction votes arbitrary: suffix)
  case Nil
  then show ?case by simp
next
  case (Cons vote votes)
  obtain i s where pair: "vote = (i,s)" by (cases vote) auto
  have range: "i < 2^64" and width: "length s = 64"
    and tail: "\<forall>(j,t) \<in> set votes. j < 2^64 \<and> length t = 64"
    using Cons.prems by (auto simp: pair)
  have rest: "p19_parse_records (length votes)
    (concat (map (\<lambda>(j,t). p19_word j @ t) votes) @ suffix) = votes"
    by (rule Cons.IH[OF tail])
  have word: "get_le_octets (put_le_octets 8 i) = i"
    by (rule get_le_octets_reads_every_representable_word) (use range in simp)
  show ?case using rest range width word
    by (simp add: pair p19_read_exact_big_endian_prefix append_assoc take_append drop_append)
qed

lemma p19_encoded_payload_length:
  assumes "\<forall>(i,s) \<in> set votes. length s = 64"
  shows "length (p19_payload_bytes votes) = 8 + 72 * length votes"
proof -
  have records: "length (concat (map (\<lambda>(i,s). p19_word i @ s) votes)) =
      72 * length votes"
    using assms by (induction votes) (auto simp: algebra_simps split: prod.splits)
  show ?thesis using records by (simp add: p19_payload_bytes_def)
qed

lemma p19_encoded_payload_octets:
  assumes "\<forall>(i,s) \<in> set votes. wire_octets s"
  shows "wire_octets (p19_payload_bytes votes)"
proof -
  have records: "wire_octets (concat (map (\<lambda>(i,s). p19_word i @ s) votes))"
    using assms by (induction votes) (auto split: prod.splits)
  show ?thesis using records by (simp add: p19_payload_bytes_def)
qed

theorem p19_decode_encoded_payload:
  assumes entries: "\<forall>(i,s) \<in> set votes. i < 2^64 \<and> length s = 64 \<and> wire_octets s"
    and count: "length votes < 2^64"
    and members: "length votes \<le> roster_size"
    and cap: "8 + 72 * length votes \<le> max_signature"
  shows "p19_decode_payload max_signature roster_size (p19_payload_bytes votes) = Some votes"
proof -
  have widths: "\<forall>(i,s) \<in> set votes. length s = 64"
    and byte_entries: "\<forall>(i,s) \<in> set votes. wire_octets s"
    and records: "\<forall>(i,s) \<in> set votes. i < 2^64 \<and> length s = 64"
    using entries by auto
  have raw_length: "length (p19_payload_bytes votes) = 8 + 72 * length votes"
    by (rule p19_encoded_payload_length[OF widths])
  have octets: "wire_octets (p19_payload_bytes votes)"
    by (rule p19_encoded_payload_octets[OF byte_entries])
  have head: "p19_read_word (p19_payload_bytes votes) = length votes"
    unfolding p19_payload_bytes_def by (rule p19_read_exact_big_endian_prefix[OF count])
  have tail: "drop 8 (p19_payload_bytes votes) =
    concat (map (\<lambda>(i,s). p19_word i @ s) votes)"
    by (simp add: p19_payload_bytes_def drop_append)
  have parsed: "p19_parse_records (length votes) (drop 8 (p19_payload_bytes votes)) = votes"
    using p19_parse_encoded_records[OF records, where suffix = "[]"]
    by (simp add: tail)
  show ?thesis using raw_length octets head parsed count members cap
    by (simp add: p19_decode_payload_def Let_def)
qed

lemma p19_good_raw_payload_roundtrip:
  "p19_decode_payload 4096 2 (p19_payload_bytes p19_good_votes) = Some p19_good_votes"
  by (rule p19_decode_encoded_payload)
    (auto simp: p19_good_votes_def wire_octets_def)

lemma p19_alias_raw_payload_roundtrip:
  "p19_decode_payload 4096 2 (p19_payload_bytes p19_alias_votes) = Some p19_alias_votes"
  by (rule p19_decode_encoded_payload)
    (auto simp: p19_alias_votes_def wire_octets_def)

lemma p19_alias_selected_roster:
  "p19_select (p19_test_registry p19_alias_roster) p19_test_core = Some p19_alias_roster"
  by (simp add: p19_select_def p19_test_registry_def p19_core_slot_def
      p19_matches_core_def p19_test_core_def p19_alias_roster_def p19_test_roster_def)

lemma p19_test_member_counts [simp]:
  "length (p19_members p19_test_roster) = 2"
  "length (p19_members p19_alias_roster) = 2"
  by (simp_all add: p19_test_roster_def p19_alias_roster_def)

theorem p19_raw_payload_positive_and_alias_negative:
  "p19_threshold_ok (\<lambda>_. True) p19_symbolic_strict (p19_test_registry p19_test_roster)
      4096 p19_test_core (p19_payload_bytes p19_good_votes)"
  "\<not> p19_threshold_ok (\<lambda>_. True) p19_symbolic_strict (p19_test_registry p19_alias_roster)
      4096 p19_test_core (p19_payload_bytes p19_alias_votes)"
  using p19_distinct_key_positive p19_key_alias_removal_counterexample
    p19_good_raw_payload_roundtrip p19_alias_raw_payload_roundtrip
  by (simp_all add: p19_threshold_ok_def p19_positive_selected_roster p19_alias_selected_roster)

definition p19_mutant_without_key_alias where
  "p19_mutant_without_key_alias key_ok strict registry cap c raw \<longleftrightarrow>
    (case p19_select registry c of None \<Rightarrow> False | Some r \<Rightarrow>
       p19_roster_shape key_ok r \<and>
       (case p19_decode_payload cap (length (p19_members r)) raw of
         None \<Rightarrow> False | Some votes \<Rightarrow>
           p19_votes_ok strict r (envelope_signing_bytes c) votes))"

theorem p19_removing_only_alias_guard_accepts_after_raw_parse:
  "p19_mutant_without_key_alias (\<lambda>_. True) p19_symbolic_strict
    (p19_test_registry p19_alias_roster) 4096 p19_test_core (p19_payload_bytes p19_alias_votes)"
  using p19_key_alias_removal_counterexample p19_alias_raw_payload_roundtrip
  by (simp add: p19_mutant_without_key_alias_def p19_alias_selected_roster)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms p19_decode_encoded_payload
      p19_raw_payload_positive_and_alias_negative
      p19_removing_only_alias_guard_accepts_after_raw_parse})
  then () else error "Unexpected oracle in raw threshold G0 candidate"
\<close>

end

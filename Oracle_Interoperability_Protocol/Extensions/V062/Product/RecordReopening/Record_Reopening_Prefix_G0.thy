theory Record_Reopening_Prefix_G0
  imports "OIP_Record_Reopening.Reference_Recovery_Code" "HOL-Library.Code_Target_Nat"
begin

section \<open>Selected byte prefixes before product-image interpretation\<close>

text \<open>This layer computes byte addressing and the guards around external digest,
  parse and canonical-encode functions. It does not authenticate a supplied head,
  prove the external functions, validate a product image, or prove physical storage.
  No archive-bound or journal-related Boolean is an input. Large journal bytes are
  evaluated only by the exported program, outside kernel simplification.\<close>

type_synonym rr_bytes = "nat list"
type_synonym rr_address = "rr_bytes native_address"

datatype rr_prefix_mode = RR_Archive | RR_Live

fun rr_octets :: "rr_bytes \<Rightarrow> bool" where
  "rr_octets [] = True"
| "rr_octets (byte # rest) = (byte < 256 \<and> rr_octets rest)"

record rr_decoded_record =
  rr_record_profile :: recovery_profile
  rr_record_sequence :: nat
  rr_record_parent :: "rr_address option"
  rr_record_token :: nat

definition rr_u64_max :: nat where
  "rr_u64_max = 18446744073709551615"

definition rr_checked_end :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "rr_checked_end offset count =
    (if offset \<le> rr_u64_max \<and> count \<le> rr_u64_max \<and>
        offset + count \<le> rr_u64_max then Some (offset + count) else None)"

definition rr_ends_by :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "rr_ends_by offset count bound =
    (case rr_checked_end offset count of None \<Rightarrow> False | Some end_offset \<Rightarrow> end_offset \<le> bound)"

definition rr_slice :: "rr_bytes \<Rightarrow> rr_address \<Rightarrow> rr_bytes" where
  "rr_slice raw head = take (address_length head) (drop (address_offset head) raw)"

definition rr_span_ok :: "rr_bytes \<Rightarrow> rr_address \<Rightarrow> bool" where
  "rr_span_ok raw head \<longleftrightarrow>
    0 < address_length head \<and> address_sequence head \<le> rr_u64_max \<and>
    rr_octets (rr_slice raw head) \<and>
    rr_ends_by (address_offset head) (address_length head) (length raw)"

fun rr_parent_ok :: "rr_address \<Rightarrow> rr_address option \<Rightarrow> bool" where
  "rr_parent_ok head None = (address_sequence head = 0)"
| "rr_parent_ok head (Some parent) =
    (address_profile parent = address_profile head \<and>
     address_sequence parent < rr_u64_max \<and>
     Suc (address_sequence parent) = address_sequence head \<and>
     rr_ends_by (address_offset parent) (address_length parent) (address_offset head))"

definition rr_record_checks ::
  "(nat \<Rightarrow> rr_bytes option) \<Rightarrow> rr_address \<Rightarrow> rr_bytes \<Rightarrow> rr_decoded_record \<Rightarrow> bool" where
  "rr_record_checks encode head selected record \<longleftrightarrow>
    rr_record_profile record = address_profile head \<and>
    rr_record_sequence record = address_sequence head \<and>
    encode (rr_record_token record) = Some selected \<and>
    rr_parent_ok head (rr_record_parent record)"

definition rr_read_record ::
  "(rr_bytes \<Rightarrow> rr_bytes option) \<Rightarrow> (rr_bytes \<Rightarrow> rr_decoded_record option) \<Rightarrow>
   (nat \<Rightarrow> rr_bytes option) \<Rightarrow> rr_bytes \<Rightarrow> rr_address \<Rightarrow> rr_decoded_record option" where
  "rr_read_record digest parse encode raw head =
    (let selected = rr_slice raw head in
     if \<not> rr_span_ok raw head \<or> digest selected \<noteq> Some (address_hash head) then None
     else case parse selected of None \<Rightarrow> None
       | Some record \<Rightarrow> if rr_record_checks encode head selected record then Some record else None)"

definition rr_read_record_without_digest where
  "rr_read_record_without_digest digest parse encode raw head =
    (let selected = rr_slice raw head in
     if \<not> rr_span_ok raw head then None
     else case parse selected of None \<Rightarrow> None
       | Some record \<Rightarrow> if rr_record_checks encode head selected record then Some record else None)"

definition rr_prefix_ok ::
  "rr_prefix_mode \<Rightarrow> nat \<Rightarrow> recovery_profile \<Rightarrow> rr_address \<Rightarrow>
   nat \<Rightarrow> rr_bytes \<Rightarrow> (rr_bytes \<Rightarrow> rr_bytes option) \<Rightarrow> rr_bytes \<Rightarrow> bool" where
  "rr_prefix_ok mode limit profile head prefix_count prefix_hash digest raw \<longleftrightarrow>
    0 < limit \<and> 0 < address_length head \<and> address_profile head = profile \<and>
    (case rr_checked_end (address_offset head) (address_length head) of None \<Rightarrow> False
     | Some end_offset \<Rightarrow> prefix_count = end_offset \<and> end_offset \<le> limit \<and>
       (case mode of RR_Archive \<Rightarrow> length raw = end_offset | RR_Live \<Rightarrow> end_offset \<le> length raw) \<and>
       rr_octets (take end_offset raw) \<and> digest (take end_offset raw) = Some prefix_hash)"

definition rr_select_with where
  "rr_select_with read_record mode limit profile head prefix_count prefix_hash digest raw =
    (if rr_prefix_ok mode limit profile head prefix_count prefix_hash digest raw then
      map_option (\<lambda>record. (head, rr_slice raw head, record)) (read_record raw head)
     else None)"

definition rr_select where
  "rr_select digest parse encode mode limit profile head prefix_count prefix_hash raw =
    rr_select_with (rr_read_record digest parse encode) mode limit profile head prefix_count prefix_hash digest raw"

definition rr_select_without_record_digest where
  "rr_select_without_record_digest digest parse encode mode limit profile head prefix_count prefix_hash raw =
    rr_select_with (rr_read_record_without_digest digest parse encode) mode limit profile head prefix_count prefix_hash digest raw"

text \<open>The floor walk is a separate composed stage. Its input is an address,
  not a list of asserted reachable ancestors. Each visited record is read from raw
  bytes. The bound is the starting sequence plus one. Byte gaps are allowed.\<close>

fun rr_floor_walk ::
  "(rr_bytes \<Rightarrow> rr_address \<Rightarrow> rr_decoded_record option) \<Rightarrow>
   rr_bytes \<Rightarrow> rr_address \<Rightarrow> nat \<Rightarrow> rr_address \<Rightarrow> bool" where
  "rr_floor_walk read_record raw floor_head 0 head = False"
| "rr_floor_walk read_record raw floor_head (Suc fuel) head =
    (if address_profile head \<noteq> address_profile floor_head \<or>
        address_sequence head < address_sequence floor_head then False
     else case read_record raw head of None \<Rightarrow> False
       | Some record \<Rightarrow> if head = floor_head then True
           else case rr_record_parent record of None \<Rightarrow> False
             | Some parent \<Rightarrow> rr_floor_walk read_record raw floor_head fuel parent)"

definition rr_native_view :: "rr_address \<Rightarrow> rr_bytes \<Rightarrow> (rr_bytes, rr_bytes) native_journal_view" where
  "rr_native_view head selected =
    \<lparr>native_current = Some head,
     native_records = (\<lambda>address. if address = head then Some selected else None)\<rparr>"

lemma rr_checked_end_success_iff:
  "rr_checked_end offset count = Some end_position \<longleftrightarrow>
    offset \<le> rr_u64_max \<and> count \<le> rr_u64_max \<and>
    offset + count \<le> rr_u64_max \<and> end_position = offset + count"
  by (auto simp: rr_checked_end_def)

lemma rr_checked_end_overflow:
  "rr_u64_max < offset + count \<Longrightarrow> rr_checked_end offset count = None"
  by (simp add: rr_checked_end_def)

lemma rr_checked_span_has_the_exact_slice_length:
  assumes "rr_span_ok raw head"
  shows "length (rr_slice raw head) = address_length head"
proof -
  have bound: "address_offset head + address_length head \<le> length raw"
    using assms by (auto simp: rr_span_ok_def rr_ends_by_def rr_checked_end_def split: if_splits)
  have "address_length head \<le> length raw - address_offset head" using bound by arith
  then show ?thesis by (simp add: rr_slice_def min_def)
qed

lemma rr_read_success_exposes_computed_guards:
  assumes "rr_read_record digest parse encode raw head = Some record"
  shows "rr_span_ok raw head"
    "digest (rr_slice raw head) = Some (address_hash head)"
    "parse (rr_slice raw head) = Some record"
    "encode (rr_record_token record) = Some (rr_slice raw head)"
    "rr_record_profile record = address_profile head"
    "rr_record_sequence record = address_sequence head"
    "rr_parent_ok head (rr_record_parent record)"
  using assms by (auto simp: rr_read_record_def rr_record_checks_def Let_def split: option.splits if_splits)

theorem checked_selected_prefix_supplies_the_exact_native_address:
  assumes selected: "rr_select digest parse encode mode limit profile head count hash raw = Some (address, bytes, record)"
  shows "address = head"
    "bytes = rr_slice raw head"
    "length bytes = address_length head"
    "address_profile head = profile"
    "rr_record_profile record = profile"
    "rr_record_sequence record = address_sequence head"
    "digest bytes = Some (address_hash head)"
    "parse bytes = Some record"
    "encode (rr_record_token record) = Some bytes"
    "model_head_of address = model_head_of head"
proof -
  have at: "address = head" "bytes = rr_slice raw head"
    and read: "rr_read_record digest parse encode raw head = Some record"
    and prefix: "rr_prefix_ok mode limit profile head count hash digest raw"
    using selected by (auto simp: rr_select_def rr_select_with_def split: option.splits if_splits)
  have p: "address_profile head = profile" using prefix by (simp add: rr_prefix_ok_def)
  note checked = rr_read_success_exposes_computed_guards[OF read]
  show "address = head" by (rule at(1))
  show "bytes = rr_slice raw head" by (rule at(2))
  show "length bytes = address_length head"
    using rr_checked_span_has_the_exact_slice_length[OF checked(1)] at by simp
  show "address_profile head = profile" by (rule p)
  show "rr_record_profile record = profile" using checked(5) p by simp
  show "rr_record_sequence record = address_sequence head" by (rule checked(6))
  show "digest bytes = Some (address_hash head)" using checked(2) at by simp
  show "parse bytes = Some record" using checked(3) at by simp
  show "encode (rr_record_token record) = Some bytes" using checked(4) at by simp
  show "model_head_of address = model_head_of head" using at by simp
qed

lemma rr_archive_exact_length:
  "rr_prefix_ok RR_Archive limit profile head count hash digest raw \<Longrightarrow> length raw = count"
  by (auto simp: rr_prefix_ok_def split: option.splits)

lemma rr_live_prefix_survives_suffix:
  assumes "rr_prefix_ok RR_Live limit profile head count hash digest raw"
  shows "rr_prefix_ok RR_Live limit profile head count hash digest (raw @ suffix)"
  using assms by (auto simp: rr_prefix_ok_def take_append split: option.splits)

lemma rr_floor_success_reads_the_exact_floor:
  assumes "rr_floor_walk read_record raw floor_head fuel head"
  shows "\<exists>record. read_record raw floor_head = Some record"
  using assms
proof (induction fuel arbitrary: head)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  then show ?case by (auto split: option.splits if_splits)
qed

lemma rr_archive_rejects_nonempty_suffix:
  assumes accepted: "rr_prefix_ok RR_Archive limit profile head count hash digest raw"
    and suffix: "suffix \<noteq> []"
  shows "\<not> rr_prefix_ok RR_Archive limit profile head count hash digest (raw @ suffix)"
  using rr_archive_exact_length[OF accepted] suffix
    rr_archive_exact_length[of limit profile head count hash digest "raw @ suffix"] by auto

lemma rr_native_view_reuses_the_existing_exact_readback:
  "native_confirm_reply (rr_native_view head bytes) head expected reply =
    (if bytes = expected then Some reply else None)"
  by (simp add: native_confirm_reply_def rr_native_view_def)

lemma rr_reopen_view_uses_the_checked_profile:
  assumes "address_profile head = profile"
  shows "native_reopen_view True False Native_Direct profile (rr_native_view head bytes) = Some bytes"
  using assms by (simp add: native_reopen_view_def rr_native_view_def)

lemma rr_same_address_different_bytes_cannot_release_the_expected_reply:
  "bytes \<noteq> expected \<Longrightarrow> native_confirm_reply (rr_native_view head bytes) head expected reply = None"
  by (simp add: rr_native_view_reuses_the_existing_exact_readback)

section \<open>Small normal and single-removal witnesses\<close>

definition rr_test_profile :: recovery_profile where
  "rr_test_profile = \<lparr>recovery_deployment = 7, recovery_format = 1, recovery_authority_profile = 99\<rparr>"

definition rr_test_head :: rr_address where
  "rr_test_head = \<lparr>address_profile = rr_test_profile, address_sequence = 0,
    address_offset = 0, address_length = 2, address_hash = [7,8]\<rparr>"

definition rr_test_record :: "nat \<Rightarrow> rr_decoded_record" where
  "rr_test_record token = \<lparr>rr_record_profile = rr_test_profile, rr_record_sequence = 0,
    rr_record_parent = None, rr_record_token = token\<rparr>"

definition rr_test_parse :: "rr_bytes \<Rightarrow> rr_decoded_record option" where
  "rr_test_parse bytes = (if bytes = [7,8] then Some (rr_test_record 0)
    else if bytes = [7,9] then Some (rr_test_record 1) else None)"

definition rr_test_encode :: "nat \<Rightarrow> rr_bytes option" where
  "rr_test_encode token = (if token = 0 then Some [7,8] else if token = 1 then Some [7,9] else None)"

lemma rr_normal_archive_witness:
  "rr_select Some rr_test_parse rr_test_encode RR_Archive 10 rr_test_profile rr_test_head 2 [7,8] [7,8] =
    Some (rr_test_head,[7,8],rr_test_record 0)"
  by (simp add: rr_select_def rr_select_with_def rr_prefix_ok_def rr_read_record_def
      rr_span_ok_def rr_ends_by_def rr_checked_end_def rr_slice_def rr_record_checks_def
      rr_test_head_def rr_test_parse_def rr_test_encode_def rr_test_record_def rr_u64_max_def Let_def)

lemma rr_live_suffix_and_archive_length_removal_witness:
  "rr_select Some rr_test_parse rr_test_encode RR_Live 10 rr_test_profile rr_test_head 2 [7,8] [7,8,0] =
    Some (rr_test_head,[7,8],rr_test_record 0)"
  "rr_select Some rr_test_parse rr_test_encode RR_Archive 10 rr_test_profile rr_test_head 2 [7,8] [7,8,0] = None"
  by (simp_all add: rr_select_def rr_select_with_def rr_prefix_ok_def rr_read_record_def
      rr_span_ok_def rr_ends_by_def rr_checked_end_def rr_slice_def rr_record_checks_def
      rr_test_head_def rr_test_parse_def rr_test_encode_def rr_test_record_def rr_u64_max_def Let_def)

lemma rr_same_address_record_digest_single_removal_witness:
  "rr_select Some rr_test_parse rr_test_encode RR_Archive 10 rr_test_profile rr_test_head 2 [7,9] [7,9] = None"
  "rr_select_without_record_digest Some rr_test_parse rr_test_encode RR_Archive 10 rr_test_profile rr_test_head 2 [7,9] [7,9] =
    Some (rr_test_head,[7,9],rr_test_record 1)"
  by (simp_all add: rr_select_def rr_select_without_record_digest_def rr_select_with_def
      rr_prefix_ok_def rr_read_record_def rr_read_record_without_digest_def rr_span_ok_def
      rr_ends_by_def rr_checked_end_def rr_slice_def rr_record_checks_def
      rr_test_head_def rr_test_parse_def rr_test_encode_def rr_test_record_def rr_u64_max_def Let_def)

definition rr_address_without_length where
  "rr_address_without_length (head::rr_address) =
    (address_profile head, address_sequence head, address_offset head, address_hash head)"

lemma rr_address_length_single_removal_witness:
  "rr_address_without_length rr_test_head = rr_address_without_length (rr_test_head\<lparr>address_length := 3\<rparr>)"
  "model_head_of rr_test_head \<noteq> model_head_of (rr_test_head\<lparr>address_length := 3\<rparr>)"
  by (simp_all add: rr_address_without_length_def model_head_of_def rr_test_head_def)

definition rr_gap_parent :: rr_address where
  "rr_gap_parent = rr_test_head\<lparr>address_hash := [1,2]\<rparr>"

definition rr_gap_head :: rr_address where
  "rr_gap_head = rr_test_head\<lparr>address_sequence := 1, address_offset := 5, address_hash := [9,10]\<rparr>"

definition rr_gap_parse :: "rr_bytes \<Rightarrow> rr_decoded_record option" where
  "rr_gap_parse bytes = (if bytes = [1,2] then Some (rr_test_record 2)
    else if bytes = [9,10] then Some ((rr_test_record 3)\<lparr>rr_record_sequence := 1, rr_record_parent := Some rr_gap_parent\<rparr>)
    else None)"

definition rr_gap_encode :: "nat \<Rightarrow> rr_bytes option" where
  "rr_gap_encode token = (if token = 2 then Some [1,2] else if token = 3 then Some [9,10] else None)"

lemma rr_parent_floor_gap_witness:
  "rr_parent_ok rr_gap_head (Some rr_gap_parent)"
  "address_offset rr_gap_parent + address_length rr_gap_parent < address_offset rr_gap_head"
  "rr_floor_walk (rr_read_record Some rr_gap_parse rr_gap_encode) [1,2,0,0,0,9,10] rr_gap_parent 2 rr_gap_head"
  by (simp_all add: numeral_2_eq_2 rr_floor_walk.simps rr_gap_head_def rr_gap_parent_def rr_test_head_def rr_read_record_def
      rr_span_ok_def rr_ends_by_def rr_checked_end_def rr_slice_def rr_record_checks_def
      rr_gap_parse_def rr_gap_encode_def rr_test_record_def rr_u64_max_def Let_def)

lemma rr_overflow_is_not_wrapped_to_zero:
  "rr_checked_end rr_u64_max 1 = None"
  by (simp add: rr_checked_end_def rr_u64_max_def)

section \<open>Input-only flat executable interface\<close>

text \<open>External facts are exact-keyed function graphs. Digest rows contain bytes
  and computed hash bytes; parse rows contain bytes and typed metadata; encode rows
  contain opaque parsed-record tokens and computed canonical bytes. No result or
  validity verdict is supplied. Missing graph entries fail closed. The external
  producer and its SHA/parser/encoder are separately hashed assumptions.\<close>

fun rr_make_profile :: "nat list \<Rightarrow> recovery_profile option" where
  "rr_make_profile [deployment,format,authority] =
    Some \<lparr>recovery_deployment = deployment, recovery_format = format, recovery_authority_profile = authority\<rparr>"
| "rr_make_profile _ = None"

fun rr_make_address :: "nat list \<Rightarrow> rr_bytes \<Rightarrow> rr_address option" where
  "rr_make_address [deployment,format,authority,sequence,offset,count] hash =
    Some \<lparr>address_profile = \<lparr>recovery_deployment = deployment, recovery_format = format,
      recovery_authority_profile = authority\<rparr>, address_sequence = sequence,
      address_offset = offset, address_length = count, address_hash = hash\<rparr>"
| "rr_make_address _ _ = None"

fun rr_parse_fields :: "nat list list \<Rightarrow> rr_decoded_record option" where
  "rr_parse_fields [[deployment,format,authority,sequence,token],[],[]] =
    Some \<lparr>rr_record_profile = \<lparr>recovery_deployment = deployment, recovery_format = format,
      recovery_authority_profile = authority\<rparr>, rr_record_sequence = sequence, rr_record_parent = None, rr_record_token = token\<rparr>"
| "rr_parse_fields [[deployment,format,authority,sequence,token],parent,hash] =
    (case rr_make_address parent hash of None \<Rightarrow> None | Some head \<Rightarrow>
      Some \<lparr>rr_record_profile = \<lparr>recovery_deployment = deployment, recovery_format = format,
        recovery_authority_profile = authority\<rparr>, rr_record_sequence = sequence,
        rr_record_parent = Some head, rr_record_token = token\<rparr>)"
| "rr_parse_fields _ = None"

definition rr_parse_graph where
  "rr_parse_graph facts raw = (case map_of facts raw of None \<Rightarrow> None | Some raw_record_fields \<Rightarrow> rr_parse_fields raw_record_fields)"

definition rr_address_words where
  "rr_address_words (head::rr_address) =
    [recovery_deployment (address_profile head), recovery_format (address_profile head),
     recovery_authority_profile (address_profile head), address_sequence head, address_offset head, address_length head]"

definition rr_prefix_request where
  "rr_prefix_request mode limit profile head count raw =
    (if 0 < limit \<and> 0 < address_length head \<and> address_profile head = profile then
      case rr_checked_end (address_offset head) (address_length head) of None \<Rightarrow> None
       | Some end_offset \<Rightarrow> if count = end_offset \<and> end_offset \<le> limit \<and>
           (case mode of RR_Archive \<Rightarrow> length raw = end_offset | RR_Live \<Rightarrow> end_offset \<le> length raw) \<and>
           rr_octets (take end_offset raw) then Some (take end_offset raw) else None
     else None)"

definition rr_record_observed where
  "rr_record_observed check_digest digests parsed encoded raw head =
    (if \<not> rr_span_ok raw head then True else
      let bytes = rr_slice raw head in
      if check_digest \<and> map_of digests bytes = None then False
      else if check_digest \<and> map_of digests bytes \<noteq> Some (address_hash head) then True
      else case map_of parsed bytes of None \<Rightarrow> False
        | Some raw_record_fields \<Rightarrow> (case rr_parse_fields raw_record_fields of None \<Rightarrow> True
          | Some record \<Rightarrow> if rr_record_profile record \<noteq> address_profile head \<or>
                rr_record_sequence record \<noteq> address_sequence head then True
              else map_of encoded (rr_record_token record) \<noteq> None))"

definition rr_selection_observed where
  "rr_selection_observed check_digest mode limit profile head count prefix_hash raw digests parsed encoded =
    (case rr_prefix_request mode limit profile head count raw of None \<Rightarrow> True
     | Some prefix_bytes_value \<Rightarrow> (case map_of digests prefix_bytes_value of None \<Rightarrow> False
       | Some actual \<Rightarrow> if actual \<noteq> prefix_hash then True
           else rr_record_observed check_digest digests parsed encoded raw head))"

fun rr_floor_observed where
  "rr_floor_observed read_record check_digest raw floor_head 0 head digests parsed encoded = True"
| "rr_floor_observed read_record check_digest raw floor_head (Suc fuel) head digests parsed encoded =
    (if address_profile head \<noteq> address_profile floor_head \<or>
        address_sequence head < address_sequence floor_head then True
     else if \<not> rr_record_observed check_digest digests parsed encoded raw head then False
     else case read_record raw head of None \<Rightarrow> True
       | Some record \<Rightarrow> if head = floor_head then True
           else case rr_record_parent record of None \<Rightarrow> True
             | Some parent \<Rightarrow> rr_floor_observed read_record check_digest raw floor_head fuel parent digests parsed encoded)"

definition rr_observation_result :: "bool \<Rightarrow> nat list list option \<Rightarrow> nat list list option" where
  "rr_observation_result observed result =
    (if observed then Some (case result of None \<Rightarrow> [] | Some rows \<Rightarrow> rows) else None)"

lemma rr_missing_external_observation_is_not_a_guard_rejection:
  "rr_observation_result False result = None"
  "rr_observation_result True None = Some []"
  "rr_observation_result False result \<noteq> rr_observation_result True None"
  by (simp_all add: rr_observation_result_def)

definition rr_run_nat_with where
  "rr_run_nat_with read_record check_digest input digests parsed encoded =
    (case input of [profile,head_words,head_hash,[mode,limit,count],prefix_hash,floor_words,floor_hash,raw] \<Rightarrow>
      (case (rr_make_profile profile,rr_make_address head_words head_hash) of (Some p,Some h) \<Rightarrow>
        if mode > 1 then None else
        rr_observation_result
          (rr_selection_observed check_digest (if mode = 0 then RR_Archive else RR_Live)
            limit p h count prefix_hash raw digests parsed encoded)
          (map_option (\<lambda>(address,bytes,record). [rr_address_words address,address_hash address,bytes])
          (rr_select_with (read_record (map_of digests) (rr_parse_graph parsed) (map_of encoded))
            (if mode = 0 then RR_Archive else RR_Live) limit p h count prefix_hash (map_of digests) raw))
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition rr_floor_nat_with where
  "rr_floor_nat_with read_record check_digest input digests parsed encoded =
    (case input of [profile,head_words,head_hash,[mode,limit,count],prefix_hash,floor_words,floor_hash,raw] \<Rightarrow>
      (case (rr_make_address head_words head_hash,rr_make_address floor_words floor_hash) of (Some h,Some f) \<Rightarrow>
         (let reader = read_record (map_of digests) (rr_parse_graph parsed) (map_of encoded) in
          if rr_floor_observed reader check_digest raw f (Suc (address_sequence h)) h digests parsed encoded then
            Some [[if rr_floor_walk reader raw f (Suc (address_sequence h)) h then 1 else 0]] else None)
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition rr_nonnegative :: "integer list \<Rightarrow> bool" where
  "rr_nonnegative xs = list_all (\<lambda>x. 0 \<le> x) xs"

definition rr_flat_inputs_nonnegative where
  "rr_flat_inputs_nonnegative input digests parsed encoded \<longleftrightarrow>
    list_all rr_nonnegative input \<and>
    list_all (\<lambda>(a,b). rr_nonnegative a \<and> rr_nonnegative b) digests \<and>
    list_all (\<lambda>(a,bs). rr_nonnegative a \<and> list_all rr_nonnegative bs) parsed \<and>
    list_all (\<lambda>(token,bs). 0 \<le> token \<and> rr_nonnegative bs) encoded"

definition rr_integer_call where
  "rr_integer_call run input digests parsed encoded =
    (if \<not> rr_flat_inputs_nonnegative input digests parsed encoded then None else
      let ns = map nat_of_integer;
          result = run (map ns input) (map (\<lambda>(a,b). (ns a,ns b)) digests)
            (map (\<lambda>(a,bs). (ns a,map ns bs)) parsed)
            (map (\<lambda>(token,bs). (nat_of_integer token,ns bs)) encoded)
      in map_option (map (map integer_of_nat)) result)"

definition rr_run_flat where
  "rr_run_flat = rr_integer_call (rr_run_nat_with rr_read_record True)"

definition rr_run_without_record_digest_flat where
  "rr_run_without_record_digest_flat = rr_integer_call (rr_run_nat_with rr_read_record_without_digest False)"

definition rr_floor_flat where
  "rr_floor_flat = rr_integer_call (rr_floor_nat_with rr_read_record True)"

definition rr_floor_without_record_digest_flat where
  "rr_floor_without_record_digest_flat = rr_integer_call (rr_floor_nat_with rr_read_record_without_digest False)"

definition rr_export_identity :: "integer list" where
  "rr_export_identity = [1,64,1,0]"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms checked_selected_prefix_supplies_the_exact_native_address
      rr_checked_end_success_iff rr_checked_end_overflow rr_checked_span_has_the_exact_slice_length
      rr_read_success_exposes_computed_guards rr_archive_exact_length rr_live_prefix_survives_suffix
      rr_archive_rejects_nonempty_suffix rr_floor_success_reads_the_exact_floor rr_native_view_reuses_the_existing_exact_readback
      rr_reopen_view_uses_the_checked_profile rr_same_address_different_bytes_cannot_release_the_expected_reply
      rr_normal_archive_witness rr_live_suffix_and_archive_length_removal_witness
      rr_same_address_record_digest_single_removal_witness rr_address_length_single_removal_witness
      rr_parent_floor_gap_witness rr_overflow_is_not_wrapped_to_zero
      rr_missing_external_observation_is_not_a_guard_rejection})
  then () else error "Unexpected oracle in selected-prefix G0"
\<close>

export_code rr_run_flat rr_run_without_record_digest_flat rr_floor_flat rr_floor_without_record_digest_flat rr_export_identity
  in SML module_name OIP_Record_Reopening_Prefix file_prefix "oip_record_reopening_prefix"

end

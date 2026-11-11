theory Etcd_Control_Confirmation
  imports "OIP_Product.Wire_Fields" "HOL-Library.Code_Target_Nat"
begin

section \<open>Control transport confirmations\<close>

text \<open>
  These observations start at the response bytes of the pinned control client.
  The shared parser covers the canonical fixture fields. The actual protobuf
  decoder also has a wider input domain. TLS, process completion, the initial
  linearizable read and server atomicity are surrounding conditions.
\<close>

fun ec_scalar_fields where
  "ec_scalar_fields ec_tag [] = []"
| "ec_scalar_fields ec_tag (Proto_Varint ec_number ec_value # ec_rest) =
     (if ec_tag = ec_number then ec_value # ec_scalar_fields ec_tag ec_rest else ec_scalar_fields ec_tag ec_rest)"
| "ec_scalar_fields ec_tag (ec_other # ec_rest) = ec_scalar_fields ec_tag ec_rest"

fun ec_message_fields where
  "ec_message_fields ec_tag [] = []"
| "ec_message_fields ec_tag (Proto_Bytes ec_number ec_bytes # ec_rest) =
     (if ec_tag = ec_number then ec_bytes # ec_message_fields ec_tag ec_rest else ec_message_fields ec_tag ec_rest)"
| "ec_message_fields ec_tag (ec_other # ec_rest) = ec_message_fields ec_tag ec_rest"

definition ec_nat_field where
  "ec_nat_field ec_tag ec_fields = (case rev (ec_scalar_fields ec_tag ec_fields) of [] \<Rightarrow> 0 | ec_value # _ \<Rightarrow> ec_value)"

definition ec_bytes_field where
  "ec_bytes_field ec_tag ec_fields = (case rev (ec_message_fields ec_tag ec_fields) of [] \<Rightarrow> [] | ec_value # _ \<Rightarrow> ec_value)"

fun ec_single where
  "ec_single [] = None"
| "ec_single [ec_only] = Some ec_only"
| "ec_single (ec_first # ec_second # ec_rest) = None"

definition ec_header_revision where
  "ec_header_revision ec_cluster ec_headers =
    (case ec_headers of [ec_header] \<Rightarrow>
       Option.bind (read_canonical_proto_fields ec_header) (\<lambda>ec_fields.
         let ec_revision = ec_nat_field 3 ec_fields in
           if ec_nat_field 1 ec_fields = ec_cluster \<and> ec_nat_field 2 ec_fields > 0 \<and>
              ec_revision > 0 \<and> ec_revision < 2^63
           then Some ec_revision else None)
     | _ \<Rightarrow> None)"

definition ec_range_control where
  "ec_range_control ec_cluster ec_key ec_max ec_response =
    Option.bind (read_canonical_proto_fields ec_response) (\<lambda>ec_fields.
      Option.bind (ec_header_revision ec_cluster (ec_message_fields 1 ec_fields)) (\<lambda>ec_revision.
        if ec_nat_field 3 ec_fields \<noteq> 0 \<or> ec_nat_field 4 ec_fields \<noteq> 1 then None else
        Option.bind (ec_single (ec_message_fields 2 ec_fields)) (\<lambda>ec_raw_kv.
          Option.bind (read_canonical_proto_fields ec_raw_kv) (\<lambda>ec_kv.
            let ec_mod = ec_nat_field 3 ec_kv; ec_value = ec_bytes_field 5 ec_kv in
              if ec_bytes_field 1 ec_kv = ec_key \<and> ec_mod > 0 \<and> ec_mod \<le> ec_revision \<and>
                 length ec_value \<le> ec_max then Some (ec_mod,ec_value) else None))))"

definition ec_put_header_matches where
  "ec_put_header_matches ec_cluster ec_revision ec_headers =
    (case ec_headers of [] \<Rightarrow> True | [ec_header] \<Rightarrow>
      (case read_canonical_proto_fields ec_header of None \<Rightarrow> False | Some ec_fields \<Rightarrow>
        ec_nat_field 1 ec_fields \<in> {0,ec_cluster} \<and> ec_nat_field 3 ec_fields \<in> {0,ec_revision})
    | _ \<Rightarrow> False)"

definition ec_exact_put where
  "ec_exact_put ec_cluster ec_revision ec_operation =
    (case read_canonical_proto_fields ec_operation of None \<Rightarrow> False | Some ec_fields \<Rightarrow>
      ec_message_fields 1 ec_fields = [] \<and> ec_message_fields 3 ec_fields = [] \<and> ec_message_fields 4 ec_fields = [] \<and>
      (case ec_message_fields 2 ec_fields of [ec_put] \<Rightarrow>
        (case read_canonical_proto_fields ec_put of None \<Rightarrow> False | Some ec_put_fields \<Rightarrow>
          ec_message_fields 2 ec_put_fields = [] \<and> ec_put_header_matches ec_cluster ec_revision (ec_message_fields 1 ec_put_fields))
       | _ \<Rightarrow> False))"

definition ec_txn_revision where
  "ec_txn_revision ec_cluster ec_expected ec_response =
    Option.bind (read_canonical_proto_fields ec_response) (\<lambda>ec_fields.
      Option.bind (ec_header_revision ec_cluster (ec_message_fields 1 ec_fields)) (\<lambda>ec_revision.
        let ec_operations = ec_message_fields 3 ec_fields in
        if ec_nat_field 2 ec_fields = 0 then (if ec_operations = [] then Some None else None)
        else Option.bind (ec_single ec_operations) (\<lambda>ec_op.
          if ec_revision > ec_expected \<and> ec_exact_put ec_cluster ec_revision ec_op then Some (Some ec_revision) else None)))"

definition ec_confirm_write where
  "ec_confirm_write ec_check_bytes ec_cluster ec_expected ec_key ec_max ec_candidate ec_txn ec_readback =
    (case ec_txn_revision ec_cluster ec_expected ec_txn of
      None \<Rightarrow> None | Some None \<Rightarrow> Some None | Some (Some ec_revision) \<Rightarrow>
      (case ec_range_control ec_cluster ec_key ec_max ec_readback of None \<Rightarrow> None
       | Some (ec_seen,ec_value) \<Rightarrow> if ec_seen = ec_revision \<and> (\<not> ec_check_bytes \<or> ec_value = ec_candidate)
         then Some (Some ec_seen) else None))"

lemma ec_range_yields_a_positive_bounded_mod_revision_and_value:
  assumes "ec_range_control ec_cluster ec_key ec_max ec_raw = Some (ec_mod,ec_value)"
  shows "0 < ec_mod \<and> length ec_value \<le> ec_max"
  using assms by (auto simp: ec_range_control_def Let_def Option.bind_eq_Some_conv split: if_splits)

lemma ec_transaction_confirmation_advances_the_expected_revision:
  assumes "ec_txn_revision ec_cluster ec_expected ec_txn = Some (Some ec_revision)"
  shows "ec_expected < ec_revision"
  using assms by (auto simp: ec_txn_revision_def Let_def Option.bind_eq_Some_conv split: if_splits)

lemma ec_success_requires_exact_selected_revision_and_bytes:
  assumes "ec_confirm_write True ec_cluster ec_expected ec_key ec_max ec_candidate ec_txn ec_readback = Some (Some ec_revision)"
  shows "ec_txn_revision ec_cluster ec_expected ec_txn = Some (Some ec_revision)"
    "ec_range_control ec_cluster ec_key ec_max ec_readback = Some (ec_revision,ec_candidate)"
  using assms by (auto simp: ec_confirm_write_def split: option.splits prod.splits if_splits)

lemma ec_bytes_guard_separates_a_different_value_at_the_same_revision:
  assumes "ec_txn_revision ec_cluster ec_expected ec_txn = Some (Some ec_revision)"
    "ec_range_control ec_cluster ec_key ec_max ec_readback = Some (ec_revision,ec_other)"
    "ec_other \<noteq> ec_candidate"
  shows "ec_confirm_write True ec_cluster ec_expected ec_key ec_max ec_candidate ec_txn ec_readback = None"
    "ec_confirm_write False ec_cluster ec_expected ec_key ec_max ec_candidate ec_txn ec_readback = Some (Some ec_revision)"
  using assms by (simp_all add: ec_confirm_write_def)

fun ec_txn_observation where
  "ec_txn_observation None = [0]"
| "ec_txn_observation (Some None) = [1]"
| "ec_txn_observation (Some (Some ec_revision)) = [2,ec_revision]"

definition ec_observe where
  "ec_observe ec_check_bytes ec_header ec_key ec_candidate ec_raw ec_readback =
    (case ec_header of [ec_mode,ec_cluster,ec_expected,ec_max] \<Rightarrow>
      (if ec_mode = 0 then
         (case ec_range_control ec_cluster ec_key ec_max ec_raw of None \<Rightarrow> [0] | Some (ec_revision,ec_value) \<Rightarrow> [2,ec_revision] @ ec_value)
       else if ec_mode = 1 then ec_txn_observation (ec_txn_revision ec_cluster ec_expected ec_raw)
       else if ec_mode = 2 then ec_txn_observation (ec_confirm_write ec_check_bytes ec_cluster ec_expected ec_key ec_max ec_candidate ec_raw ec_readback)
       else [])
    | _ \<Rightarrow> [])"

definition ec_observe_integer :: "bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list" where
  "ec_observe_integer ec_check ec_header ec_key ec_candidate ec_raw ec_readback =
    (if list_all (\<lambda>ec_word. 0 \<le> ec_word) (ec_header @ ec_key @ ec_candidate @ ec_raw @ ec_readback)
     then map integer_of_nat (ec_observe ec_check (map nat_of_integer ec_header) (map nat_of_integer ec_key)
       (map nat_of_integer ec_candidate) (map nat_of_integer ec_raw) (map nat_of_integer ec_readback)) else [])"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms ec_range_yields_a_positive_bounded_mod_revision_and_value
    ec_transaction_confirmation_advances_the_expected_revision ec_success_requires_exact_selected_revision_and_bytes
    ec_bytes_guard_separates_a_different_value_at_the_same_revision}) then ()
  else error "Unexpected oracle in control confirmation"
\<close>

export_code ec_observe_integer in SML module_name OIP_Etcd_Confirmation file_prefix "oip_etcd_confirmation"

end

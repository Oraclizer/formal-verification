theory ACK1_Entry
  imports "OIP_Message_Code.Wire_Code_Oracle_Codegen"
    "OIP_Message_Code.Wire_Code_Typed_Summary_ABI"
begin

text \<open>Entry boundary for the synthetic Rules fixture. The ordered lanes
have a selected control with no cancelled transport or pending decisions.
This leaf stops at eligibility to invoke acknowledge_secondary. Its signed
envelope and its product identity and maintenance credential are separate.\<close>

definition ack1_rules_principal :: "nat \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> nat option" where
  "ack1_rules_principal a1_host_token a1_host_principal a1_token =
    (if a1_token = Some a1_host_token then Some a1_host_principal else None)"

text \<open>The result words are status, final gate, binding reached, arrival
tag, maintenance principal present, and principal. A zero status means
maintenance capability was obtained. The ACK product effect is separate.\<close>

definition ack1_reply :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> nat list" where
  "ack1_reply a1_status a1_gate a1_reached a1_arrival a1_principal =
    [a1_status,a1_gate,a1_reached,a1_arrival,(case a1_principal of None \<Rightarrow> 0 | Some _ \<Rightarrow> 1),
      (case a1_principal of None \<Rightarrow> 0 | Some a1_actor \<Rightarrow> a1_actor)]"

definition ack1_ordered_precheck ::
  "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> (nat \<times> nat) option" where
  "ack1_ordered_precheck a1_source a1_revoked a1_host_token a1_host_principal a1_token =
    (if a1_source \<in> set a1_revoked then Some (72,2)
     else if a1_token = None then Some (77,3)
     else case ack1_rules_principal a1_host_token a1_host_principal a1_token of
       None \<Rightarrow> Some (77,4)
     | Some a1_maintainer \<Rightarrow> if a1_maintainer \<in> set a1_revoked then Some (72,5) else None)"

definition ack1_run_operand ::
  "nat \<Rightarrow> wire_core \<Rightarrow> native_scheduled_ack \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
     nat option \<Rightarrow> nat list \<Rightarrow> nat list" where
  "ack1_run_operand a1_arrival a1_core a1_ack a1_host_token a1_host_principal a1_token a1_maintainers =
    (if scheduled_ack_target a1_ack \<noteq> wire_source_domain a1_core then ack1_reply 72 7 1 a1_arrival None
     else if a1_token = None then ack1_reply 77 8 1 a1_arrival None
     else case ack1_rules_principal a1_host_token a1_host_principal a1_token of
       None \<Rightarrow> ack1_reply 77 9 1 a1_arrival None
     | Some a1_principal \<Rightarrow>
       if a1_principal \<in> set a1_maintainers then ack1_reply 0 11 1 a1_arrival (Some a1_principal)
       else ack1_reply 77 10 1 a1_arrival (Some a1_principal))"

definition ack1_select where
  "ack1_select a1_ordered a1_revoked a1_source a1_host_token a1_host_principal a1_token a1_maintainers a1_prior a1_core a1_ack =
    (case (if a1_ordered then ack1_ordered_precheck a1_source a1_revoked a1_host_token a1_host_principal a1_token else None) of
       Some (a1_status,a1_gate) \<Rightarrow> ack1_reply a1_status a1_gate 0 0 None
     | None \<Rightarrow> (case code_compare_binding a1_prior (encode_wire_core a1_core) of
         Code_Replay_Conflict \<Rightarrow> ack1_reply 76 6 1 2 None
       | Code_First \<Rightarrow> ack1_run_operand 0 a1_core a1_ack a1_host_token a1_host_principal a1_token a1_maintainers
       | Code_Identical \<Rightarrow> ack1_run_operand 1 a1_core a1_ack a1_host_token a1_host_principal a1_token a1_maintainers))"

lemma ack1_direct_target_precedes_maintenance:
  assumes "scheduled_ack_target a1_ack \<noteq> wire_source_domain a1_core"
  shows "ack1_run_operand a1_arrival a1_core a1_ack a1_host_token a1_host_principal a1_token a1_maintainers = [72,7,1,a1_arrival,0,0]"
  using assms by (simp add: ack1_run_operand_def ack1_reply_def)

lemma ack1_ordered_missing_stops_before_binding_and_target:
  assumes "a1_source \<notin> set a1_revoked"
  shows "ack1_select True a1_revoked a1_source a1_host_token a1_host_principal None a1_maintainers a1_prior a1_core a1_ack =
    [77,3,0,0,0,0]"
  using assms by (simp add: ack1_select_def ack1_ordered_precheck_def ack1_reply_def)

lemma ack1_ordered_invalid_stops_before_binding_and_target:
  assumes "a1_source \<notin> set a1_revoked" "a1_token \<noteq> a1_host_token"
  shows "ack1_select True a1_revoked a1_source a1_host_token a1_host_principal (Some a1_token) a1_maintainers a1_prior a1_core a1_ack =
    [77,4,0,0,0,0]"
  using assms by (simp add: ack1_select_def ack1_ordered_precheck_def ack1_rules_principal_def ack1_reply_def)

lemma ack1_direct_missing_and_invalid_are_distinct_after_first_binding:
  assumes "scheduled_ack_target a1_ack = wire_source_domain a1_core"
    and "a1_token \<noteq> a1_host_token"
  shows "ack1_select False a1_revoked a1_source a1_host_token a1_host_principal None a1_maintainers None a1_core a1_ack = [77,8,1,0,0,0]"
    and "ack1_select False a1_revoked a1_source a1_host_token a1_host_principal (Some a1_token) a1_maintainers None a1_core a1_ack = [77,9,1,0,0,0]"
  using assms by (simp_all add: ack1_select_def ack1_run_operand_def code_compare_binding_def
    ack1_rules_principal_def ack1_reply_def)

lemma ack1_capability_requires_ledger_membership_after_rules_authentication:
  assumes "scheduled_ack_target a1_ack = wire_source_domain a1_core"
  shows "ack1_run_operand a1_arrival a1_core a1_ack a1_host_token a1_host_principal (Some a1_host_token) a1_maintainers =
    (if a1_host_principal \<in> set a1_maintainers then [0,11,1,a1_arrival,1,a1_host_principal]
     else [77,10,1,a1_arrival,1,a1_host_principal])"
  using assms by (simp add: ack1_run_operand_def ack1_rules_principal_def ack1_reply_def)

lemma ack1_outer_conflict_stops_direct_before_target:
  assumes "a1_saved \<noteq> encode_wire_core a1_core"
  shows "ack1_select False a1_revoked a1_source a1_host_token a1_host_principal a1_token a1_maintainers (Some a1_saved) a1_core a1_ack =
    [76,6,1,2,0,0]"
  using assms by (simp add: ack1_select_def ack1_reply_def
    a_conflicting_source_binding_cannot_replace_an_earlier_body)

definition ack1_view where
  "ack1_view a1_words a1_core a1_ack =
    [a1_words,[wire_source_domain a1_core,scheduled_ack_target a1_ack],
     code_ir_transport_key a1_core,encode_wire_core a1_core]"

definition ack1_stop where
  "ack1_stop a1_status a1_gate = [ack1_reply a1_status a1_gate 0 0 None,[],[],[]]"

definition ack1_from_core where
  "ack1_from_core a1_ordered a1_revoked a1_identity a1_directory_entry a1_host_token a1_host_principal a1_token a1_maintainers a1_prior a1_core =
    (if wire_message_family a1_core \<noteq> Wire_Ack \<or> wire_opcode (wire_operation_body a1_core) \<noteq> 1 then None
     else case parse_native_scheduled_ack a1_core of None \<Rightarrow> Some (ack1_stop 70 0)
     | Some a1_ack \<Rightarrow>
       (case a1_identity of [a1_principal,a1_domain,a1_ocid,a1_rai] \<Rightarrow>
          if a1_identity \<noteq> a1_directory_entry \<or> a1_principal \<noteq> wire_principal a1_core \<or> a1_domain \<noteq> wire_source_domain a1_core
          then Some (ack1_view (ack1_reply 72 1 0 0 None) a1_core a1_ack)
          else Some (ack1_view
            (ack1_select a1_ordered a1_revoked a1_principal a1_host_token a1_host_principal a1_token a1_maintainers a1_prior a1_core a1_ack) a1_core a1_ack)
        | _ \<Rightarrow> None))"

definition ack1_from_packet where
  "ack1_from_packet a1_ordered a1_revoked a1_identity a1_directory_entry a1_host_token a1_host_principal a1_token a1_maintainers a1_prior
      a1_authority a1_verified a1_preimage a1_signature_bytes a1_bytes =
    (case code_check_declared_version a1_bytes (boundary_max_frame a1_authority) of
       Some a1_reason \<Rightarrow> Some (ack1_stop (code_transport_refusal_number a1_reason) 0)
     | None \<Rightarrow>
       (case decode_wire_packet a1_bytes of None \<Rightarrow> Some (ack1_stop 70 0)
        | Some a1_packet \<Rightarrow>
          (case code_admit_packet (\<lambda>_ a1_msg a1_sig_bytes. a1_verified \<and> a1_msg = a1_preimage \<and> a1_sig_bytes = a1_signature_bytes)
                   a1_packet a1_authority of
             Some a1_reason \<Rightarrow> Some (ack1_stop (code_transport_refusal_number a1_reason) 0)
           | None \<Rightarrow> ack1_from_core a1_ordered a1_revoked a1_identity a1_directory_entry a1_host_token a1_host_principal
               a1_token a1_maintainers a1_prior (packet_core a1_packet))))"

definition ack1_entry_integer ::
  "integer list \<Rightarrow> integer list option \<Rightarrow> integer list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow>
    integer list \<Rightarrow> integer list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list list option" where
  "ack1_entry_integer a1_bytes a1_prior a1_values a1_version a1_families a1_atomicities a1_schemes a1_critical a1_verified
      a1_controls a1_identity a1_directory_entry a1_maintainers a1_revoked a1_preimage a1_signature_bytes =
    (if length a1_values \<noteq> 13 \<or> length a1_identity \<noteq> 4 \<or> length a1_directory_entry \<noteq> 4 \<or>
       a1_version \<noteq> 6 \<or> 1 \<notin> set a1_schemes \<or>
       \<not> code_integer_u64_values (a1_values @ [a1_version] @ a1_families @ a1_atomicities @ a1_schemes @ a1_controls @
         a1_identity @ a1_directory_entry @ a1_maintainers @ a1_revoked) \<or> \<not> code_integer_common_host_values a1_values \<or>
       \<not> list_all code_integer_octet_values (a1_bytes # a1_preimage # a1_signature_bytes # (case a1_prior of None \<Rightarrow> [] | Some a1_saved \<Rightarrow> [a1_saved]))
     then None else case map nat_of_integer a1_controls of
       [a1_ordered,a1_host_token,a1_host_principal,a1_present,a1_token_value,0,0] \<Rightarrow>
         if a1_ordered > 1 \<or> a1_present > 1 then None else
         map_option (map (map integer_of_nat))
           (ack1_from_packet (a1_ordered = 1) (map nat_of_integer a1_revoked) (map nat_of_integer a1_identity)
             (map nat_of_integer a1_directory_entry) a1_host_token a1_host_principal
             (if a1_present = 1 then Some a1_token_value else None) (map nat_of_integer a1_maintainers)
             (map_option (map nat_of_integer) a1_prior)
             (code_contract_boundary (map nat_of_integer a1_values) (nat_of_integer a1_version)
               (map nat_of_integer a1_families) (map nat_of_integer a1_atomicities) (map nat_of_integer a1_schemes) a1_critical)
             a1_verified (map nat_of_integer a1_preimage) (map nat_of_integer a1_signature_bytes) (map nat_of_integer a1_bytes))
      | _ \<Rightarrow> None)"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      the_source_settlement_ack_parser_has_the_existing_exact_product_value
      ack1_direct_target_precedes_maintenance
      ack1_ordered_missing_stops_before_binding_and_target
      ack1_ordered_invalid_stops_before_binding_and_target
      ack1_direct_missing_and_invalid_are_distinct_after_first_binding
      ack1_capability_requires_ledger_membership_after_rules_authentication
      ack1_outer_conflict_stops_direct_before_target})
  then () else error "Unexpected oracle in ACK/1 entry"
\<close>

export_code ack1_entry_integer in SML module_name OIP_ACK1_Entry_ABI file_prefix "oip_ack1_entry_abi"

end

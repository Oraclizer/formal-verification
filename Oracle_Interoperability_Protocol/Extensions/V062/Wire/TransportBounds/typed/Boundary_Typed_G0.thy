theory Boundary_Typed_G0
  imports "OIP_Transport_Boundary_Arithmetic.Boundary_Go_Arithmetic"
    "OIP_Message_Code.Wire_Code_Oracle_Contract"
begin

text \<open>
  Source data witness only.  This leaf proves the arithmetic/nonvacuity
  branches without invoking the byte parser.  The child byte leaf separately
  proves exact encoding to the frozen 425-byte signed source Packet.
\<close>

definition boundary_g0_typed_body :: wire_body where
  "boundary_g0_typed_body = \<lparr>wire_opcode = 1, wire_words = [33,33,2,2,9,0,17,17,7,2,3,1,17,0,17,7,0,9,1,17,0,0],
    wire_blobs = [[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]], wire_deadline = Deadline_Absent\<rparr>"

definition boundary_g0_typed_core :: wire_core where
  "boundary_g0_typed_core = \<lparr>wire_version = 6, wire_purpose = 1,
    wire_deployment = 7, wire_source_domain = 0, wire_target_domain = 0,
    wire_principal = 7, wire_key_number = 9, wire_authority_epoch = 9,
    wire_sent_seconds = 100, wire_ttl_seconds = 5, wire_uuid = [0,1,2,3,4,5,64,7,128,9,10,11,12,13,14,15],
    wire_message_family = Wire_State_Sync, wire_primary_code = 1, wire_secondary_code = Some 77,
    wire_signature_scheme = 1, wire_operation_body = boundary_g0_typed_body,
    wire_atomicity = 3, wire_priority = 3, wire_route_scope = 1\<rparr>"

definition boundary_g0_typed_packet :: wire_packet where
  "boundary_g0_typed_packet = \<lparr>packet_core = boundary_g0_typed_core,
    packet_signature = [254,173,113,58,226,33,234,102,211,135,76,109,223,32,108,55,115,188,185,242,176,65,203,155,229,203,241,209,9,107,152,67,245,31,44,234,145,226,75,23,25,39,212,101,95,47,224,183,204,210,182,144,148,244,15,145,184,20,20,45,66,157,98,6]\<rparr>"

definition boundary_g0_authority :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> wire_boundary" where
  "boundary_g0_authority now floor skew =
    code_contract_boundary [7,0,0,7,9,9,1,now,floor,skew,1048576,6,4]
      6 [1,2,3,4,5,6,7] [1,2,3] [1,2] False"

lemmas boundary_g0_typed_simps = boundary_g0_typed_body_def boundary_g0_typed_core_def
  boundary_g0_typed_packet_def boundary_g0_authority_def code_contract_boundary_def
  code_numeric_family_set_def family_at_number_def

lemma typed_source_packet_has_the_arithmetic_carriers:
  "wire_sent_seconds (packet_core boundary_g0_typed_packet) = 100"
  "wire_ttl_seconds (packet_core boundary_g0_typed_packet) = 5"
  by (simp_all add: boundary_g0_typed_simps)

lemma typed_source_positive_and_overflow_branches_are_reached:
  "code_admit_packet (\<lambda>_ _ _. True) boundary_g0_typed_packet
      (boundary_g0_authority 105 0 0) = None"
  "code_admit_packet (\<lambda>_ _ _. True) boundary_g0_typed_packet
      (boundary_g0_authority 0 (2^64 - 1) 100) = Some Wire_TTL_Invalid"
  "code_admit_packet (\<lambda>_ _ _. True) boundary_g0_typed_packet
      (boundary_g0_authority 105 0 (2^64 - 1)) = Some Wire_TTL_Invalid"
  by (simp_all add: boundary_g0_typed_simps code_admit_packet_def
    code_check_versioned_scope_def code_profile_allows_def code_wire_expiry_def
    current_wire_scope_def Let_def)

definition boundary_g0_mutated_ttl_tail ::
  "bool \<Rightarrow> bool \<Rightarrow> wire_core \<Rightarrow> wire_boundary \<Rightarrow> wire_refusal option" where
  "boundary_g0_mutated_ttl_tail keep_expiry keep_latest core authority =
    (let sent = wire_sent_seconds core;
         ttl = max (wire_ttl_seconds core) (boundary_asset_ttl_floor authority);
         now = boundary_now authority; skew = boundary_future_skew authority in
      if (keep_expiry \<and> ttl > 2^64 - 1 - sent) \<or>
         (keep_latest \<and> skew > 2^64 - 1 - now) \<or>
         sent > (now + skew) mod 2^64
      then Some Wire_TTL_Invalid
      else if (sent + ttl) mod 2^64 < now then Some Wire_TTL_Expired else None)"

lemma keeping_both_go_guards_reuses_the_generic_tail:
  assumes "wire_sent_seconds core < 2^64" "boundary_now authority < 2^64"
  shows "boundary_g0_mutated_ttl_tail True True core authority =
    (if wire_expiry authority core \<ge> 2^64 \<or>
        boundary_now authority + boundary_future_skew authority \<ge> 2^64 \<or>
        wire_sent_seconds core > boundary_now authority + boundary_future_skew authority
     then Some Wire_TTL_Invalid
     else if wire_expiry authority core < boundary_now authority
     then Some Wire_TTL_Expired else None)"
proof -
  note tail = go_wrapped_ttl_tail_equals_the_existing_sum_tail[OF assms,
    where ttl="max (wire_ttl_seconds core) (boundary_asset_ttl_floor authority)"
      and skew="boundary_future_skew authority"]
  show ?thesis
    by (simp only: boundary_g0_mutated_ttl_tail_def wire_expiry_def
      effective_wire_ttl_def Let_def simp_thms tail)
qed

lemma typed_removing_either_overflow_guard_reaches_the_success_tail:
  "boundary_g0_mutated_ttl_tail False True (packet_core boundary_g0_typed_packet)
      (boundary_g0_authority 0 (2^64 - 1) 100) = None"
  "boundary_g0_mutated_ttl_tail True False (packet_core boundary_g0_typed_packet)
      (boundary_g0_authority 105 0 (2^64 - 1)) = None"
  by (simp_all add: boundary_g0_mutated_ttl_tail_def boundary_g0_typed_simps Let_def)

lemma typed_old_clock_skew_vector_masks_removal_of_the_latest_guard:
  "boundary_g0_mutated_ttl_tail True False (packet_core boundary_g0_typed_packet)
      (boundary_g0_authority (2^64 - 1) 0 1) = Some Wire_TTL_Invalid"
  by (simp add: boundary_g0_mutated_ttl_tail_def boundary_g0_typed_simps Let_def)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      typed_source_packet_has_the_arithmetic_carriers
      typed_source_positive_and_overflow_branches_are_reached
      keeping_both_go_guards_reuses_the_generic_tail
      typed_removing_either_overflow_guard_reaches_the_success_tail
      typed_old_clock_skew_vector_masks_removal_of_the_latest_guard})
  then () else error "Unexpected oracle in typed boundary G-0"
\<close>

end

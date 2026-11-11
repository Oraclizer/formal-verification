theory Boundary_Go_Arithmetic
  imports "OIP_Message_Code.Wire_Code_Admission"
begin

text \<open>
  G-0 draft.  This theory adds no admission, packet, or transport model.
  It relates the subtraction checks in go/wire/admission.go:204--208 to
  the existing checked-sum admission model.  The two carrier bounds are
  supplied by the decoded u64 Core and the u64 host Boundary, respectively.
  They are not new protocol permissions.  Native checking is owned by Main.
\<close>

lemma subtraction_capacity_is_exact_sum_overflow:
  fixes left right limit :: nat
  assumes "left < limit"
  shows "(right > limit - 1 - left) \<longleftrightarrow> limit \<le> left + right"
  using assms by arith

lemma go_wrapped_ttl_tail_equals_the_existing_sum_tail:
  fixes sent ttl now skew :: nat
  assumes sent: "sent < 2^64" and now: "now < 2^64"
  shows
    "(if ttl > 2^64 - 1 - sent \<or> skew > 2^64 - 1 - now \<or>
           sent > (now + skew) mod 2^64
      then Some Wire_TTL_Invalid
      else if (sent + ttl) mod 2^64 < now then Some Wire_TTL_Expired else None) =
     (if sent + ttl \<ge> 2^64 \<or> now + skew \<ge> 2^64 \<or> sent > now + skew
      then Some Wire_TTL_Invalid
      else if sent + ttl < now then Some Wire_TTL_Expired else None)"
proof -
  have expiry: "(ttl > 2^64 - 1 - sent) \<longleftrightarrow> 2^64 \<le> sent + ttl"
    by (rule subtraction_capacity_is_exact_sum_overflow[OF sent])
  have latest: "(skew > 2^64 - 1 - now) \<longleftrightarrow> 2^64 \<le> now + skew"
    by (rule subtraction_capacity_is_exact_sum_overflow[OF now])
  show ?thesis
    apply (simp only: expiry latest)
    by (cases "sent + ttl < 2^64"; cases "now + skew < 2^64") simp_all
qed

theorem go_scope_checks_reuse_the_existing_single_wire_admission:
  fixes core :: wire_core and authority :: wire_boundary
  assumes sent: "wire_sent_seconds core < 2^64"
    and now: "boundary_now authority < 2^64"
  shows
    "(let profile = boundary_profile authority;
          sent = wire_sent_seconds core;
          ttl = max (wire_ttl_seconds core) (boundary_asset_ttl_floor authority);
          now = boundary_now authority; skew = boundary_future_skew authority in
      if negotiated_version profile \<noteq> 6 \<or> wire_version core \<noteq> 6 \<or>
         boundary_version_floor authority > 6 \<or>
         wire_message_family core \<notin> negotiated_families profile \<or>
         wire_atomicity core \<notin> negotiated_atomicities profile
      then Some Unsupported_Wire_Version
      else if \<not> current_wire_scope authority core then Some Invalid_Wire_Source
      else if ttl > 2^64 - 1 - sent \<or> skew > 2^64 - 1 - now \<or>
              sent > (now + skew) mod 2^64
      then Some Wire_TTL_Invalid
      else if (sent + ttl) mod 2^64 < now then Some Wire_TTL_Expired else None) =
     code_check_versioned_scope core authority 6"
proof -
  note tail = go_wrapped_ttl_tail_equals_the_existing_sum_tail[OF sent now,
    where ttl="max (wire_ttl_seconds core) (boundary_asset_ttl_floor authority)"
      and skew="boundary_future_skew authority"]
  show ?thesis
    apply (simp only: Let_def tail)
    by (auto simp: code_check_versioned_scope_def code_profile_allows_def
      code_wire_expiry_def Let_def split: if_splits)
qed

lemma a_representable_endpoint_includes_the_exact_maximum:
  "\<not> ((2^64 - 1::nat) > 2^64 - 1 - 0)"
  "(0 + (2^64 - 1::nat)) mod 2^64 = 2^64 - 1"
  by simp_all

lemma the_left_carrier_bound_cannot_be_silently_dropped:
  "\<not> ((0::nat) > 2^64 - 1 - 2^64)"
  "(2^64::nat) \<le> 2^64 + 0"
  by simp_all

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms
      subtraction_capacity_is_exact_sum_overflow
      go_wrapped_ttl_tail_equals_the_existing_sum_tail
      go_scope_checks_reuse_the_existing_single_wire_admission
      a_representable_endpoint_includes_the_exact_maximum
      the_left_carrier_bound_cannot_be_silently_dropped})
  then () else error "Unexpected oracle in transport boundary arithmetic"
\<close>

end

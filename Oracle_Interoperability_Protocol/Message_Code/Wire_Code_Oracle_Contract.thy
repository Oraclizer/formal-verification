theory Wire_Code_Oracle_Contract
  imports Wire_Code_Oracle_Transport
begin

definition code_numeric_family_set where
  "code_numeric_family_set numbers =
    set (concat (map (\<lambda>number. case family_at_number number of None \<Rightarrow> [] | Some family \<Rightarrow> [family]) numbers))"

lemma a_known_numeric_profile_family_has_the_exact_model_membership:
  "family \<in> code_numeric_family_set numbers \<longleftrightarrow> family_number family \<in> set numbers"
proof -
  have element: "\<And>number. family \<in> set
      (case family_at_number number of None \<Rightarrow> [] | Some parsed_family \<Rightarrow> [parsed_family])
      \<longleftrightarrow> family_at_number number = Some family"
  proof -
    fix number
    show "family \<in> set
        (case family_at_number number of None \<Rightarrow> [] | Some parsed_family \<Rightarrow> [parsed_family])
        \<longleftrightarrow> family_at_number number = Some family"
      by (cases "family_at_number number") auto
  qed
  have membership: "family \<in> code_numeric_family_set numbers \<longleftrightarrow>
      (\<exists>number \<in> set numbers. family_at_number number = Some family)"
    by (simp add: code_numeric_family_set_def element eq_commute)
  show ?thesis
  proof
    assume "family \<in> code_numeric_family_set numbers"
    then obtain number where member: "number \<in> set numbers"
      and decoded: "family_at_number number = Some family"
      using membership by blast
    have "family_number family = number"
      using decoded by (auto simp only: family_at_number_def find_Some_iff)
    then show "family_number family \<in> set numbers" using member by simp
  next
    assume member: "family_number family \<in> set numbers"
    have "\<exists>number \<in> set numbers. family_at_number number = Some family"
      by (rule bexI[where x="family_number family"]) (use member in simp_all)
    then show "family \<in> code_numeric_family_set numbers" using membership by blast
  qed
qed

definition code_contract_boundary where
  "code_contract_boundary values version families atomicities schemes critical =
    \<lparr>boundary_profile = \<lparr>negotiated_version = version,negotiated_families = code_numeric_family_set families,
       negotiated_atomicities = set atomicities,negotiated_schemes = set schemes\<rparr>,
     boundary_deployment = values ! 0,boundary_source = values ! 1,boundary_target = values ! 2,
     boundary_principal = values ! 3,boundary_key = values ! 4,boundary_epoch = values ! 5,
     boundary_route_scope = values ! 6,boundary_now = values ! 7,boundary_asset_ttl_floor = values ! 8,
     boundary_future_skew = values ! 9,boundary_max_frame = values ! 10,boundary_version_floor = values ! 11,
     boundary_critical_allowed = critical,boundary_threshold_supported = False\<rparr>"

definition code_contract_transport_oracle where
  "code_contract_transport_oracle bytes values version families atomicities schemes critical signature_valid attestation_valid prior =
    (if length values \<noteq> 13 then (Code_Transport_Pending,prior)
     else code_partial_transport_oracle bytes
       (code_contract_boundary values version families atomicities schemes critical) (values ! 12)
       signature_valid attestation_valid prior)"

fun code_integer_reply where
  "code_integer_reply (Code_Transport_First,binding) = (0,map_option (map integer_of_nat) binding)"
| "code_integer_reply (Code_Transport_Identical,binding) = (1,map_option (map integer_of_nat) binding)"
| "code_integer_reply (Code_Transport_Refusal number,binding) =
    (integer_of_nat number,map_option (map integer_of_nat) binding)"
| "code_integer_reply (Code_Transport_Pending,binding) = (-1,map_option (map integer_of_nat) binding)"

definition code_integer_u64_values where
  "code_integer_u64_values values \<longleftrightarrow> (\<forall>value \<in> set values. 0 \<le> value \<and> value < (2^64::integer))"

definition code_integer_octet_values where
  "code_integer_octet_values values \<longleftrightarrow> (\<forall>value \<in> set values. 0 \<le> value \<and> value < (256::integer))"

definition code_integer_common_host_values where
  "code_integer_common_host_values values \<longleftrightarrow>
    (length values \<noteq> 13 \<or> (values ! 10 < (2^63::integer) \<and> values ! 12 < (2^63::integer)))"

definition code_partial_transport_integer_oracle ::
  "integer list \<Rightarrow> integer list \<Rightarrow> integer \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow>
    integer list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> integer list option \<Rightarrow>
    (integer \<times> integer list option)" where
  "code_partial_transport_integer_oracle bytes values version families atomicities schemes critical signature_valid attestation_valid prior =
    (if \<not> code_integer_octet_values bytes \<or>
        \<not> code_integer_u64_values (values @ [version] @ families @ atomicities @ schemes) \<or>
        \<not> code_integer_common_host_values values \<or>
        (case prior of None \<Rightarrow> False | Some retained \<Rightarrow> \<not> code_integer_octet_values retained)
     then (-1,None)
     else code_integer_reply (code_contract_transport_oracle
       (map nat_of_integer bytes) (map nat_of_integer values) (nat_of_integer version)
       (map nat_of_integer families) (map nat_of_integer atomicities) (map nat_of_integer schemes)
       critical signature_valid attestation_valid (map_option (map nat_of_integer) prior)))"

definition code_partial_transport_flat_oracle where
  "code_partial_transport_flat_oracle bytes values version families atomicities schemes critical signature_valid attestation_valid prior_present prior =
    (let (status,binding) = code_partial_transport_integer_oracle bytes values version families atomicities schemes
        critical signature_valid attestation_valid (if prior_present then Some prior else None)
     in case binding of None \<Rightarrow> (status,False,[]) | Some retained \<Rightarrow> (status,True,retained))"

lemma an_in_domain_integer_call_keeps_the_transport_result:
  assumes raw: "code_integer_octet_values bytes"
    and numbers: "code_integer_u64_values (values @ [version] @ families @ atomicities @ schemes)"
    and host: "code_integer_common_host_values values"
    and retained: "case prior of None \<Rightarrow> True | Some saved \<Rightarrow> code_integer_octet_values saved"
  shows "code_partial_transport_integer_oracle bytes values version families atomicities schemes
      critical signature_valid attestation_valid prior =
    code_integer_reply (code_contract_transport_oracle
      (map nat_of_integer bytes) (map nat_of_integer values) (nat_of_integer version)
      (map nat_of_integer families) (map nat_of_integer atomicities) (map nat_of_integer schemes)
      critical signature_valid attestation_valid (map_option (map nat_of_integer) prior))"
  using assms by (cases prior) (simp_all add: code_partial_transport_integer_oracle_def)

lemma a_frame_limit_outside_the_common_host_domain_is_bad_metadata:
  assumes "length values = 13" "(2^63::integer) \<le> values ! 10"
  shows "code_partial_transport_integer_oracle bytes values version families atomicities schemes
      critical signature_valid attestation_valid prior = (-1,None)"
  using assms by (simp add: code_partial_transport_integer_oracle_def code_integer_common_host_values_def)

lemma a_nesting_limit_outside_the_common_host_domain_is_bad_metadata:
  assumes "length values = 13" "(2^63::integer) \<le> values ! 12"
  shows "code_partial_transport_integer_oracle bytes values version families atomicities schemes
      critical signature_valid attestation_valid prior = (-1,None)"
  using assms by (simp add: code_partial_transport_integer_oracle_def code_integer_common_host_values_def)

lemma the_common_host_domain_reads_only_frame_and_nesting_positions:
  assumes "length first = 13" "length second = 13"
    "first ! 10 = second ! 10" "first ! 12 = second ! 12"
  shows "code_integer_common_host_values first = code_integer_common_host_values second"
  using assms by (simp add: code_integer_common_host_values_def)

lemma the_maximum_common_host_limits_are_in_domain:
  "code_integer_common_host_values
    [0,0,0,0,0,0,0,0,0,0,2^63-1,6,2^63-1]"
  by (simp add: code_integer_common_host_values_def)

lemma a_full_u64_deployment_does_not_narrow_the_common_host_limits:
  "code_integer_common_host_values
    [2^64-1,0,0,0,0,0,0,0,0,0,2^63-1,6,2^63-1]"
  by (simp add: code_integer_common_host_values_def)

text \<open>
  The integer-only ABI lets a JSONL adapter serialize data without recreating
  any wire validation rule.  Boundary values are ordered as deployment,
  source, target, principal, key_id, epoch, route_scope, now, asset_ttl_floor,
  future_skew, max_frame, version_floor, max_nesting.  Status zero means a
  first acceptance, one an identical acceptance, a positive refusal uses
  its exact response number, and minus one means pending or bad adapter
  metadata.  A strict runner must reject minus one as incomplete.
  The flat wrapper uses an explicit presence boolean and a list at the ABI
  boundary, so the adapter need not know generated option constructors.
  On the shared 64-bit execution domain only max_frame at index10 and
  max_nesting at index12 additionally have the Go int upper bound2^63-1;
  Rust represents these as usize. Existing u64 validation already enforces
  nonnegativity. Every other integer field retains its u64 domain. A bad
  shared host limit is adapter metadata failure, never a protocol refusal.
\<close>

end

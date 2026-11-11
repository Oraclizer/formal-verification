theory Wire_Code_Finite_Context
  imports Wire_Code_Finite_Debit
begin

datatype code_finite_permission_pattern =
    Code_Finite_Exact_Binding nat transfer_binding
  | Code_Finite_Asset_Binding nat nat

fun code_finite_permission_matches :: "code_finite_permission_pattern \<Rightarrow> nat \<Rightarrow> transfer_binding \<Rightarrow> bool" where
  "code_finite_permission_matches (Code_Finite_Exact_Binding actor exact_binding) who binding =
    (who = actor \<and> binding = exact_binding)"
| "code_finite_permission_matches (Code_Finite_Asset_Binding actor asset) who binding =
    (who = actor \<and> binding_asset binding = asset)"

record code_finite_lock_context =
  finite_context_endpoint :: nat
  finite_context_relay_epoch :: nat
  finite_context_authority_epoch :: nat
  finite_context_version :: nat
  finite_context_permissions :: "code_finite_permission_pattern list"
  finite_context_readers :: "nat list"
  finite_context_metadata :: "((nat \<times> nat) \<times> asset_state) list"
  finite_context_metadata_locks :: "nat list"
  finite_context_restriction_clear :: "nat list"
  finite_context_dependencies :: "(nat \<times> nat list) list"
  finite_context_write_permissions :: "(nat \<times> nat \<times> nat) list"
  finite_context_spend_permissions :: "(nat \<times> source_key \<times> nat \<times> nat \<times> nat \<times> message_operation) list"

definition code_interpret_finite_context :: "code_finite_lock_context \<Rightarrow> lock_context" where
  "code_interpret_finite_context descriptor =
    \<lparr>lock_authority = \<lparr>context_endpoint = finite_context_endpoint descriptor,
        context_relay_epoch = finite_context_relay_epoch descriptor,
        context_authority_epoch = finite_context_authority_epoch descriptor,
        context_version = finite_context_version descriptor,
        context_permissions = {pair. list_ex (\<lambda>pattern.
          code_finite_permission_matches pattern (fst pair) (snd pair)) (finite_context_permissions descriptor)},
        context_readers = set (finite_context_readers descriptor)\<rparr>,
      lock_metadata = \<lparr>gs_chains = (\<lambda>domain asset. map_of (finite_context_metadata descriptor) (domain,asset)),
        gs_locks = (\<lambda>asset. asset \<in> set (finite_context_metadata_locks descriptor))\<rparr>,
      lock_restrictions = (\<lambda>asset. asset \<in> set (finite_context_restriction_clear descriptor)),
      lock_dependencies = (\<lambda>asset. case map_of (finite_context_dependencies descriptor) asset of None \<Rightarrow> [] | Some dependencies \<Rightarrow> dependencies),
      lock_write_permissions = set (finite_context_write_permissions descriptor),
      lock_spend_permissions = set (finite_context_spend_permissions descriptor)\<rparr>"

lemma the_finite_current_use_test_consumes_exact_epoch_version_and_explicit_permission_pattern:
  "current_use_allowed (lock_authority (code_interpret_finite_context descriptor)) request \<longleftrightarrow>
    request_authority_epoch request = finite_context_authority_epoch descriptor \<and>
    request_version request = finite_context_version descriptor \<and>
    list_ex (\<lambda>pattern. code_finite_permission_matches pattern (request_caller request) (request_binding request))
      (finite_context_permissions descriptor)"
  by (simp add: current_use_allowed_def code_interpret_finite_context_def)

lemma absent_finite_context_entries_have_the_named_existing_defaults:
  assumes metadata: "map_of (finite_context_metadata descriptor) (domain,asset) = None"
    and dependencies: "map_of (finite_context_dependencies descriptor) asset = None"
    and restrictions: "asset \<notin> set (finite_context_restriction_clear descriptor)"
  shows "get_reg_state (lock_metadata (code_interpret_finite_context descriptor)) domain asset = None"
    "lock_dependencies (code_interpret_finite_context descriptor) asset = []"
    "\<not> lock_restrictions (code_interpret_finite_context descriptor) asset"
  using assms by (simp_all add: code_interpret_finite_context_def get_reg_state_def get_asset_state_def)

definition code_finite_data_debit :: "code_finite_lock_context \<Rightarrow> execution_request \<Rightarrow> nat \<Rightarrow>
  (nat \<times> nat) list \<Rightarrow> code_finite_reservation_machine \<Rightarrow> (code_finite_reservation_machine \<times> reservation_reply)" where
  "code_finite_data_debit descriptor request generation versions machine =
    code_finite_execute_source_effect (code_interpret_finite_context descriptor) request generation (code_model_version_at versions) machine"

theorem the_data_only_context_and_version_wrapper_is_the_same_frozen_debit:
  "map_prod code_interpret_finite_machine id (code_finite_data_debit descriptor request generation versions machine) =
    execute_source_effect (code_interpret_finite_context descriptor) request generation (vector_lookup versions)
      (code_interpret_finite_machine machine)"
proof -
  have lookup: "code_model_version_at versions = vector_lookup versions"
    by (rule ext) (simp add: code_model_version_at_def vector_lookup_def)
  show ?thesis
    by (simp add: code_finite_data_debit_def the_finite_debit_and_frozen_debit_are_exactly_the_same_operation lookup)
qed

text \<open>
  This wrapper has no function-valued JSON argument. Finite patterns, rows
  and lists construct all old context fields and the signed version lookup.
  The Exact/Asset permission patterns are explicit representation forms;
  they are not an opaque permission=true callback. A raw source context
  needs its separate operation-grant/current-policy projection relation.
  Metadata defaults to None, dependencies to [], restriction-clear to False.
  Relay epoch/context version and binding-only coordinates remain explicit
  model coordinates; no source equality is inferred merely by choosing them.
\<close>

end

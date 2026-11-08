theory Wire_Code_JSON_Contexts
  imports Wire_Code_JSON_Primitives
begin

definition code_json_routes where
  "code_json_routes = [''Normal'',''Administrative'',''Adapter'']"

definition code_json_permissions where
  "code_json_permissions = [''Reserve'',''Dispatch'',''Debit'',''Cancel'',''Fence'',''Preempt'',
    ''ObserveTime'',''Attest'',''Credit'',''Refund'',''Reconcile'',''Write'',''PublishPrimary'']"

definition code_json_grant :: "wire_bytes \<Rightarrow> ((nat \<times> nat \<times> nat) \<times> wire_bytes) option" where
  "code_json_grant = code_json_triple code_json_u64
    (code_json_enum code_json_routes) (code_json_enum code_json_permissions)"

definition code_json_dependency :: "wire_bytes \<Rightarrow> ((nat \<times> nat list) \<times> wire_bytes) option" where
  "code_json_dependency = code_json_pair code_json_u64 (code_json_strict_list (<) code_json_u64)"

definition code_json_write_permission :: "wire_bytes \<Rightarrow> ((nat \<times> nat \<times> nat) \<times> wire_bytes) option" where
  "code_json_write_permission = code_json_triple code_json_u64 code_json_u64 code_json_u64"

definition code_json_first_field :: "string \<Rightarrow> (wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option" where
  "code_json_first_field name parse bytes = Option.bind (code_json_expect (code_json_open_key name) bytes) parse"

definition code_json_next_field :: "string \<Rightarrow> (wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option) \<Rightarrow> wire_bytes \<Rightarrow> ('a \<times> wire_bytes) option" where
  "code_json_next_field name parse bytes = Option.bind (code_json_expect (code_json_next_key name) bytes) parse"

record code_json_endpoint_context =
  json_context_endpoint :: nat
  json_context_epoch :: nat
  json_context_grants :: "(nat \<times> nat \<times> nat) list"
  json_context_dependencies :: "(nat \<times> nat list) list"
  json_context_write_permissions :: "(nat \<times> nat \<times> nat) list"

definition code_json_context :: "wire_bytes \<Rightarrow> (code_json_endpoint_context \<times> wire_bytes) option" where
  "code_json_context bytes =
    Option.bind (code_json_first_field ''endpoint'' code_json_u64 bytes) (\<lambda>(endpoint,r0).
      Option.bind (code_json_next_field ''epoch'' code_json_u64 r0) (\<lambda>(epoch,r1).
        Option.bind (code_json_next_field ''grants''
          (code_json_strict_list code_json_lex3 code_json_grant) r1) (\<lambda>(grants,r2).
          Option.bind (code_json_next_field ''dependencies''
            (code_json_strict_list (\<lambda>first second. fst first < fst second) code_json_dependency) r2) (\<lambda>(dependencies,r3).
            Option.bind (code_json_next_field ''write_permissions''
              (code_json_strict_list code_json_lex3 code_json_write_permission) r3) (\<lambda>(writes,r4).
              map_option (\<lambda>rest.
                (\<lparr>json_context_endpoint = endpoint,json_context_epoch = epoch,json_context_grants = grants,
                  json_context_dependencies = dependencies,json_context_write_permissions = writes\<rparr>,rest))
                (code_json_expect [125] r4))))))"

definition code_json_contexts :: "wire_bytes \<Rightarrow> code_json_endpoint_context list option" where
  "code_json_contexts bytes =
    Option.bind (code_json_complete
      (code_json_strict_list (\<lambda>first second. json_context_endpoint first < json_context_endpoint second) code_json_context) bytes)
      (\<lambda>values. if values = [] then None else Some values)"

record code_json_session_binding =
  json_session_principal :: nat
  json_session_epoch :: nat

definition code_json_session_binding :: "wire_bytes \<Rightarrow> (code_json_session_binding \<times> wire_bytes) option" where
  "code_json_session_binding bytes =
    Option.bind (code_json_first_field ''principal'' code_json_u64 bytes) (\<lambda>(principal,r0).
      Option.bind (code_json_next_field ''authority_epoch'' code_json_u64 r0) (\<lambda>(epoch,r1).
        map_option (\<lambda>rest. (\<lparr>json_session_principal = principal,json_session_epoch = epoch\<rparr>,rest))
          (code_json_expect [125] r1)))"

definition code_json_session_entry :: "wire_bytes \<Rightarrow> ((nat \<times> code_json_session_binding) \<times> wire_bytes) option" where
  "code_json_session_entry = code_json_pair code_json_u64 code_json_session_binding"

definition code_json_session_bindings :: "wire_bytes \<Rightarrow> (nat \<times> code_json_session_binding) list option" where
  "code_json_session_bindings bytes = code_json_complete
    (code_json_strict_list (\<lambda>first second. fst first < fst second) code_json_session_entry) bytes"

theorem accepted_governance_contexts_are_nonempty_and_in_exact_endpoint_order:
  assumes "code_json_contexts bytes = Some contexts"
  shows "contexts \<noteq> []"
    "sorted_wrt (\<lambda>first second. json_context_endpoint first < json_context_endpoint second) contexts"
proof -
  have parsed: "code_json_strict_list
      (\<lambda>first second. json_context_endpoint first < json_context_endpoint second) code_json_context bytes = Some (contexts,[])"
    using assms by (auto simp: code_json_contexts_def code_json_complete_def bind_eq_Some_conv
      split: option.splits prod.splits list.splits if_splits)
  show "contexts \<noteq> []"
    using assms by (auto simp: code_json_contexts_def bind_eq_Some_conv split: if_splits)
  show "sorted_wrt (\<lambda>first second. json_context_endpoint first < json_context_endpoint second) contexts"
    using parsed by (auto simp: code_json_strict_list_def bind_eq_Some_conv split: prod.splits if_splits)
qed

theorem accepted_session_bindings_keep_strict_session_key_order:
  assumes "code_json_session_bindings bytes = Some sessions"
  shows "sorted_wrt (\<lambda>first second. fst first < fst second) sessions"
  using assms by (auto simp: code_json_session_bindings_def code_json_complete_def code_json_strict_list_def
    bind_eq_Some_conv split: option.splits prod.splits list.splits if_splits)

text \<open>
  Only the governance schemas are parsed here.  Their keys and enum strings
  are fixed ASCII; every free scalar is u64.  The parser directly recognizes
  compact, declaration-ordered JSON and strict set/map order.  It does not
  accept an arbitrary JSON value and outsource a validation verdict.
  Equivalence to the pinned Serde schemas still requires source review,
  fixed vectors, native checks and the independent differential execution.
\<close>

end

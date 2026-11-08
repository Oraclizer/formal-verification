theory Wire_Code_Operands_Governance
  imports Wire_Code_JSON_Contexts
begin

datatype code_governance_fields =
    Code_Governance_Handover nat product_cut nat nat nat nat nat nat "code_json_endpoint_context list" wire_bytes wire_bytes
  | Code_Governance_Install nat product_cut nat "code_json_endpoint_context list"
      "(nat \<times> code_json_session_binding) list" wire_bytes

definition code_decode_governance where
  "code_decode_governance core =
    (let body = wire_operation_body core in
     if wire_deadline body \<noteq> Deadline_Absent then None
     else case (wire_words body,wire_blobs body) of (session # revision # tail,[batch,first,second]) \<Rightarrow>
       if first = [] \<or> second = [] then None
       else Option.bind (code_json_contexts batch) (\<lambda>contexts.
         let cut = \<lparr>cut_authority_epoch = wire_authority_epoch core,cut_revision = revision\<rparr>
         in if wire_opcode body = 1 then
           (case tail of [asset,previous,successor,old_session,new_session,epoch] \<Rightarrow>
              Some (Code_Governance_Handover session cut asset previous successor old_session new_session epoch contexts first second)
            | _ \<Rightarrow> None)
         else (case tail of [epoch] \<Rightarrow>
           map_option (\<lambda>sessions. Code_Governance_Install session cut epoch contexts sessions second)
             (code_json_session_bindings first)
          | _ \<Rightarrow> None))
      | _ \<Rightarrow> None)"

lemma a_governance_deadline_is_refused_before_json_parsing:
  "wire_deadline (wire_operation_body core) \<noteq> Deadline_Absent \<Longrightarrow>
    code_decode_governance core = None"
  by (simp add: code_decode_governance_def Let_def)

lemma governance_requires_two_nonempty_authorization_blobs:
  assumes "wire_blobs (wire_operation_body core) = [batch,first,second]" "first = [] \<or> second = []"
  shows "code_decode_governance core = None"
  using assms by (auto simp: code_decode_governance_def Let_def split: list.splits if_splits)

end

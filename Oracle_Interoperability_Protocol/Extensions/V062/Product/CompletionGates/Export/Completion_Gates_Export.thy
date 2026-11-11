theory Completion_Gates_Export
  imports "OIP_Completion_Gates.Completion_Gates"
begin

fun cg_flag where
  "cg_flag False = (0::nat)"
| "cg_flag True = 1"

definition cg_optional where
  "cg_optional present value = (if present = (1::nat) then Some value else None)"

fun cg_optional_words where
  "cg_optional_words None = [(0::nat),0]"
| "cg_optional_words (Some value) = [1,value]"

fun cg_reply_words where
  "cg_reply_words (CG_Waiting, complete) = [0,0,0,0,cg_flag complete]"
| "cg_reply_words (CG_Rejected, complete) = [1,0,0,0,cg_flag complete]"
| "cg_reply_words (CG_Collected (tag, commit), complete) =
    [2,tag] @ cg_optional_words commit @ [cg_flag complete]"

fun cg_decision_words where
  "cg_decision_words None = [(0::nat),0,0]"
| "cg_decision_words (Some (kind, position)) = [1,kind,position]"

definition cg_completion_nat where
  "cg_completion_nat header requested retained =
    (case header of
      [origin_domain,origin_event,lock_present,lock_domain,lock_event,row_present,
       decision_present,decision_kind,decision_position,settled_present,settled_position,
       published_present,published_position,stored_present,outcome_tag,outcome_commit_present,outcome_commit,completed] \<Rightarrow>
        (let flags = [lock_present,row_present,decision_present,settled_present,published_present,
                      stored_present,outcome_commit_present,completed];
             origin = (origin_domain,origin_event);
             owner = cg_optional lock_present (lock_domain,lock_event);
             decision = cg_optional decision_present (decision_kind,decision_position);
             row = cg_optional row_present (decision, cg_optional settled_present settled_position,
                      cg_optional published_present published_position);
             stored = cg_optional stored_present (retained, (outcome_tag, cg_optional outcome_commit_present outcome_commit));
             final = outcome_tag = 1 \<or> outcome_tag = 2 \<or> outcome_tag = 3;
             observed = cg_observe final origin owner row requested stored
         in if \<not> list_all (\<lambda>flag. flag \<le> 1) flags then None else
            Some (cg_decision_words (cg_publication row) @
                  [cg_flag (cg_ready final origin owner row),
                   cg_flag (completed = 1 \<or> snd observed)] @ cg_reply_words observed @
                  cg_reply_words (cg_observe_with False True final origin owner row requested stored) @
                  cg_reply_words (cg_observe_with True False final origin owner row requested stored)))
    | _ \<Rightarrow> None)"

definition cg_completion_integer :: "integer list \<Rightarrow> integer list \<Rightarrow> integer list \<Rightarrow> integer list option" where
  "cg_completion_integer header requested retained =
    (if list_all (\<lambda>word. word \<ge> 0) (header @ requested @ retained) then
      map_option (map integer_of_nat) (cg_completion_nat (map nat_of_integer header)
        (map nat_of_integer requested) (map nat_of_integer retained))
     else None)"

lemma cg_export_refuses_negative_words:
  assumes "\<not> list_all (\<lambda>word. word \<ge> 0) (header @ requested @ retained)"
  shows "cg_completion_integer header requested retained = None"
  unfolding cg_completion_integer_def by (simp only: if_False assms)

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms cg_export_refuses_negative_words})
  then () else error "Unexpected oracle in retained completion export"
\<close>

export_code cg_completion_integer in SML module_name OIP_Completion_Gates file_prefix "oip_completion_gates"

end

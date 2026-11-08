theory Recovery_Request_Provenance_Word
  imports "Recovery_Boundary_Semantics"
begin

text \<open>The actual Ask word is an external trace observation, not an extra machine field or guard.
  The existing ghost_disks and ghost_cuts fields supply the guarded restoration universe, and
  ghost_slot supplies Issue's logical ordinal. This observation does not delete those fields or
  classify every field named ghost as erasable.\<close>

fun ask_occurrence :: "'act boundary_event \<Rightarrow> (authority_connection \<times> 'act) list" where
  "ask_occurrence (Ask connection action) = [(connection, action)]"
| "ask_occurrence event = []"

definition actual_ask_word where
  "actual_ask_word events = concat (map ask_occurrence events)"

lemma actual_ask_word_Nil [simp]: "actual_ask_word [] = []"
  by (simp add: actual_ask_word_def)

lemma actual_ask_word_Cons [simp]:
  "actual_ask_word (event # events) = ask_occurrence event @ actual_ask_word events"
  by (simp add: actual_ask_word_def)

lemma actual_ask_word_append [simp]:
  "actual_ask_word (prefix @ suffix) = actual_ask_word prefix @ actual_ask_word suffix"
  by (simp add: actual_ask_word_def)

inductive requested_subsequence :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  empty: "requested_subsequence [] ys"
| keep: "requested_subsequence xs ys \<Longrightarrow> requested_subsequence (x # xs) (x # ys)"
| skip: "requested_subsequence xs ys \<Longrightarrow> requested_subsequence xs (y # ys)"

lemma requested_subsequence_empty_right:
  "requested_subsequence xs [] \<Longrightarrow> xs = []"
proof -
  assume sub: "requested_subsequence xs []"
  from sub show "xs = []"
    by (cases rule: requested_subsequence.cases) simp_all
qed

lemma requested_subsequence_append_right:
  "requested_subsequence xs ys \<Longrightarrow> requested_subsequence xs (ys @ suffix)"
proof (induction rule: requested_subsequence.induct)
  case empty
  show ?case by (rule requested_subsequence.empty)
next
  case keep
  show ?case
    by (simp only: append_Cons) (rule requested_subsequence.keep[OF keep.IH])
next
  case skip
  show ?case
    by (simp only: append_Cons) (rule requested_subsequence.skip[OF skip.IH])
qed

lemma requested_singleton_at_the_end:
  "requested_subsequence [x] (ys @ [x])"
proof (induction ys)
  case Nil
  have base: "requested_subsequence [] []" by (rule requested_subsequence.empty)
  show ?case
    by (simp only: append_Nil) (rule requested_subsequence.keep[OF base])
next
  case (Cons y ys)
  show ?case
    by (simp only: append_Cons) (rule requested_subsequence.skip[OF Cons.IH])
qed

lemma requested_subsequence_snoc:
  "requested_subsequence xs ys \<Longrightarrow> requested_subsequence (xs @ [x]) (ys @ [x])"
proof (induction rule: requested_subsequence.induct)
  case empty
  show ?case
    by (simp only: append_Nil) (rule requested_singleton_at_the_end)
next
  case keep
  show ?case
    by (simp only: append_Cons) (rule requested_subsequence.keep[OF keep.IH])
next
  case skip
  show ?case
    by (simp only: append_Cons) (rule requested_subsequence.skip[OF skip.IH])
qed

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms actual_ask_word_Nil actual_ask_word_Cons actual_ask_word_append
      requested_subsequence_empty_right requested_subsequence_append_right
      requested_singleton_at_the_end requested_subsequence_snoc})
  then () else error "Unexpected oracle in Recovery_Request_Provenance_Word"
\<close>

end

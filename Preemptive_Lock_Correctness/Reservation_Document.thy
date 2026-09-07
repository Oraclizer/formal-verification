(* SPDX-License-Identifier: BSD-3-Clause *)
(*<*)
theory Reservation_Document
  imports Reservation_Provider Reservation_Policy_Cases Reservation_Boundaries
begin
(*>*)

section \<open>Source Guide\<close>

text \<open>Reservation\_Types and Reservation\_Protocol contain the actual state
  and operation definitions. Reservation\_Execution defines finite interleavings
  and complete-journal replay. Ownership, Frame and Progress prove reservation
  exclusion, committed-update protection and the conditional recovery bounds.

  Source\_Non\_Reuse and Reservation\_Message\_Link connect irreversible source
  effects to the original message receiver. Lifecycle, Evidence, Settlement
  and Return\_History connect source closure, certificates, returned records
  and the actual journal. Accounting and Conservation prove account histories,
  rooted funding and the per-source allocation identity.

  Information, Lineage and Recovery give the publication-sensitive receiver
  summary, the pooled-information counterexample, and recovery of actual
  continuations. Examples, Scenarios, Mutations, Boundaries, Access and
  Policy\_Cases supply typed normal executions, rejected controls and explicit
  consumer or state-update mutations. Reservation\_Provider packages the
  proved execution contract for the subsequent protocol layer.\<close>

(*<*)
end
(*>*)

theory Rollback_Legacy_Inspection
  imports Rollback_Legacy
begin

ML \<open>
val roots = @{thms terminal_observation_agrees_with_rac
  dquencer_priority_concrete.selected_request_still_requires_rollback_authority}
val _ =
  if null (Thm_Deps.all_oracles roots)
  then Output.physical_stdout "LEGACY ADAPTER CLAIM-ROOT ORACLES: 0\n"
  else error "An oracle occurs in the legacy adapter claim-root closure"
\<close>

end

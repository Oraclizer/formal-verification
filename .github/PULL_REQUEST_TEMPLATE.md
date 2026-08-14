## Summary

Describe the smallest reviewable change and link the issue.

## Artifact impact

- [ ] No theory, theorem, locale, or assumption changes
- [ ] Theory or proof changed; exact Isabelle build result is included
- [ ] `FORMAL_MODEL_MAPPING.md` updated only for Oraclizer product/refinement changes
- [ ] `Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md` updated for companion correspondence changes
- [ ] Paper or citation metadata updated where required
- [ ] Tracked PDFs use `<Session>/release/<Session>.pdf`
- [ ] Model-level and implementation-level claims remain distinct
- [ ] Production-maintenance claims remain repository-scoped and consistent

Explain the affected formal items and public claims:

## Verification

- [ ] Isabelle `2025-2` build for every affected session, or an explicit documentation-only N/A
- [ ] External dependency revision recorded for proof-affecting changes
- [ ] `node scripts/verify-repository-health.mjs`
- [ ] No `sorry`, `oops`, credentials, local paths, or generated Isabelle output

Paste concise results or link the exact Continuous Integration run.

## Reviewer focus

Identify the assumption, proof step, model boundary, or rendering detail that
deserves the closest review.

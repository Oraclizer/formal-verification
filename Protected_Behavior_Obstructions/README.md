# Protected Behavior Obstructions

This Isabelle/HOL 2025-2 session is an explicitly `PARTIAL` companion to the
Lean protected-obstruction development. It uses locales, sets, and direct HOL
reasoning. It is not a translation of the Lean stochastic foundation, and no
Lean/Isabelle row receives `SAME` credit.

The detailed T0--T8 and stochastic boundary is in
[`CROSS_PROVER_MAPPING.md`](CROSS_PROVER_MAPPING.md).

Build from the repository root:

```text
isabelle build -c -D Protected_Behavior_Obstructions Protected_Behavior_Obstructions
```

The exact boundary is intentional:

- `protected_profile.T2_positive_endpoint` consumes the locale assumption
  `hit_pos_iff_endpoint`; Isabelle does not derive first-hit positivity from a
  transition kernel or path weights.
- `protected_profile.T3_all_sources_no_closed_trap` consumes the locale
  assumption `hit_one_iff_no_closed_trap`; Isabelle does not define the
  pre-hit reach graph or prove the finite closed-trap theorem.
- `profile_correspondence` consumes explicit cut-membership exactness. The
  Isabelle morphism has no kernel lumping, stochastic-law pushforward, or
  independently derived cut equality.
- `m2_hit` and `m3_first` are direct finite functions, not quantities derived
  from Markov kernels.
- Nitpick satisfiability runs are bounded model controls only. They are not
  theorem proofs or cross-prover equivalence evidence.

The session therefore supports set/profile algebra, assumption-transparent
T2/T3/T4/T5 consequences, set-level morphism identity/composition, profile
preorder facts, and bounded mutation witnesses. Lean remains canonical for
the stochastic foundation, kernel-derived T2/T3, stochastic morphism
exactness, quantitative transport, scheduler correspondence, and OPH
behavior-cut recovery.

No model-to-code refinement, rate, expected-time, mixing, infinite-tower, or
deployment-safety claim is made.

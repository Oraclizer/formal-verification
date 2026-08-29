# Protected Behavior Obstructions cross-prover mapping

This folder-local document records the detailed correspondence between the
canonical Lean protected-obstruction development
([FloatingPragma/observer-patch-holography](https://github.com/FloatingPragma/observer-patch-holography))
and this independent Isabelle/HOL companion. The Isabelle session is `PARTIAL / NO SAME`: a locale
assumption that repeats a Lean conclusion is not an independent derivation of
that conclusion. This session has no Oraclizer implementation target and no
Oraclizer product-refinement target.

| Obligation | Lean-canonical surface | Isabelle/HOL surface | Exact boundary |
|---|---|---|---|
| T0 profile algebra | `t0_partition`; `t0_pairwise_disjoint` | `protected_profile.T0_partition`; `T0_pairwise` | `PARTIAL`: common nested-set consequence, no shared compiled stochastic model |
| T1 empty fiber | `t1_fiber_empty_iff`; rewrite-path consequence | `protected_profile.T1_empty_fiber` | `PARTIAL`: Isabelle proves only the static target-set equality |
| T2 positive first hit | kernel and `pathWeight` derived positivity | `protected_profile.T2_positive_endpoint` | `PARTIAL`: Isabelle consumes `hit_pos_iff_endpoint` and does not construct the first-hit law |
| T3 almost-sure first hit | kernel-derived no-reachable-closed-trap equivalence | `protected_profile.T3_all_sources_no_closed_trap` | `PARTIAL`: Isabelle consumes `hit_one_iff_no_closed_trap` and has no pre-hit reach graph or kernel proof |
| T4 endpoint union | path-defined certificate and exact profile theorem | `protected_profile.T4_endpoint_union` | `PARTIAL`: Isabelle unfolds a certificate over the supplied opaque `first_hit` function |
| T5 observable collapse | kernel-connected profile collapse | `protected_profile.T5_observable_determination` | `PARTIAL`: Isabelle proves the set/profile consequence under the locale laws |
| T6 scheduler correspondence | support soundness, rewrite completeness, target normality | None | `LEAN-ONLY` |
| T7 behavior recovery | the Lean development's `RealizedBehavior` and `BehaviorCut` recovery | None | `LEAN-ONLY` |
| T8 product preorder | four concrete cut coordinates in the Lean development | `profile_LE`; `profile_LT`; reflexivity and transitivity | `PARTIAL`: `profile_correspondence` assumes exact cut membership instead of deriving it |
| Qualitative exact morphism | kernel lumping, target and quotient exactness, derived layer exactness | `exact_morphism_id`; `exact_morphism_comp` | `PARTIAL`: Isabelle has set-level protected, initial, target, and silent-relation exactness only |
| Quantitative transport | full-support pooling and stochastic pushforward | zero-weight boundary theorem only | `LEAN-ONLY` for the positive theorem; the Isabelle theorem is boundary evidence |
| M2/M3 witnesses | kernel-derived proper-target fixtures | `M2_positive_not_almost_sure`; `M3_two_positive_endpoints` | `PARTIAL`: Isabelle values are defined directly, not derived from kernels |
| Nitpick controls | No cross-prover theorem claim | four `expect = genuine` satisfiability checks | `BOUNDED SATISFIABILITY CONTROL ONLY`: never theorem proof |

## Load-bearing assumptions and limits

- `hit_pos_iff_endpoint` is the load-bearing T2 locale assumption.
- `hit_one_iff_no_closed_trap` is the load-bearing T3 locale assumption.
- `profile_correspondence` assumes exact membership correspondence for all
  four cut coordinates.
- `exact_morphism` contains no transition kernel, kernel lumping, first-hit
  law, law pushforward, or independently derived cut exactness.
- `m2_hit` and `m3_first` are direct finite functions.

The named-session build and Nitpick checks establish only the scoped results
above. They do not establish model-to-code refinement, stochastic cross-prover
equivalence, deployment safety, rates, expected times, mixing, or an infinite
tower result.

## Reproduction

From the repository root with Isabelle2025-2 installed:

```text
isabelle build -c -D Protected_Behavior_Obstructions Protected_Behavior_Obstructions
```

Review the assumptions in `Protected_Behavior_Profile.thy`, then the
identity/composition results in `Protected_Stochastic_Morphism.thy`, and
finally the bounded controls in `Protected_Obstruction_Examples.thy`.

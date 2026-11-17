# Scoped Service Commitments and Conditional Request Progress

This Isabelle/HOL session extends the open regulatory scheduler with a
commit path shared by checked rollback, regulatory priority, and ordinary
FIFO service. A current certified order is bound to the selected packet and
the compared state. Successful processing records the exact packet. Retries
of that order either return the saved result or leave the state unchanged.

The rollback proof uses the accepted intent, active permissions, selected
cells, and case budget of the committed operation. Certified finality and
replica repair share the same execution model. Evidence at the wrong cut,
conflicting finality, and partial abort evidence are refused.

For an initially coherent FIFO queue with `r` packets preceding the
pending request, a finite trace with at most `B` committed priority
services records the exact request by slot `r + B + 1` if that many
effective service slots occur. Strict raises and accepted rollbacks in
a fixed finite case set consume the corresponding level headroom and
rollback credit. The example traces show how
continuing new cases, repeated legal lowering, and repeated stale
comparisons can prevent completion.

The decoded-image relation connects the compared state, checked grant
and ledger facts, selected action, effect, and receipt. The example
histories use small synthetic values. Product adapters supply signature
verification, authoritative ledger and grant evidence, serialization,
and native compare and commit behavior.

The construction of a concrete scheduler and the proof of the result
it produces follow the proof pattern used for the fixed-program scheduler
in [Observer Patch Holography #764](https://github.com/FloatingPragma/observer-patch-holography/pull/764).
Here the selection depends on the current approved queue and the supplied
certified orders of the open model.

From the repository root with Isabelle2025-2 and the repository's AFP
ADS_Functor prerequisite installed:

~~~
isabelle build -d . REOS_Scoped_Service
~~~

<!-- SPDX-License-Identifier: BSD-3-Clause -->
# Reproduce the proof inventory

The audit session imports the complete parent and child theories. It reports
the selected statements and premises, all local named theorem dependencies,
introduced axioms, constants and simplification rules, and unused named facts.
It checks oracle dependencies for both the selected statements and every local
theorem. Its output is generated data; keep it outside the source directory.

After building `Evidence_Binding_Composition`, run from the repository root:

```bash
mkdir -p output/composition-audit
cp Evidence_Binding_Composition/Audit/ROOT output/composition-audit/
cp Evidence_Binding_Composition/Audit/*.thy output/composition-audit/
isabelle build -c -b -j 1 -o threads=1 -o parallel_proofs=0 \
  -d /path/to/ADS_Functor -d . -d output/composition-audit \
  Composition_Proof_Audit
node Evidence_Binding_Composition/verify-proof-output.mjs output/composition-audit
```

The `-c` option rebuilds this auxiliary audit session so its generated output
files are recreated even when an audit heap is already cached. The parent
proof sessions remain reusable.

`verify-proof-output.mjs` compares the extracted theorem names, statements,
premise counts and oracle results with `claims.json`. It does not replace the
Isabelle build. Dependency edges stop at the next named theorem, traversing
unnamed proof nodes; following the graph gives the named dependency closure.
The parent theories form the baseline, so unchanged parent declarations are
not reported as newly introduced axioms or constants.

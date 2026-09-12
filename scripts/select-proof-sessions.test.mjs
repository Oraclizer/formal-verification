// SPDX-License-Identifier: BSD-3-Clause
import assert from "node:assert/strict";
import { test } from "node:test";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { assertProofCoverage, selectProofSessions } from "./select-proof-sessions.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const productChain = [
  "Cross_Domain_State_Preservation",
  "Regulatory_Action_Composition",
  "Cross_Chain_Message_Integrity",
  "Preemptive_Lock_Correctness",
  "Evidence_Atomic_Binding",
  "Evidence_Binding_Composition",
];

test("every tracked theory belongs to and is registered by one session", () => {
  const graph = assertProofCoverage(root);
  assert.deepEqual(graph.registeredNames, [
    "Cross_Domain_State_Preservation",
    "Protected_Behavior_Obstructions",
    ...productChain.slice(1),
  ]);
});

test("an EAB leaf change rebuilds EAB, its composition consumer and the audit", () => {
  const selected = selectProofSessions(root, ["Evidence_Atomic_Binding/Finality_Protocol.thy"]);
  assert.deepEqual(selected.productSessions, ["Evidence_Atomic_Binding", "Evidence_Binding_Composition"]);
  assert.equal(selected.audit, true);
  assert.equal(selected.protected, false);
});

test("a composition leaf change stays at the composition and audit boundary", () => {
  const selected = selectProofSessions(root, ["Evidence_Binding_Composition/Funding_Realization.thy"]);
  assert.deepEqual(selected.productSessions, ["Evidence_Binding_Composition"]);
  assert.equal(selected.audit, true);
  assert.equal(selected.protected, false);
});

test("the independent obstruction companion does not trigger the product chain", () => {
  const selected = selectProofSessions(root, ["Protected_Behavior_Obstructions/Protected_Behavior_Profile.thy"]);
  assert.deepEqual(selected.productSessions, []);
  assert.equal(selected.audit, false);
  assert.equal(selected.protected, true);
});

test("documentation-only changes do not request a native proof build", () => {
  const selected = selectProofSessions(root, ["README.md", "Evidence_Atomic_Binding/README.md"]);
  assert.deepEqual(selected.productSessions, []);
  assert.equal(selected.audit, false);
  assert.equal(selected.protected, false);
});

test("session document inputs rebuild their session and downstream consumers", () => {
  const selected = selectProofSessions(root, ["Regulatory_Action_Composition/document/root.tex"]);
  assert.deepEqual(selected.productSessions, productChain.slice(1));
  assert.equal(selected.audit, true);
});

test("the auxiliary audit can be checked without selecting catalog descendants", () => {
  const selected = selectProofSessions(root, ["Evidence_Binding_Composition/Audit/Composition_Proof_Audit.thy"]);
  assert.deepEqual(selected.productSessions, []);
  assert.equal(selected.audit, true);
});

test("ROOTS and proof-control changes force the complete registered graph", () => {
  for (const path of ["ROOTS", ".github/workflows/proofs.yml", "scripts/select-proof-sessions.mjs"]) {
    const selected = selectProofSessions(root, [path]);
    assert.deepEqual(selected.productSessions, productChain);
    assert.equal(selected.audit, true);
    assert.equal(selected.protected, true);
    assert.equal(selected.forceAll, true);
  }
});

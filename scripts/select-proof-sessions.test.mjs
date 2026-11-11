// SPDX-License-Identifier: BSD-3-Clause
import assert from "node:assert/strict";
import { test } from "node:test";
import { readFileSync } from "node:fs";
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
const expectedOipChain = [
  "OIP_Product_Base", "OIP_Product", "OIP_Reference_Profile", "OIP_Reference_Execution",
  "OIP_Record_Reopening", "OIP_Recovery_Boundary", "OIP_Message_Code",
  "OIP_Message_Response", "OIP_Message_Egress",
  "OIP_Ordered_Maintenance_G0_Core", "OIP_Ordered_Maintenance_Entry",
  "OIP_Write_Canary_Base", "OIP_Write_Canary_Removal", "OIP_Write_Canary_DurableV6",
  "OIP_Reference_Write_Profile", "OIP_Reference_Write_AuthorityV4",
  "OIP_Reference_Write_ChecksV9", "OIP_Reference_Write_Vector_Export", "OIP_Reference_Write_Core_Seed",
  "OIP_Sync_V061_Wire_V4", "OIP_Sync_V061_Position_Definitions", "OIP_Sync_V061_Position_Proofs",
  "OIP_Sync_V061_Position_Originals", "OIP_Sync_V061_Position_Boundary",
  "OIP_Sync_V061_Position_Selection", "OIP_Sync_V061_Position_Provider", "OIP_Sync_V061_Concrete_Supplier_V2",
  "OIP_Sync_V061_Position_Direct_IR", "OIP_Sync_V061_Position_Transport", "OIP_Sync_V061_Position_Ack",
  "OIP_Sync_V061_Position_Nested_IR", "OIP_Sync_V061_Product_ABI", "OIP_Sync_V061_Ack_ABI",
  "OIP_Sync_V061_Extraction_V1", "OIP_Sync_V061_Seeds_V1", "OIP_Sync_V061_Strict_Proof_Link_V1",
  "OIP_Response_Code_Allocation", "OIP_Response_Code_Extension", "OIP_Response_Code_IntInf_Runtime",
  "OIP_Sync_V061_Mode_Product_ABI", "OIP_Current_Read_G0_Source", "OIP_Current_Read_G0_V9",
  "OIP_Current_Read_Vector_Export", "OIP_Reference_Write_Raw_Ack_Seed",
  "OIP_Response_Egress_V061_Operands", "OIP_Response_Egress_V061_V5", "OIP_Response_Egress_V061_Runtime_V7",
  "OIP_Response_Egress_V061_Preservation_V7", "OIP_Sync_V061_Typed_Artifact", "OIP_Response_Egress_V061_Export",
  "OIP_Sync_V061_Configured_Profile_ABI", "OIP_Sync_V061_Supplier_ABI", "OIP_Sync_V061_Image_Link",
  "OIP_Sync_V061_ID_Guard_ABI_V2", "OIP_Reference_Write_Capacity", "OIP_Sync_V061_Image_Binding_ABI",
  "OIP_V062_Negotiation_Core", "OIP_V062_Negotiation_G0", "OIP_V062_Negotiation_Authentication",
  "OIP_V062_Negotiation_Public_Bridge", "OIP_V062_Negotiation_Export", "OIP_Transport_Boundary_Arithmetic",
  "OIP_Transport_Boundary_Typed", "OIP_Transport_Boundary_G0", "OIP_P19_Threshold_G0",
  "OIP_P19_Threshold_Export", "OIP_P19_Configured_Registry_G0", "OIP_P19_Configured_Registry_Export",
  "OIP_Record_Reopening_Prefix_G0", "OIP_Query_Cache_Source_G0", "OIP_Query_Cache_Source_Export",
  "OIP_Query6_Capture_G0", "OIP_Query6_Capture_Export", "OIP_Settlement_Queue_G0",
  "OIP_Reserve_Debit_Finite_Base", "OIP_Reserve_Debit_Replay", "OIP_Reserve_Debit_Replay_Export",
  "OIP_Secondary_Read_G0", "OIP_Secondary_Read_Export", "OIP_Historical_Read_G0",
  "OIP_Historical_Read_Export", "OIP_Pending_Lock_Model", "OIP_Pending_Lock_Export",
  "OIP_Terminal_Record_G0", "OIP_Terminal_Record_Export", "OIP_Primary_Origin_Check",
  "OIP_Primary_Origin_Export", "OIP_Completion_Gates", "OIP_Completion_Gates_Export",
  "OIP_Regulatory_Legal_G0", "OIP_Legal_Receipt_Check", "OIP_Legal_Receipt_Export",
  "OIP_Protected_Spend_Core", "OIP_Protected_Spend_Seed", "OIP_Protected_Spend_G0",
  "OIP_Protected_Spend_Export", "OIP_V062_Handover_Seed_Frame", "OIP_V062_Handover_Typed_Model",
  "OIP_V062_Handover_G0", "OIP_V062_Handover_Finite_Model", "OIP_V062_Handover_Finite_Export",
  "OIP_V062_Handover_Recovery_Control_Base", "OIP_V062_Handover_Recovery_Control_G0", "OIP_V062_Handover_Recovery_Finite_Model",
  "OIP_V062_Handover_Recovery_Export", "OIP_V062_P13_Replay_Epoch_Base", "OIP_V062_P13_Replay_Epoch_G0",
  "OIP_Schedule_Core", "OIP_Typed_Scheduler", "OIP_Schedule_Product",
  "OIP_Schedule_Cases", "OIP_Schedule_Export", "OIP_Schedule_Boundaries",
  "OIP_Signed_Schedule_Pair", "OIP_Direct_Publication_Check", "OIP_Direct_Publication_Export",
  "OIP_Independent_Publication_Check", "OIP_Independent_Publication_Export", "OIP_Etcd_Control_Confirmation",
  "OIP_Witness_Mirror_Check",
  "OIP_V062_P13_Replay_Stored_Outcome_Repair",
  "OIP_V062_P13_Replay_Stored_Outcome_Observe_Final",
  "OIP_V062_P13_Replay_Dispatch",
  "OIP_V062_P13_Replay_Install",
  "OIP_V062_P13_Replay_Lookup",
  "OIP_V062_P13_Replay_Finite_Projection",
  "OIP_V062_P13_Replay_Export",
  "OIP_Witness_Prepare_Codec_Check",
  "OIP_Etcd_Replace_Preflight",
  "OIP_Signed_Schedule_Refusals",
  "OIP_Threshold_Raw_Identity",
  "OIP_V062_Refund_Origin_Link",
  "OIP_V062_Refund_Origin_Export",
  "OIP_Exact_Receipt_Core_Comparison",
  "OIP_Query8_Scope_Binding",
  "OIP_Lock_Clock_Model_Link",
  "OIP_ACK1_Entry",
  "OIP_Dispatch_Debit_Lease_Link",
  "OIP_Response_Signer_Parse_Probe",
  "OIP_Signed_Legal_Model_Link",
  "OIP_Go_Admitted_Operand_Model_Link",
  "OIP_Raw_Terminal_Read_Model_Link",
  "OIP_Refund_Source_Certificate_Link",
  "OIP_Signed_Owner_Read_Model_Link",
  "OIP_Active_Session_Grant_Link",
  "OIP_Signed_Cache_Capture_Model_Link",
  "OIP_Selected_Record_Reopening_Model_Link",
  "OIP_Maintenance_Selection_Replay_Link",
  "OIP_Signed_Historical_Source_Pool_Link",
  "OIP_Signed_Cancel_Fence_Model_Link",
  "OIP_Signed_Write_Reopen_Link",
  "OIP_Signed_Ordinary_Spend_Model_Link",
  "OIP_Signed_Preempt_Model_Link",
  "OIP_Signed_Publish_Primary_Model_Link",
  "OIP_V062_Signed_Handover_Model_Link",
  "OIP_Retained_Transition_Integrity_Model_Link",
  "OIP_Retained_Transition_Source_Link",
  "OIP_Concrete_Enforcement_Spend_Model_Link",
  "OIP_Source_Writer_JSON_G0",
  "OIP_Source_Writer_Phases",
  "OIP_Source_Writer_Integer_Transport",
  "OIP_Resolver_Waiting_Model_Link",
  "OIP_Unpublished_Typed_Read_Link",
  "OIP_Resolver_Unseen_Close_Link",
  "OIP_Resolver_Pending_Control_Link",
  "OIP_Source_Resume_Link",
  "OIP_Source_Commitment_Resume_Link",
  "OIP_V062_Receiver_State_Branches",
  "OIP_V062_Receiver_State_ABI",
  "OIP_Publication_Endorser_Link",
  "OIP_Witness_Prepare_Compare_Link",
  "OIP_Resolver_Current_Control_Link",
  "OIP_V062_Retained_Write_Receipt",
  "OIP_Settlement_Sync_Integrity_Link",
  "OIP_V062_Confiscate_Prior_Key",
  "OIP_V062_Response_Profile_Guard",
];
const initialGraph = assertProofCoverage(root);
const oipRegistrations = initialGraph.registeredNames.filter((name) => name.startsWith("OIP_"));
if (oipRegistrations.length) assert.deepEqual(new Set(oipRegistrations), new Set(expectedOipChain));
const oipChain = oipRegistrations.length ? expectedOipChain : [];
const completeProductChain = [...productChain, ...oipChain];
const standaloneNegotiationSessions = new Set([
  "OIP_V062_Negotiation_Core",
  "OIP_V062_Negotiation_G0",
  "OIP_V062_Negotiation_Authentication",
  "OIP_V062_Negotiation_Export",
]);
const oipProductDescendants = oipChain.filter((name) => !standaloneNegotiationSessions.has(name));

test("every tracked theory belongs to and is registered by one session", () => {
  const graph = assertProofCoverage(root);
  assert.deepEqual(graph.registeredNames, [
    "Cross_Domain_State_Preservation",
    "Protected_Behavior_Obstructions",
    ...productChain.slice(1),
    ...oipRegistrations,
  ]);
  assert.deepEqual(graph.byName.get("Cross_Domain_State_Preservation").dependencies,
    ["HOL-Library", "HOL-Eisbach", "ADS_Functor"]);
});

test("an EAB leaf change rebuilds EAB, its composition consumer and the audit", () => {
  const selected = selectProofSessions(root, ["Evidence_Atomic_Binding/Finality_Protocol.thy"]);
  assert.deepEqual(selected.productSessions, ["Evidence_Atomic_Binding", "Evidence_Binding_Composition", ...oipProductDescendants]);
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

test("standalone OIP validation inputs retain an exact external boundary", () => {
  if (!oipChain.length) return;
  const prefix = "Oracle_Interoperability_Protocol/Validation/V061";
  const inventory = JSON.parse(readFileSync(resolve(root, prefix, "input-manifest.json"), "utf8"));
  const inputs = inventory.files.filter(({ path }) => path.endsWith(".ML")).map(({ path }) => `${prefix}/${path}`);
  assert.equal(inputs.length, 10);
  assert.deepEqual(selectProofSessions(root, inputs).productSessions, []);
  assert.throws(() => selectProofSessions(root, [`${prefix}/drivers/unlisted.ML`]), /outside every declared session/);
});

test("session document inputs rebuild their session and downstream consumers", () => {
  const selected = selectProofSessions(root, ["Regulatory_Action_Composition/document/root.tex"]);
  assert.deepEqual(selected.productSessions, [...productChain.slice(1), ...oipProductDescendants]);
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
    assert.deepEqual(selected.productSessions, completeProductChain);
    assert.equal(selected.audit, true);
    assert.equal(selected.protected, true);
    assert.equal(selected.forceAll, true);
  }
});

test("a graph-control change safely covers proof paths removed by a migration", () => {
  const selected = selectProofSessions(root, ["Removed_Session/Old_Theory.thy", "ROOTS"]);
  assert.deepEqual(selected.productSessions, completeProductChain);
  assert.equal(selected.audit, true);
  assert.equal(selected.protected, true);
  assert.equal(selected.forceAll, true);
});

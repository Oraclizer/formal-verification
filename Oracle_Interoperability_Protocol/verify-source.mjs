// SPDX-License-Identifier: BSD-3-Clause
// Content/form integrity only; this does not execute or certify a proof build.
import { createHash } from "node:crypto";
import { lstatSync, readFileSync, readdirSync } from "node:fs";
import { dirname, isAbsolute, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const NAMESPACE = "Oracle_Interoperability_Protocol";
// Reject unfinished proof/axiom tokens anywhere on a line, including inline sorry.
// Other untrusted forms retain the existing Proofs policy.
const UNTRUSTED_LINE = /\b(?:sorry|oops|axiomatization)\b|^\s*oracle\b|\bby\s+eval\b|\bnative_decide\b|\bskip_proof\b|\bsledgehammer\b|\bsmt_oracle\b/;
const COMMON_LOCK = ["lock_version", "binding_status", "artifact_transport", "repository", "wire_schema", "abi", "scope", "entrypoint", "natural_refinement", "runtime_source_hash", "verified_export_sha256", "public_namespace", "identity_function", "files"];
const ORIGIN_KEYS = ["origin_version", "kernel_inputs_sha256", "wire_schema", "abi", "scope", "entrypoint", "natural_refinement", "runtime_source_hash", "public_namespace", "identity_function", "model_sha256", "driver_sha256", "diagnostics_sha256"];
const PROFILES = {
  typed: {
    lock: "model-artifact.lock.json", abi: "intinf-wire-values-v2", scope: "wire-v6-general-33-values",
    entrypoint: "OIP_Wire_Oracle_V061.sync_v061_nested_transport_flat", identity: "OIP_Wire_Oracle_V061.sync_v061_typed_model_identity",
    names: { model: "oip_wire_oracle.ML", driver: "mirror-driver.ML", origin: "export-origin.json", diagnostics: "compiler-diagnostics.json" },
  },
  full: {
    lock: "wire-response-artifact.lock.json", abi: "intinf-response-full-v2", scope: "wire-response-sender-client-v2",
    entrypoint: "OIP_Wire_Response_Boundary.code_response_egress_flat_oracle", identity: "OIP_Wire_Response_Boundary.code_response_full_model_identity",
    names: { model: "oip_wire_response_full.ML", driver: "response-full-driver.ML", origin: "response-full-origin.json", diagnostics: "response-full-diagnostics.json" },
  },
  threshold: {
    lock: "threshold-raw-artifact.lock.json", abi: "intinf-threshold-raw-v1",
    scope: "wire-v6-threshold-raw-observed-primitives",
    entrypoint: "OIP_Threshold_Raw_ABI.threshold_raw_packet", identity: "OIP_Threshold_Raw_ABI.threshold_raw_model_identity",
    names: { model: "oip_threshold_raw_abi.ML", driver: "threshold-raw-driver.ML", origin: "threshold-raw-origin.json", diagnostics: "threshold-raw-diagnostics.json" },
  },
};
const LOCK_EXTRAS = { typed: ["corpus"], full: ["input_schema", "egress_entries"], threshold: ["fixtures"] };
const THRESHOLD_FIXTURES = {
  packets: { path: "tests/vectors/threshold-raw/input.jsonl", rows: 22 },
  signature_observations: { path: "tests/vectors/threshold-raw/primitive-observations.jsonl", rows: 22 },
  key_observations: { path: "tests/vectors/threshold-raw/key-observations.json", rows: 3 },
};
const EGRESS_ENTRIES = {
  queries: "code_response_egress_queries_flat", boundary_queries: "code_response_encode_boundary_queries_flat",
  sender: "code_response_egress_flat_oracle", boundary_sender: "code_response_encode_boundary_flat_oracle",
  prefix: "code_response_egress_prefix_flat", boundary_prefix: "code_response_encode_boundary_prefix_flat",
  client_queries: "code_response_admit_queries_flat", client: "code_response_admit_flat_oracle", combined: "code_response_egress_and_admit_flat_oracle",
};
export const ARTIFACT_PATHS = Object.entries(PROFILES).flatMap(([bundle, profile]) => [
  ...Object.values(profile.names).map((name) => `artifacts/${bundle}/${name}`), `artifacts/locks/${profile.lock}`,
]).sort();

function need(condition, category, message) {
  if (!condition) throw Error(`OIP_${category}: ${message}`);
}
function exact(value, keys, category, label) {
  need(value && typeof value === "object" && !Array.isArray(value) && JSON.stringify(Object.keys(value).sort()) === JSON.stringify([...keys].sort()), category, `${label}: missing or unexpected fields`);
}
function equal(left, right, category, label) {
  need(typeof left === typeof right && left === right, category, `${label}: mismatch`);
}
function digest(value, length, category, label) {
  need(typeof value === "string" && new RegExp(`^[0-9a-f]{${length}}$`).test(value), category, `${label}: bound lowercase digest required`);
}
const sha256 = (raw) => createHash("sha256").update(raw).digest("hex");
const gitBlob = (raw) => createHash("sha1").update(Buffer.from(`blob ${raw.length}\0`)).update(raw).digest("hex");

function safePath(root, name, category) {
  need(typeof name === "string" && name && !isAbsolute(name) && !/[\\:\0]/.test(name) && name.split("/").every((part) => part && part !== "." && part !== ".."), category, "unsafe relative path");
  let path = root;
  const parts = name.split("/");
  for (let index = 0; index < parts.length; index += 1) {
    path = resolve(path, parts[index]);
    let info;
    try { info = lstatSync(path); } catch { need(false, category, `missing input: ${name}`); }
    need(!info.isSymbolicLink() && (index === parts.length - 1 ? info.isFile() : info.isDirectory()), category, `non-regular input: ${name}`);
  }
  return path;
}
function read(root, name, category) { return readFileSync(safePath(root, name, category)); }
function json(raw, category, name) {
  try { return JSON.parse(raw.toString("utf8")); } catch { need(false, category, `invalid JSON: ${name}`); }
}
function files(root, prefix = "") {
  const result = [];
  for (const entry of readdirSync(resolve(root, prefix), { withFileTypes: true })) {
    const name = prefix ? `${prefix}/${entry.name}` : entry.name;
    need(!entry.isSymbolicLink(), "SOURCE_INVENTORY", `aliased input: ${name}`);
    if (entry.isDirectory()) result.push(...files(root, name));
    else { need(entry.isFile(), "SOURCE_INVENTORY", `non-regular entry: ${name}`); result.push(name); }
  }
  return result;
}
function sameSet(actual, expected, category, label) {
  need(new Set(actual).size === actual.length && JSON.stringify([...actual].sort()) === JSON.stringify([...expected].sort()), category, `${label}: missing, extra or duplicate path`);
}

export function verifySource(namespaceRoot) {
  const root = resolve(namespaceRoot);
  const inventory = json(read(root, "source-manifest.json", "SOURCE_INVENTORY"), "SOURCE_INVENTORY", "source-manifest.json");
  exact(inventory, ["format", "namespace", "files"], "SOURCE_INVENTORY", "compiler inventory");
  equal(inventory.format, "oip-public-formal-source-inventory-v1", "SOURCE_INVENTORY", "compiler inventory format");
  equal(inventory.namespace, NAMESPACE, "SOURCE_INVENTORY", "compiler namespace");
  const actualTheories = files(root).filter((name) => name.endsWith(".thy")).sort();
  // This has the same source-form policy as the pre-existing grep. Inspect it
  // before hashes so the auditor's axiomatization control has its own cause.
  for (const name of actualTheories) {
    const lines = read(root, name, "SOURCE_INVENTORY").toString("utf8").split(/\r?\n/);
    const bad = lines.findIndex((line) => UNTRUSTED_LINE.test(line));
    need(bad === -1, "PROOF_SOURCE_FORM", `untrusted proof source form: ${name}:${bad + 1}`);
  }
  need(Array.isArray(inventory.files) && inventory.files.length === 552 && actualTheories.length === 551, "SOURCE_INVENTORY", "ROOT plus exactly 551 theory inputs required");
  sameSet(inventory.files.map((row) => row.path), ["ROOT", ...actualTheories], "SOURCE_INVENTORY", "exact compiler inventory");
  for (const row of inventory.files) {
    exact(row, ["path", "bytes", "sha256"], "SOURCE_INVENTORY", "compiler input");
    digest(row.sha256, 64, "SOURCE_INVENTORY", row.path);
    need(Number.isSafeInteger(row.bytes) && row.bytes > 0, "SOURCE_INVENTORY", `invalid byte count: ${row.path}`);
    const raw = read(root, row.path, "SOURCE_INVENTORY");
    need(raw.length === row.bytes && sha256(raw) === row.sha256, "SOURCE_INVENTORY", `compiler bytes/SHA256 differ: ${row.path}`);
  }

  // This separate metadata does not alter the 552-file compiler inventory or
  // any model identity. The artifact inventory includes all three lock files.
  const artifacts = json(read(root, "artifact-manifest.json", "ARTIFACT_INVENTORY"), "ARTIFACT_INVENTORY", "artifact-manifest.json");
  exact(artifacts, ["format", "namespace", "files"], "ARTIFACT_INVENTORY", "artifact inventory");
  equal(artifacts.format, "oip-public-model-artifact-inventory-v1", "ARTIFACT_INVENTORY", "artifact inventory format");
  equal(artifacts.namespace, NAMESPACE, "ARTIFACT_INVENTORY", "artifact namespace");
  need(Array.isArray(artifacts.files) && artifacts.files.length === ARTIFACT_PATHS.length, "ARTIFACT_INVENTORY", "exact public artifact inventory required");
  sameSet(artifacts.files.map((row) => row.path), ARTIFACT_PATHS, "ARTIFACT_INVENTORY", "artifact declared paths");
  sameSet(files(root, "artifacts"), ARTIFACT_PATHS, "ARTIFACT_INVENTORY", "artifact on-disk paths");
  const rawFiles = new Map();
  for (const row of artifacts.files) {
    exact(row, ["path", "bytes", "sha256", "git_blob_sha1"], "ARTIFACT_PIN", "artifact content pin");
    digest(row.sha256, 64, "ARTIFACT_PIN", row.path); digest(row.git_blob_sha1, 40, "ARTIFACT_PIN", row.path);
    need(Number.isSafeInteger(row.bytes) && row.bytes > 0 && row.bytes <= 16 * 1024 * 1024, "ARTIFACT_PIN", `invalid artifact size: ${row.path}`);
    const raw = read(root, row.path, "ARTIFACT_PIN");
    need(raw.length === row.bytes && sha256(raw) === row.sha256 && gitBlob(raw) === row.git_blob_sha1, "ARTIFACT_PIN", `artifact bytes/SHA256/GitBlob differ: ${row.path}`);
    rawFiles.set(row.path, raw);
  }
  const locks = [], origins = [];
  for (const [bundle, profile] of Object.entries(PROFILES)) {
    const lockName = `artifacts/locks/${profile.lock}`;
    const lock = json(rawFiles.get(lockName), "ARTIFACT_SCHEMA", lockName);
    exact(lock, [...COMMON_LOCK, ...LOCK_EXTRAS[bundle]], "ARTIFACT_SCHEMA", `${bundle} lock`);
    for (const [key, expected] of Object.entries({ lock_version: 1, binding_status: "bound", artifact_transport: "github-git-blob-v1", repository: "Oraclizer/formal-verification", wire_schema: 1, abi: profile.abi, scope: profile.scope, entrypoint: profile.entrypoint, natural_refinement: "HOL-Library.Code_Target_Nat", public_namespace: NAMESPACE, identity_function: profile.identity })) equal(lock[key], expected, "ARTIFACT_SCHEMA", `${bundle} ${key}`);
    digest(lock.runtime_source_hash, 64, "ARTIFACT_SCHEMA", "runtime source hash");
    digest(lock.verified_export_sha256, 64, "ARTIFACT_SCHEMA", "verified export hash");
    if (bundle === "typed") {
      exact(lock.corpus, ["path", "rows", "sha256"], "ARTIFACT_SCHEMA", "typed corpus");
      equal(lock.corpus.path, "tests/vectors/wire-operations.jsonl", "ARTIFACT_SCHEMA", "typed corpus path");
      equal(lock.corpus.rows, 692, "ARTIFACT_SCHEMA", "typed corpus rows");
      digest(lock.corpus.sha256, 64, "ARTIFACT_SCHEMA", "typed corpus hash");
    } else if (bundle === "full") {
      equal(lock.input_schema, "tests/response-full-abi.json", "ARTIFACT_SCHEMA", "Full input schema");
      exact(lock.egress_entries, Object.keys(EGRESS_ENTRIES), "ARTIFACT_SCHEMA", "Full entries");
      for (const [key, value] of Object.entries(EGRESS_ENTRIES)) equal(lock.egress_entries[key], value, "ARTIFACT_SCHEMA", `Full entry ${key}`);
    } else {
      exact(lock.fixtures, Object.keys(THRESHOLD_FIXTURES), "ARTIFACT_SCHEMA", "threshold fixtures");
      for (const [role, fixture] of Object.entries(THRESHOLD_FIXTURES)) {
        const pin = lock.fixtures[role];
        exact(pin, ["path", "rows", "sha256"], "ARTIFACT_SCHEMA", `threshold ${role}`);
        equal(pin.path, fixture.path, "ARTIFACT_SCHEMA", `threshold ${role} path`);
        equal(pin.rows, fixture.rows, "ARTIFACT_SCHEMA", `threshold ${role} rows`);
        digest(pin.sha256, 64, "ARTIFACT_SCHEMA", `threshold ${role} hash`);
      }
    }
    need(Array.isArray(lock.files) && lock.files.length === 4, "ARTIFACT_SCHEMA", `${bundle} requires four roles`);
    sameSet(lock.files.map((row) => row.role), Object.keys(profile.names), "ARTIFACT_SCHEMA", `${bundle} roles`);
    const members = new Map();
    for (const member of lock.files) {
      exact(member, ["role", "name", "git_blob_sha1", "sha256", "bytes"], "ARTIFACT_SCHEMA", `${bundle} member`);
      equal(member.name, profile.names[member.role], "ARTIFACT_SCHEMA", `${bundle} role name`);
      const raw = rawFiles.get(`artifacts/${bundle}/${member.name}`);
      need(Number.isSafeInteger(member.bytes) && raw.length === member.bytes && sha256(raw) === member.sha256 && gitBlob(raw) === member.git_blob_sha1, "ARTIFACT_LINK", `${bundle}/${member.role} differs from lock pin`);
      members.set(member.role, member);
    }
    equal(lock.verified_export_sha256, members.get("model").sha256, "ARTIFACT_LINK", `${bundle} verified model`);
    const origin = json(rawFiles.get(`artifacts/${bundle}/${profile.names.origin}`), "ARTIFACT_SCHEMA", `${bundle} origin`);
    exact(origin, ORIGIN_KEYS, "ARTIFACT_SCHEMA", `${bundle} origin13`);
    equal(origin.origin_version, 1, "ARTIFACT_SCHEMA", `${bundle} origin version`);
    digest(origin.kernel_inputs_sha256, 64, "ARTIFACT_SCHEMA", `${bundle} kernel input hash`);
    for (const key of ["wire_schema", "abi", "scope", "entrypoint", "natural_refinement", "runtime_source_hash", "public_namespace", "identity_function"]) equal(origin[key], lock[key], "ARTIFACT_LINK", `${bundle} origin ${key}`);
    for (const role of ["model", "driver", "diagnostics"]) equal(origin[`${role}_sha256`], members.get(role).sha256, "ARTIFACT_LINK", `${bundle} origin ${role}`);
    const diagnostics = json(rawFiles.get(`artifacts/${bundle}/${profile.names.diagnostics}`), "ARTIFACT_SCHEMA", `${bundle} diagnostics`);
    exact(diagnostics, ["schema", "model_sha256", "driver_sha256", "allowed"], "ARTIFACT_SCHEMA", `${bundle} diagnostics`);
    equal(diagnostics.schema, "oip-compiler-diagnostics-v1", "ARTIFACT_SCHEMA", `${bundle} diagnostic schema`);
    for (const role of ["model", "driver"]) equal(diagnostics[`${role}_sha256`], members.get(role).sha256, "ARTIFACT_LINK", `${bundle} diagnostic ${role}`);
    need(Array.isArray(diagnostics.allowed), "ARTIFACT_SCHEMA", `${bundle} exact diagnostic blocks required`);
    for (const block of diagnostics.allowed) {
      exact(block, ["stream", "lines", "maximum"], "ARTIFACT_SCHEMA", `${bundle} diagnostic block`);
      need(["stdout", "stderr"].includes(block.stream) && Array.isArray(block.lines) && block.lines.length > 0 && block.lines.every((line) => typeof line === "string" && !/[\r\n]/.test(line)) && Number.isSafeInteger(block.maximum) && block.maximum >= 1 && block.maximum <= 4, "ARTIFACT_SCHEMA", `${bundle} malformed exact diagnostic block`);
      for (const line of block.lines) {
        const residue = line.replaceAll("{model_path}", "").replaceAll("{driver_path}", "");
        need(!/[{}]/.test(residue) && !line.startsWith("OIP-"), "ARTIFACT_SCHEMA", `${bundle} diagnostics cannot consume protocol or arbitrary templates`);
      }
    }
    locks.push(lock); origins.push(origin);
  }
  for (const lock of locks.slice(1)) equal(lock.runtime_source_hash, locks[0].runtime_source_hash, "ARTIFACT_LINK", "common runtime source");
  for (const origin of origins.slice(1)) equal(origin.kernel_inputs_sha256, origins[0].kernel_inputs_sha256, "ARTIFACT_LINK", "common kernel input seal");
  const sealRaw = read(root, "Validation/V061/kernel-input-seal.json", "ARTIFACT_LINK");
  const seal = json(sealRaw, "ARTIFACT_LINK", "v0.6.1 compiler input seal");
  equal(seal.format, "oip-v061-compiler-input-seal-v1", "ARTIFACT_LINK", "kernel seal format");
  equal(seal.namespace, NAMESPACE, "ARTIFACT_LINK", "kernel seal namespace");
  equal(sha256(sealRaw), origins[0].kernel_inputs_sha256, "ARTIFACT_LINK", "checked common compiler seal");
  equal(seal.source_manifest_sha256, sha256(read(root, "source-manifest.json", "SOURCE_INVENTORY")),
    "ARTIFACT_LINK", "seal compiler source manifest");
  equal(seal.root_sha256, sha256(read(root, "ROOT", "SOURCE_INVENTORY")), "ARTIFACT_LINK", "seal ROOT");
  equal(seal.compiler_inputs, inventory.files.length, "ARTIFACT_LINK", "seal compiler input count");
  need(Array.isArray(seal.targets) && ["OIP_Sync_V061_Typed_Artifact", "OIP_Response_Egress_V061_Export", "OIP_Threshold_Raw_Identity"]
    .every((name) => seal.targets.includes(name)), "ARTIFACT_LINK", "all checked export targets are required");
  return { compiler_files: inventory.files.length, theory_files: actualTheories.length, public_artifact_files: ARTIFACT_PATHS.length, runtime_source_hash: locks[0].runtime_source_hash, proof_or_model_execution: false };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const args = process.argv.slice(2);
    need(args.length === 0 || (args.length === 2 && args[0] === "--root"), "USAGE", "use verify-source.mjs [--root namespace]");
    const result = verifySource(args.length ? args[1] : dirname(fileURLToPath(import.meta.url)));
    console.log(`source verification PASS: OIP ${result.compiler_files} compiler inputs, ${result.public_artifact_files} artifact content pins; no proof/model execution`);
  } catch (error) { console.error(error.message); process.exitCode = 1; }
}

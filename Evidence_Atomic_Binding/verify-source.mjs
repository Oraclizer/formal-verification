// SPDX-License-Identifier: BSD-3-Clause
import { createHash } from "node:crypto";
import { readFileSync, readdirSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(fileURLToPath(import.meta.url));
const read = (path) => readFileSync(resolve(root, path), "utf8");
const manifest = JSON.parse(read("source-manifest.json"));
const actual = readdirSync(root).filter((name) => name.endsWith(".thy")).sort();
const declared = manifest.files.map((file) => file.path).filter((name) => name.endsWith(".thy")).sort();
if (JSON.stringify(actual) !== JSON.stringify(declared)) throw Error("Theory inventory mismatch");
const sessionRoot = read("ROOT");
if (!sessionRoot.includes("session Evidence_Atomic_Binding = Preemptive_Lock_Correctness +")) {
  throw Error("Unexpected session parent");
}
for (const file of manifest.files) {
  if (file.path.startsWith("/") || file.path.split(/[\\/]/).includes("..")) throw Error("Invalid manifest path");
  const digest = createHash("sha256").update(readFileSync(resolve(root, file.path))).digest("hex");
  if (digest !== file.sha256) throw Error(`Source digest mismatch: ${file.path}`);
  if (file.path.endsWith(".thy") && !sessionRoot.split(/\r?\n/).some((line) => line.trim() === file.path.slice(0, -4))) {
    throw Error(`Theory absent from ROOT: ${file.path}`);
  }
}
const parent = createHash("sha256").update(readFileSync(resolve(root, "../Preemptive_Lock_Correctness/source-manifest.json"))).digest("hex");
if (parent !== manifest.parent_source_manifest_sha256) throw Error("Parent source manifest changed");
const claims = JSON.parse(read("claims.json"));
if (claims.result_level !== "formal_model" || claims.implementation_refinement !== "NOT_ESTABLISHED") throw Error("Unreviewed claim scope");
if (new Set(claims.claims.map((claim) => claim.id)).size !== claims.claims.length) throw Error("Duplicate claim identity");
for (const claim of claims.claims) {
  if (claim.oracle_dependencies !== 0 || !claim.statement || !actual.includes(claim.file)) throw Error("Invalid recorded claim");
  const name = claim.theorem.split(".").at(-1).replace(/\(\d+\)$/, "");
  if (!new RegExp(`(?:lemma|theorem)\\s+${name}\\b`).test(read(claim.file))) throw Error(`Claim declaration missing: ${claim.theorem}`);
}
const obligations = JSON.parse(read("product-obligations.json"));
if (obligations.implementation_refinement !== "NOT_ESTABLISHED") throw Error("Unreviewed runtime status");
if (obligations.obligations.some((row) => row.compiled_consumer.status !== "UNVERIFIED")) throw Error("Unreviewed compiled consumer");
console.log(`source verification PASS: ${manifest.files.length} files, ${actual.length} theories, ${claims.claims.length} recorded claim roots`);

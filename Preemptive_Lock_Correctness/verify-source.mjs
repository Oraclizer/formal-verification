// SPDX-License-Identifier: BSD-3-Clause
import { createHash } from "node:crypto";
import { readFileSync, readdirSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(fileURLToPath(import.meta.url));
const manifest = JSON.parse(readFileSync(resolve(root, "source-manifest.json"), "utf8"));
const actual = readdirSync(root).filter((name) => name.endsWith(".thy")).sort();
const declared = manifest.files.map((file) => file.path).filter((name) => name.endsWith(".thy")).sort();
if (JSON.stringify(actual) !== JSON.stringify(declared)) throw Error("Theory inventory mismatch");
const sessionRoot = readFileSync(resolve(root, "ROOT"), "utf8");
if (!sessionRoot.includes("session Preemptive_Lock_Correctness = Cross_Chain_Message_Integrity +")) {
  throw Error("Unexpected session parent");
}
for (const file of manifest.files) {
  const digest = createHash("sha256").update(readFileSync(resolve(root, file.path))).digest("hex");
  if (digest !== file.sha256) throw Error(`Source digest mismatch: ${file.path}`);
  if (file.path.endsWith(".thy") && !sessionRoot.includes(file.path.slice(0, -4))) {
    throw Error(`Theory absent from ROOT: ${file.path}`);
  }
}
const claims = JSON.parse(readFileSync(resolve(root, "claims.json"), "utf8"));
if (claims.claims.some((claim) => claim.oracle_dependencies !== 0)) throw Error("Claim oracle dependency");
const obligations = JSON.parse(readFileSync(resolve(root, "refinement-obligations.json"), "utf8"));
if (obligations.runtime_refinement !== "PLANNED") throw Error("Unreviewed runtime status");
console.log(`source verification PASS: ${manifest.files.length} files, ${actual.length} theories, ${claims.claims.length} recorded claim roots`);

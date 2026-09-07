// SPDX-License-Identifier: BSD-3-Clause
import { readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = dirname(fileURLToPath(import.meta.url));
if (process.argv.length !== 3) throw Error("Usage: node verify-proof-output.mjs AUDIT_OUTPUT_DIRECTORY");
const output = resolve(process.argv[2]);
const claims = JSON.parse(readFileSync(resolve(root, "claims.json"), "utf8")).claims;
const lines = readFileSync(resolve(output, "claim-roots.tsv"), "utf8").trimEnd().split(/\r?\n/);
if (lines.shift() !== "label\ttheorem\toracles\tpremises\tstatement") throw Error("Unexpected proof output format");
const actual = new Map();
for (const line of lines) {
  const fields = line.split("\t");
  if (fields.length !== 5 || actual.has(fields[0])) throw Error("Invalid or duplicate proof output row");
  actual.set(fields[0], fields);
}
if (actual.size !== claims.length) throw Error("Proof output inventory mismatch");
for (const claim of claims) {
  const row = actual.get(claim.id);
  if (!row || row[1] !== claim.theorem || row[2] !== "0" ||
      Number(row[3]) !== claim.premise_count || row[4] !== claim.statement) {
    throw Error(`Proof output differs from the recorded statement: ${claim.id}`);
  }
}
if (readFileSync(resolve(output, "audit-progress.txt"), "utf8").trim() !== "complete") {
  throw Error("Audit extraction did not complete");
}
if (readFileSync(resolve(output, "all-local-oracles.txt"), "utf8").trim() !== "0") {
  throw Error("A local theorem has an oracle dependency");
}
console.log(`proof output verification PASS: ${claims.length} statements and zero local oracle dependencies`);

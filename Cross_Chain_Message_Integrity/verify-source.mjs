// SPDX-License-Identifier: BSD-3-Clause
import { createHash } from "node:crypto";
import { readFileSync, readdirSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
const root = dirname(fileURLToPath(import.meta.url));
const manifest = JSON.parse(readFileSync(resolve(root, "source-manifest.json"), "utf8"));
const actualTheories = readdirSync(root).filter((name) => name.endsWith(".thy")).sort();
const declaredTheories = manifest.files.map((f) => f.path).filter((p) => p.endsWith(".thy")).sort();
if (JSON.stringify(actualTheories) !== JSON.stringify(declaredTheories)) throw Error("Theory inventory mismatch");
const sessionRoot = readFileSync(resolve(root, "ROOT"), "utf8");
for (const file of manifest.files) {
  const bytes = readFileSync(resolve(root, file.path));
  const digest = createHash("sha256").update(bytes).digest("hex");
  if (digest !== file.sha256) throw Error(`Source digest mismatch: ${file.path}`);
  if (file.path.endsWith(".thy") && !sessionRoot.includes(file.path.slice(0, -4))) {
    throw Error(`Theory absent from ROOT: ${file.path}`);
  }
}
if (!sessionRoot.includes("session Cross_Chain_Message_Integrity = Regulatory_Action_Composition +")) {
  throw Error("Unexpected session parent");
}
console.log(`source verification PASS: ${manifest.files.length} files, ${actualTheories.length} registered theories`);

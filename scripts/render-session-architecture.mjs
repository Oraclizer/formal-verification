// SPDX-License-Identifier: BSD-3-Clause
// Write the registered session graph as Mermaid. The session map in docs/assets
// draws the base sessions as stations and one square per remaining session;
// scripts/verify-repository-health.mjs checks those drawings against this graph.
import { writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { assertProofCoverage } from "./select-proof-sessions.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const assets = join(root, "docs/assets");
const graph = assertProofCoverage(root);
const edges = graph.registeredNames.flatMap((name) =>
  graph.byName.get(name).dependencies.map((dependency) => [dependency, name]));

const aliases = (name) => name.replaceAll("-", "_");
const names = [...new Set(edges.flat())].sort();
writeFileSync(join(assets, "session-architecture.mmd"), [
  "%% Generated from the registered session graph. Arrows run from dependency to importer.",
  "flowchart TB",
  ...names.map((name) => `    ${aliases(name)}["${name}"]`),
  ...edges.map(([from, to]) => `    ${aliases(from)} --> ${aliases(to)}`),
  "",
].join("\n"));
console.log(`Wrote ${graph.registeredNames.length} registered sessions and ${edges.length} dependency edges.`);

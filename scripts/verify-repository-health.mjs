// SPDX-License-Identifier: BSD-3-Clause

import { readFileSync, readdirSync, statSync } from "node:fs";
import { dirname, extname, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const failures = [];
const required = [
  "README.md",
  "LICENSE",
  "SECURITY.md",
  "CONTRIBUTING.md",
  "CODE_OF_CONDUCT.md",
  "SUPPORT.md",
  "GOVERNANCE.md",
  "DISCLAIMER.md",
  "CITATION.cff",
  "CHANGELOG.md",
  "FORMAL_MODEL_MAPPING.md",
  "ROOTS",
  "Cross_Domain_State_Preservation/ROOT",
  "Cross_Domain_State_Preservation/release/Cross_Domain_State_Preservation.pdf",
  "Cross_Domain_State_Preservation/release/manifest.json",
  "Regulatory_Action_Composition/ROOT",
  "Regulatory_Action_Composition/Regulatory_Action_Composition.thy",
  "Regulatory_Action_Composition/release/Regulatory_Action_Composition.pdf",
  "Regulatory_Action_Composition/release/manifest.json",
  "docs/assets/formal-verification-banner.svg",
  ".github/PULL_REQUEST_TEMPLATE.md",
  ".github/dependabot.yml",
  ".github/ISSUE_TEMPLATE/config.yml",
  ".github/ISSUE_TEMPLATE/proof-review.yml",
  ".github/ISSUE_TEMPLATE/documentation.yml",
];
const excluded = new Set([".git", ".isabelle", "output"]);
const textExtensions = new Set([
  ".bib",
  ".cff",
  ".json",
  ".md",
  ".mjs",
  ".svg",
  ".tex",
  ".thy",
  ".yml",
  ".yaml",
]);

function walk(path) {
  const rel = relative(root, path).replaceAll("\\", "/");
  if (rel && rel.split("/").some((part) => excluded.has(part))) return [];
  if (statSync(path).isFile()) return [path];
  return readdirSync(path)
    .sort()
    .flatMap((entry) => walk(resolve(path, entry)));
}

for (const path of required) {
  try {
    if (!statSync(resolve(root, path)).isFile()) failures.push(`required path is not a file: ${path}`);
  } catch {
    failures.push(`missing required file: ${path}`);
  }
}

const files = walk(root);
for (const absolute of files.filter((path) => extname(path).toLowerCase() === ".pdf")) {
  const path = relative(root, absolute).replaceAll("\\", "/");
  const match = /^([^/]+)\/release\/([^/]+)\.pdf$/.exec(path);
  if (!match || match[1] !== match[2]) {
    failures.push(`PDF release must be <Session>/release/<Session>.pdf: ${path}`);
  }
}

for (const absolute of files) {
  const path = relative(root, absolute).replaceAll("\\", "/");
  if (!textExtensions.has(extname(path).toLowerCase())) continue;
  const bytes = readFileSync(absolute);
  const text = bytes.toString("utf8");
  if (bytes.length >= 3 && bytes[0] === 0xef && bytes[1] === 0xbb && bytes[2] === 0xbf) {
    failures.push(`UTF-8 BOM is not allowed: ${path}`);
  }
  if (text.includes("\uFFFD")) failures.push(`Unicode replacement character: ${path}`);
  if (text.includes("\u0000")) failures.push(`NUL byte in text file: ${path}`);
  if (/(C:\\Users\\|\/Users\/[^/]+\/|\/home\/[^/]+\/)/i.test(text)) {
    failures.push(`local absolute path: ${path}`);
  }
  if (/-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----/.test(text)) {
    failures.push(`possible private key: ${path}`);
  }
}

for (const absolute of files.filter((path) => extname(path).toLowerCase() === ".thy")) {
  const path = relative(root, absolute).replaceAll("\\", "/");
  const text = readFileSync(absolute, "utf8");
  if (/^\s*(?:sorry|oops)\b/m.test(text)) failures.push(`unfinished Isabelle command: ${path}`);
}

const rootSession = readFileSync(resolve(root, "Cross_Domain_State_Preservation/ROOT"), "utf8");
const racSession = readFileSync(resolve(root, "Regulatory_Action_Composition/ROOT"), "utf8");
const cdspTheories = [
  "State_Preservation",
  "Regulatory_Instance",
  "Priority_Resolution",
  "DQuencer_Instance",
  "Composition",
  "Proof_Automation",
  "Functor_Laws",
  "Hierarchy",
  "External_Instance",
  "Canton_Bridge",
];
for (const theory of cdspTheories) {
  if (!rootSession.includes(theory)) failures.push(`ROOT missing theory: ${theory}`);
  try {
    statSync(resolve(root, "Cross_Domain_State_Preservation", `${theory}.thy`));
  } catch {
    failures.push(`missing theory source: ${theory}.thy`);
  }
}
if (!racSession.includes("session Regulatory_Action_Composition = Cross_Domain_State_Preservation +")) {
  failures.push("RAC ROOT must extend Cross_Domain_State_Preservation");
}
if (!racSession.includes("Regulatory_Action_Composition")) {
  failures.push("RAC ROOT missing Regulatory_Action_Composition theory");
}
const repositoryRoots = readFileSync(resolve(root, "ROOTS"), "utf8");
for (const sessionRoot of [
  "Cross_Domain_State_Preservation",
  "Regulatory_Action_Composition",
]) {
  if (!repositoryRoots.split(/\r?\n/).includes(sessionRoot)) {
    failures.push(`ROOTS missing session directory: ${sessionRoot}`);
  }
}

function anchorsFor(path) {
  const counts = new Map();
  const anchors = new Set();
  for (const line of readFileSync(path, "utf8").split(/\r?\n/)) {
    const match = /^(#{1,6})\s+(.+?)\s*$/.exec(line);
    if (!match) continue;
    const base = match[2]
      .replace(/<[^>]*>/g, "")
      .replace(/[`*_~]/g, "")
      .toLowerCase()
      .replace(/[^\p{L}\p{N}\s-]/gu, "")
      .trim()
      .replace(/\s+/g, "-");
    const duplicate = counts.get(base) ?? 0;
    counts.set(base, duplicate + 1);
    anchors.add(duplicate === 0 ? base : `${base}-${duplicate}`);
  }
  return anchors;
}

const markdown = files.filter((path) => extname(path).toLowerCase() === ".md");
const anchorCache = new Map();
for (const source of markdown) {
  const text = readFileSync(source, "utf8").replace(/```[\s\S]*?```/g, "");
  for (const match of text.matchAll(/!?\[[^\]]*]\(([^)\s]+)(?:\s+"[^"]*")?\)/g)) {
    const rawTarget = match[1];
    if (/^(https?:|mailto:)/i.test(rawTarget)) continue;
    const [rawPath, rawFragment = ""] = rawTarget.split("#", 2);
    const target = rawPath ? resolve(dirname(source), decodeURIComponent(rawPath)) : source;
    const label = `${relative(root, source).replaceAll("\\", "/")} -> ${rawTarget}`;
    try {
      if (!statSync(target).isFile()) failures.push(`link target is not a file: ${label}`);
    } catch {
      failures.push(`missing link target: ${label}`);
      continue;
    }
    if (rawFragment && extname(target).toLowerCase() === ".md") {
      const anchors = anchorCache.get(target) ?? anchorsFor(target);
      anchorCache.set(target, anchors);
      if (!anchors.has(decodeURIComponent(rawFragment).toLowerCase())) {
        failures.push(`missing heading anchor: ${label}`);
      }
    }
  }
}

const readme = readFileSync(resolve(root, "README.md"), "utf8");
for (const marker of [
  "## Verified model-level results",
  "## Theory architecture",
  "## Assurance boundary",
  "## Reproduce the proofs",
  "## Independent review and contributions",
  "## License and disclaimer",
]) {
  if (!readme.includes(marker)) failures.push(`README missing required marker: ${marker}`);
}

const workflow = readFileSync(resolve(root, ".github/workflows/repository-health.yml"), "utf8");
if (!/^permissions:\s*$/m.test(workflow)) failures.push("workflow missing top-level permissions");
if (!/timeout-minutes:\s*\d+/m.test(workflow)) failures.push("workflow missing job timeout");
for (const match of workflow.matchAll(/^\s*uses:\s*([^#\s]+)(?:\s+#.*)?$/gm)) {
  if (!/@[0-9a-f]{40}$/i.test(match[1])) {
    failures.push(`GitHub Action is not pinned to a full commit: ${match[1]}`);
  }
}

if (failures.length) {
  for (const failure of failures) console.error(failure);
  process.exit(1);
}

console.log(`repository health PASS: ${files.length} files, ${cdspTheories.length + 1} theories, 2 sessions`);

// SPDX-License-Identifier: BSD-3-Clause
import { appendFileSync, readFileSync, readdirSync, statSync } from "node:fs";
import { basename, dirname, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const PROTECTED_SESSION = "Protected_Behavior_Obstructions";
const AUDIT_SESSION = "Composition_Proof_Audit";

function posix(path) {
  return path.replaceAll("\\", "/").replace(/^\.\//, "").replace(/^\/+|\/+$/g, "");
}

function walk(directory, wantedName, files = []) {
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    if ([".git", "node_modules", "output", "release"].includes(entry.name)) continue;
    const path = resolve(directory, entry.name);
    if (entry.isDirectory()) walk(path, wantedName, files);
    else if (entry.isFile() && entry.name === wantedName) files.push(path);
  }
  return files;
}

function parseSessionRoot(rootPath, repositoryRoot) {
  const text = readFileSync(rootPath, "utf8");
  const match = /\bsession\s+"?([A-Za-z0-9_-]+)"?\s*=\s*"?([A-Za-z0-9_-]+)"?\s*\+/.exec(text);
  if (!match) throw new Error(`Cannot parse Isabelle session declaration: ${relative(repositoryRoot, rootPath)}`);
  return {
    name: match[1],
    parent: match[2],
    directory: posix(relative(repositoryRoot, dirname(rootPath))),
    rootPath,
    text,
  };
}

function declaredTheories(session) {
  const names = new Set();
  const block = /(?:^|\n)\s*theories(?:\s*\[[^\]]*\])?\s*\n([\s\S]*?)(?=\n\s*(?:chapter|session|sessions|options|theories|document_files|directories)\b|$)/g;
  for (const match of session.text.matchAll(block)) {
    const withoutComments = match[1].replace(/\(\*[\s\S]*?\*\)/g, " ");
    for (const token of withoutComments.match(/"[^"]+"|[A-Za-z0-9_./-]+/g) ?? []) {
      names.add(token.replaceAll('"', ""));
    }
  }
  return names;
}

export function readSessionGraph(repositoryRoot) {
  const root = resolve(repositoryRoot);
  const registeredDirectories = readFileSync(resolve(root, "ROOTS"), "utf8")
    .split(/\r?\n/)
    .flatMap((line) => line.replace(/#.*/, "").trim().split(/\s+/))
    .map(posix)
    .filter(Boolean);
  const sessions = walk(root, "ROOT").map((path) => parseSessionRoot(path, root));
  const byName = new Map(sessions.map((session) => [session.name, session]));
  if (byName.size !== sessions.length) throw new Error("Duplicate Isabelle session name");

  const registeredNames = [];
  for (const directory of registeredDirectories) {
    const candidates = sessions.filter((session) => session.directory === directory);
    if (candidates.length !== 1) throw new Error(`ROOTS entry must identify one session: ${directory}`);
    registeredNames.push(candidates[0].name);
  }
  for (const session of sessions) {
    if (!registeredNames.includes(session.name) && session.name !== AUDIT_SESSION) {
      throw new Error(`Unregistered non-audit Isabelle session: ${session.name}`);
    }
  }

  const children = new Map(sessions.map((session) => [session.name, []]));
  for (const session of sessions) {
    if (children.has(session.parent)) children.get(session.parent).push(session.name);
  }

  const order = [];
  const visited = new Set();
  function visit(name) {
    if (visited.has(name)) return;
    const session = byName.get(name);
    if (session && byName.has(session.parent)) visit(session.parent);
    visited.add(name);
    order.push(name);
  }
  for (const name of registeredNames) visit(name);
  for (const session of sessions) visit(session.name);

  return { root, sessions, byName, children, registeredNames, order };
}

function ownerForPath(graph, path) {
  const candidates = graph.sessions
    .filter((session) => path === session.directory || path.startsWith(`${session.directory}/`))
    .sort((left, right) => right.directory.length - left.directory.length);
  return candidates[0];
}

export function assertProofCoverage(repositoryRoot) {
  const graph = readSessionGraph(repositoryRoot);
  function gather(directory, files = []) {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      if ([".git", "node_modules", "output", "release"].includes(entry.name)) continue;
      const path = resolve(directory, entry.name);
      if (entry.isDirectory()) gather(path, files);
      else if (entry.isFile() && entry.name.endsWith(".thy")) files.push(path);
    }
    return files;
  }

  const actualBySession = new Map(graph.sessions.map((session) => [session.name, new Set()]));
  for (const absolute of gather(graph.root)) {
    const path = posix(relative(graph.root, absolute));
    const owner = ownerForPath(graph, path);
    if (!owner) throw new Error(`Theory is outside every declared session: ${path}`);
    actualBySession.get(owner.name).add(posix(relative(resolve(graph.root, owner.directory), absolute)).replace(/\.thy$/, ""));
  }

  for (const session of graph.sessions) {
    const declared = declaredTheories(session);
    const actual = actualBySession.get(session.name);
    for (const theory of actual) {
      if (!declared.has(theory)) throw new Error(`${session.name} does not register theory ${theory}`);
    }
    for (const theory of declared) {
      const path = resolve(graph.root, session.directory, `${theory}.thy`);
      if (!statSync(path, { throwIfNoEntry: false })?.isFile()) {
        throw new Error(`${session.name} registers missing theory ${theory}`);
      }
    }
  }
  return graph;
}

function isGlobalProofControl(path) {
  return path === "ROOTS" ||
    /^\.github\/workflows\/[^/]+\.ya?ml$/.test(path) ||
    /^scripts\/select-proof-sessions(?:\.test)?\.mjs$/.test(path);
}

function affectsSessionBuild(path, session) {
  if (path === `${session.directory}/ROOT`) return true;
  if (!path.startsWith(`${session.directory}/`)) return false;
  return /\.(?:thy|ML)$/.test(path) || path.startsWith(`${session.directory}/document/`);
}

export function selectProofSessions(repositoryRoot, changedPaths, { forceAll = false } = {}) {
  const graph = assertProofCoverage(repositoryRoot);
  const changed = [...new Set(changedPaths.map(posix).filter(Boolean))];
  const affected = new Set();
  const global = forceAll || changed.some(isGlobalProofControl);

  for (const path of changed) {
    if (isGlobalProofControl(path)) {
      continue;
    }

    const owner = ownerForPath(graph, path);
    if (owner && affectsSessionBuild(path, owner)) affected.add(owner.name);

    if ((path === "Evidence_Binding_Composition/claims.json" ||
         path === "Evidence_Binding_Composition/verify-proof-output.mjs") &&
        graph.byName.has(AUDIT_SESSION)) {
      affected.add(AUDIT_SESSION);
    }

    if ((/\.(?:thy|ML)$/.test(path) || basename(path) === "ROOT") && !owner && !global) {
      throw new Error(`Proof input is outside every declared session: ${path}`);
    }
  }

  if (global) for (const session of graph.sessions) affected.add(session.name);

  const queue = [...affected];
  for (let index = 0; index < queue.length; index += 1) {
    for (const child of graph.children.get(queue[index]) ?? []) {
      if (!affected.has(child)) {
        affected.add(child);
        queue.push(child);
      }
    }
  }

  const productSessions = graph.order.filter((name) =>
    affected.has(name) && name !== PROTECTED_SESSION && name !== AUDIT_SESSION && graph.registeredNames.includes(name));

  return {
    forceAll: global,
    changedCount: changed.length,
    protected: affected.has(PROTECTED_SESSION),
    productSessions,
    audit: affected.has(AUDIT_SESSION),
  };
}

function runCli() {
  const forceAll = process.argv.includes("--all");
  const nullDelimited = process.argv.includes("--null");
  const input = forceAll ? "" : readFileSync(0, "utf8");
  const changedPaths = input ? input.split(nullDelimited ? "\0" : /\r?\n/) : [];
  const selection = selectProofSessions(process.cwd(), changedPaths, { forceAll });
  process.stdout.write(`${JSON.stringify(selection, null, 2)}\n`);

  if (process.env.GITHUB_OUTPUT) {
    appendFileSync(process.env.GITHUB_OUTPUT,
      `protected=${selection.protected}\n` +
      `product_sessions=${selection.productSessions.join(" ")}\n` +
      `audit=${selection.audit}\n` +
      `force_all=${selection.forceAll}\n` +
      `changed_count=${selection.changedCount}\n`);
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) runCli();

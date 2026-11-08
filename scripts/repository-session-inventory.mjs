// SPDX-License-Identifier: BSD-3-Clause
import { assertProofCoverage, selectProofSessions } from "./select-proof-sessions.mjs";

// One shared interpretation of ROOT/in-directory ownership and exact external
// ML data exceptions. No second ROOT parser or whole-directory exclusion.
export function repositorySessionInventory(repositoryRoot, repositoryPaths) {
  const graph = assertProofCoverage(repositoryRoot);
  const paths = repositoryPaths.map((path) => path.replaceAll("\\", "/"));
  const proofInputs = paths.filter((path) => /\.(?:thy|ML)$/.test(path) || /(?:^|\/)ROOT$/.test(path));
  // Reuse the selector's unknown-input check and its exact four artifact paths.
  selectProofSessions(repositoryRoot, proofInputs);
  const sessionEdges = new Set();
  for (const name of graph.registeredNames) {
    const session = graph.byName.get(name);
    if (!session) throw new Error(`Missing registered session metadata: ${name}`);
    for (const dependency of session.dependencies) sessionEdges.add(`${dependency}|${name}`);
  }
  return {
    graph,
    sessionEdges,
    registeredSessionCount: graph.registeredNames.length,
    auxiliarySessionCount: graph.sessions.length - graph.registeredNames.length,
    theoryFileCount: paths.filter((path) => path.endsWith(".thy")).length,
  };
}

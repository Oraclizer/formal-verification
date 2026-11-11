// SPDX-License-Identifier: BSD-3-Clause
import { readFileSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { assertProofCoverage, selectProofSessions } from "./select-proof-sessions.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const assets = join(root, "docs/assets");
const graph = assertProofCoverage(root);
const { productSessions } = selectProofSessions(root, [], { forceAll: true });
const edges = graph.registeredNames.flatMap((name) =>
  graph.byName.get(name).dependencies.map((dependency) => [dependency, name]));
const marker = "<!-- Generated extension dependency catalog -->";
const escape = (value) => value.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll('"', "&quot;");

// Classify declared session directories, rather than guessing from session names.
const groups = [
  {
    title: "Wire and authentication",
    detail: ["Negotiation, canonical wire data", "and threshold signatures"],
    areas: ["Wire", "Product/ReferenceSecurity"],
  },
  {
    title: "State sync and reads",
    detail: ["Commitment sync, queries, cached", "and historical reads"],
    areas: ["Product/SyncCommitment", "Product/CurrentRead", "Product/QueryCache", "Product/QueryCapture",
      "Product/SecondaryRead", "Product/HistoricalRead"],
  },
  {
    title: "Responses and receipts",
    detail: ["Response codes, signed replies", "and stored outcomes"],
    areas: ["Base/ResponseExtension", "Product/ResponseEgress", "Product/ResponseSigner", "Product/Response",
      "Product/StoredReceipt", "Product/CompletionGates"],
  },
  {
    title: "Authority and asset effects",
    detail: ["Handover, legal controls, locks", "and reference writes"],
    areas: ["Base/Checks/OrderedMaintenanceCore", "Product/OrderedMaintenanceEntry", "Product/OrderedMaintenance",
      "Product/Write", "Product/PendingLock", "Product/ReserveDebitReplay", "Product/OrderedDebit", "Product/LegalFresh",
      "Product/LegalReceipt", "Product/ProtectedSpend", "Product/Handover"],
  },
  {
    title: "Ordering and settlement",
    detail: ["Scheduling, primary decisions", "and settlement queues"],
    areas: ["Product/Schedule", "Product/SignedSchedule", "Product/PrimaryOrigin", "Product/TerminalRecord",
      "Product/SettlementQueue", "Product/Settlement"],
  },
  {
    title: "Persistence and recovery",
    detail: ["Source journals, witness checks,", "publication and reopening"],
    areas: ["Storage", "Product/RecordReopening", "Product/SourceWriter", "Product/SourceCertificate",
      "Product/DirectPublication", "Product/IndependentPublication", "Product/Publish"],
  },
];

function groupCounts(names) {
  const result = groups.map((group) => ({ ...group, count: 0 }));
  for (const name of names) {
    const { directory } = graph.byName.get(name);
    const area = directory.match(/^Oracle_Interoperability_Protocol\/Extensions\/V\d+\/(.+)$/)?.[1];
    const matches = result.filter((group) => group.areas.some((entry) => area === entry || area?.startsWith(`${entry}/`)));
    if (matches.length !== 1) throw new Error(`Expected one overview group for ${name} (${directory})`);
    matches[0].count++;
  }
  return result.filter(({ count }) => count > 0);
}

function text(x, y, value, size, color = "#e1eaf8") {
  return `<text x="${x}" y="${y}" font-size="${size}" fill="${color}">${escape(value)}</text>`;
}

function render(path, columns) {
  const source = readFileSync(path, "utf8").replaceAll("\r\n", "\n").split(marker)[0]
    .replace(/<\/svg>\s*$/, "").trimEnd();
  const base = new Set([...source.matchAll(/data-node="([^"]+)"/g)].map((match) => match[1]));
  const baseEdges = [...source.matchAll(/data-from="([^"]+)" data-to="([^"]+)"/g)]
    .map((match) => `${match[1]}|${match[2]}`).sort();
  const expectedBase = edges.filter(([from, to]) => base.has(from) && base.has(to))
    .map(([from, to]) => `${from}|${to}`).sort();
  if (JSON.stringify(baseEdges) !== JSON.stringify(expectedBase)) {
    throw new Error("The drawn base graph differs from the registered session dependencies");
  }
  const dimensions = /<rect width="(\d+)" height="(\d+)" rx="20" fill="#0b142a"\/>/.exec(source);
  if (!dimensions) throw new Error("Missing base diagram canvas");
  const [width, baseHeight] = dimensions.slice(1).map(Number);
  const remaining = productSessions.filter((name) => !base.has(name));
  const summary = groupCounts(remaining);
  // Retain exact edges for repository validation without drawing a card per session.
  const metadata = edges.filter(([from, to]) => !base.has(from) || !base.has(to)).map(([from, to]) =>
    `  <dependency data-from="${escape(from)}" data-to="${escape(to)}"/>`);
  const description = `${graph.registeredNames.length} registered sessions. The upper diagram shows the base dependencies. ` +
    `The ${remaining.length} additional OIP sessions are grouped by purpose below. ` +
    "The arrows above indicate direct Isabelle source dependencies. The full graph and ROOT files are linked in the README.";
  const panelWidth = (width - 56 - 16 * (columns - 1)) / columns;
  const drawing = ['<g font-family="Arial,Segoe UI,sans-serif" aria-label="OIP extensions by purpose">',
    text(28, baseHeight + 44, "OIP extension groups", 27),
    text(28, baseHeight + 74, `${remaining.length} sessions by purpose · full graph linked below`, 17, "#a8bbd5")];
  let y = baseHeight + 100;
  const rowHeight = 90;
  for (let start = 0; start < summary.length; start += columns) {
    const row = summary.slice(start, start + columns);
    for (const [column, { title, detail, count }] of row.entries()) {
      const x = 28 + column * (panelWidth + 16);
      drawing.push(`<g aria-label="${escape(`${title}: ${count} sessions`)}">`,
        `<rect x="${x}" y="${y}" width="${panelWidth}" height="${rowHeight}" rx="10" fill="#11233c" stroke="#527aa1"/>`,
        text(x + 16, y + 29, title, 22),
        `<rect x="${x + panelWidth - 116}" y="${y + 12}" width="100" height="26" rx="13" fill="#233e5e"/>`,
        text(x + panelWidth - 106, y + 30, `${count} sessions`, 16, "#cfdef4"),
        ...detail.map((line, index) => text(x + 16, y + 55 + 21 * index, line, 17, "#a8bbd5")),
        "</g>");
    }
    y += rowHeight + 12;
  }
  const height = y + 16;
  const opening = source.replace(/height="\d+" viewBox="0 0 \d+ \d+"/, `height="${height}" viewBox="0 0 ${width} ${height}"`)
    .replace(/<desc id="desc">[^<]*<\/desc>/, `<desc id="desc">${escape(description)}</desc>`)
    .replace("Sixteen registered sessions · dependency → child", "Base sessions · dependency → child");
  const panel = `<rect x="0" y="${baseHeight - 8}" width="${width}" height="${height - baseHeight + 8}" rx="16" fill="#0b142a"/>`;
  writeFileSync(path, [opening, marker, '<metadata id="oip-extension-dependencies">', ...metadata, "</metadata>",
    panel, ...drawing, "</g></svg>", ""].join("\n"));
}

render(join(assets, "session-architecture.svg"), 2);
render(join(assets, "session-architecture-mobile.svg"), 1);

const aliases = (name) => name.replaceAll("-", "_");
const names = [...new Set(edges.flat())].sort();
writeFileSync(join(assets, "session-architecture.mmd"), [
  "%% Generated from the registered session graph. Arrows run from dependency to importer.",
  "flowchart TB",
  ...names.map((name) => `    ${aliases(name)}["${name}"]`),
  ...edges.map(([from, to]) => `    ${aliases(from)} --> ${aliases(to)}`),
  "",
].join("\n"));
console.log(`Rendered ${graph.registeredNames.length} registered sessions and ${edges.length} dependency edges.`);

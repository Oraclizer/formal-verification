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
  const description = `${graph.registeredNames.length} registered sessions. The upper diagram shows the base dependencies. ` +
    "The catalog below lists each additional OIP session with its direct dependencies. The arrows indicate Isabelle source dependencies.";
  const panelWidth = (width - 56 - 16 * (columns - 1)) / columns;
  const drawing = ['<g font-family="Arial,Segoe UI,sans-serif">',
    text(28, baseHeight + 44, "Additional OIP sessions", 27),
    text(28, baseHeight + 74, "Each card names the session and its direct dependencies.", 17, "#a8bbd5")];
  let y = baseHeight + 100;
  for (let start = 0; start < remaining.length; start += columns) {
    const row = remaining.slice(start, start + columns);
    const rowHeight = 52 + 24 * Math.max(...row.map((name) => graph.byName.get(name).dependencies.length));
    for (const [column, name] of row.entries()) {
      const x = 28 + column * (panelWidth + 16);
      drawing.push(`<g data-node="${escape(name)}">`,
        `<rect x="${x}" y="${y}" width="${panelWidth}" height="${rowHeight}" rx="10" fill="#11233c" stroke="#527aa1"/>`,
        text(x + 14, y + 29, name, 17));
      for (const [index, dependency] of graph.byName.get(name).dependencies.entries()) {
        drawing.push(`<g data-from="${escape(dependency)}" data-to="${escape(name)}">` +
          text(x + 14, y + 54 + 24 * index, `← ${dependency}`, 15, "#a8bbd5") + "</g>");
      }
      drawing.push("</g>");
    }
    y += rowHeight + 12;
  }
  const height = y + 16;
  const opening = source.replace(/height="\d+" viewBox="0 0 \d+ \d+"/, `height="${height}" viewBox="0 0 ${width} ${height}"`)
    .replace(/<desc id="desc">[^<]*<\/desc>/, `<desc id="desc">${escape(description)}</desc>`)
    .replace("Sixteen registered sessions · dependency → child", "Base sessions · dependency → child");
  const panel = `<rect x="0" y="${baseHeight - 8}" width="${width}" height="${height - baseHeight + 8}" rx="16" fill="#0b142a"/>`;
  writeFileSync(path, [opening, marker, panel, ...drawing, "</g></svg>", ""].join("\n"));
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

// SPDX-License-Identifier: BSD-3-Clause
import { copyFileSync, mkdirSync, renameSync, readFileSync } from "node:fs";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";

const root = dirname(fileURLToPath(import.meta.url));
if (process.argv.length !== 3) throw Error("Usage: node build-document.mjs OUTPUT_DIRECTORY");
const output = resolve(process.argv[2]);
if (output === resolve(root, "document")) throw Error("Choose a separate document output directory");
mkdirSync(output, { recursive: true });
for (const file of ["root.tex", "root.bib"]) {
  copyFileSync(resolve(root, "document", file), resolve(output, file));
}
const latex = ["-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "root.tex"];
for (const [command, args] of [["pdflatex", latex], ["bibtex", ["root"]], ["pdflatex", latex], ["pdflatex", latex]]) {
  const run = spawnSync(command, args, { cwd: output, encoding: "utf8" });
  if (run.error || run.status !== 0) {
    process.stderr.write(run.stdout ?? "");
    process.stderr.write(run.stderr ?? "");
    throw run.error ?? Error(`${command} failed with exit ${run.status}`);
  }
}
const log = readFileSync(resolve(output, "root.log"), "utf8");
if (/Overfull \\[hv]box|undefined references|Citation .+ undefined/.test(log)) {
  throw Error("Review document layout or unresolved references in root.log");
}
const pdf = resolve(output, "Evidence_Binding_Composition.pdf");
renameSync(resolve(output, "root.pdf"), pdf);
console.log(`Technical document built: ${pdf}`);

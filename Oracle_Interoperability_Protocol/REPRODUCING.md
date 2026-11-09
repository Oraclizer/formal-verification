# Reproducing the OIP prototype interfaces

Run the session commands from the formal-verification repository root. Run the
wire consumers from the exact OIP source checkout identified by its source
fingerprint and artifact locks. Source identity, logical-session extraction,
ABI loading and sampled value comparisons have separate purposes.

## Compiler-input identity

`source-manifest.json` contains ROOT plus 398 theory records with relative path,
byte count and SHA256. The raw manifest SHA256 is
`05c18602e03737f7d94503f6a7e0d732fa8f0b840538884abb33086b32771563`.
The canonical inventory identity is
`fa28a301c30c77618acc4726f26a5a6d0c396bf5f6b10d8f073d72cf92c6b079`:
SHA256 of ASCII JSON with sorted keys, compact separators and no final newline.
ROOT separately hashes to
`f79ab1c2d2ea32f4e70a2c21df3e1dd92eabdc06b5af663d6679dec90d02563d`.
These are source identities, not assertions of a build or comparison result.

The following reads the actual bytes and displays the two compiler-input
digests without changing the source:

```bash
python3 - <<'PY'
from pathlib import Path
import hashlib, json, stat
root = Path('Oracle_Interoperability_Protocol')
raw = (root / 'source-manifest.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '05c18602e03737f7d94503f6a7e0d732fa8f0b840538884abb33086b32771563'
manifest = json.loads(raw)
assert manifest['format'] == 'oip-public-formal-source-inventory-v1'
assert manifest['namespace'] == 'Oracle_Interoperability_Protocol'
rows = manifest['files']
expected = {'ROOT', *(p.relative_to(root).as_posix() for p in root.rglob('*.thy'))}
assert len(rows) == 399 and {row['path'] for row in rows} == expected
for row in rows:
    relative = Path(row['path'])
    assert not relative.is_absolute() and '..' not in relative.parts
    path = root / relative
    info = path.lstat()
    assert stat.S_ISREG(info.st_mode) and not path.is_symlink() and info.st_nlink == 1
    data = path.read_bytes()
    assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
canonical = json.dumps(manifest, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode('ascii')
formal = hashlib.sha256(canonical).hexdigest()
root_sha = hashlib.sha256((root / 'ROOT').read_bytes()).hexdigest()
assert formal == 'fa28a301c30c77618acc4726f26a5a6d0c396bf5f6b10d8f073d72cf92c6b079'
assert root_sha == 'f79ab1c2d2ea32f4e70a2c21df3e1dd92eabdc06b5af663d6679dec90d02563d'
print('formal_root_sha256=' + formal)
print('ROOT_sha256=' + root_sha)
PY
```

## Pinned Isabelle and AFP dependency

Use Isabelle2025-2 and the dated AFP `ADS_Functor` entry pinned by
[Proofs](../.github/workflows/proofs.yml). The workflow specifies the archive
URLs and verifies their bytes:

| Archive | SHA256 |
| --- | --- |
| `Isabelle2025-2_linux.tar.gz` | `a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c` |
| `afp-ADS_Functor-2026-02-06.tar.gz` | `10d6fa8671c461022ae5e71859a07610d616681fed79e2f1c81029a124203c85` |

Set `ISABELLE` to that distribution's `bin/isabelle` and `AFP_ENTRY` to the
extracted `ADS_Functor` directory containing ROOT. This uses the same existing
dependency instructions as the repository proof lane.

```bash
"$ISABELLE" version
"$ISABELLE" build -b -j 1 -o threads=1 -o parallel_proofs=0 \
  -o document=false -o quick_and_dirty=false -o skip_proofs=false -o timeout_build=false \
  -d "$AFP_ENTRY" -d . \
  OIP_Record_Reopening OIP_Recovery_Boundary OIP_Sync_V061_Typed_Artifact OIP_Response_Egress_V061_Export
```

The four targets build the two recovery boundaries, the two export sessions
and their dependencies from ROOT. `build -n` prints the build plan. The
repository Proofs workflow selects the affected sessions and their downstream
consumers and checks each selected result.

## Exact logical-session exports

Use a fresh `OUT` directory and keep this shell variable when changing to the
OIP checkout. First list each checked session's exports without building.
Confirm the exact owner and name in the list before extracting one entry.
Do not use wildcard extraction or edit generated ML.

```bash
OUT="$(mktemp -d)"
"$ISABELLE" export -n -l -d "$AFP_ENTRY" -d . OIP_Sync_V061_Typed_Artifact > "$OUT/typed-exports.txt"
grep -Fx 'OIP_Sync_V061_Typed_Artifact.Sync_V061_Typed_Identity:code/oip_wire_values_v061_current.ML' "$OUT/typed-exports.txt"
"$ISABELLE" export -n -d "$AFP_ENTRY" -d . -O "$OUT/typed" -p 1 \
  -x 'OIP_Sync_V061_Typed_Artifact.Sync_V061_Typed_Identity:code/oip_wire_values_v061_current.ML' OIP_Sync_V061_Typed_Artifact

"$ISABELLE" export -n -l -d "$AFP_ENTRY" -d . OIP_Response_Egress_V061_Export > "$OUT/full-exports.txt"
grep -Fx 'OIP_Response_Egress_V061_Export.Response_Egress_V061_Export:code/oip_wire_response_full_v061.ML' "$OUT/full-exports.txt"
"$ISABELLE" export -n -d "$AFP_ENTRY" -d . -O "$OUT/full" -p 1 \
  -x 'OIP_Response_Egress_V061_Export.Response_Egress_V061_Export:code/oip_wire_response_full_v061.ML' OIP_Response_Egress_V061_Export
```

The extracted files are `typed/code/oip_wire_values_v061_current.ML` and
`full/code/oip_wire_response_full_v061.ML` beneath `OUT`. Record their actual
bytes/hashes and the session database identity independently. The external
runtime artifact names may differ; a packaging copy must preserve model bytes.

## External ABI and six-field identities

Use genuine Ubuntu 24.04/amd64 and the OIP repository's
[locked Poly/ML 5.7.1-5build1 packages](https://github.com/Oraclizer/oip-spec/blob/main/tools/polyml-noble-amd64.lock.json).
From the exact OIP source checkout, the
[userspace recipe](https://github.com/Oraclizer/oip-spec/blob/main/scripts/prepare-polyml-userspace.py)
extracts those byte-pinned packages into a fresh local target directory:

```bash
python3 scripts/prepare-polyml-userspace.py
POLYML="$PWD/target/polyml-userspace/bin/poly"
```

Run the unchanged production drivers from that same checkout:

| Driver | SHA256 |
| --- | --- |
| `tests/wire-values-driver.ML` | `c9ed19c6c27c6eed5aa0bc07b0e2c899fb83fa92e7f5f861dc1da64ab6b356bc` |
| `tests/response-full-driver.ML` | `c9d865ba0257bed26f24b8d9cfca64add77dc03ab4357fdea1943c11f61a0703` |

```bash
printf '' | env OIP_WIRE_MODEL="$OUT/typed/code/oip_wire_values_v061_current.ML" \
  "$POLYML" -q --error-exit --script tests/wire-values-driver.ML
printf '' | env OIP_WIRE_RESPONSE_MODEL="$OUT/full/code/oip_wire_response_full_v061.ML" \
  "$POLYML" -q --error-exit --script tests/response-full-driver.ML
```

`OIP_Wire_Oracle_V061.sync_v061_typed_model_identity ()` and
`OIP_Wire_Response_Boundary.code_response_full_model_identity ()` each return
six ASCII fields. The last field must match the `runtime_source_hash` in the
corresponding [artifact lock](artifacts/locks/).

| Field | Typed transport | Full sender/client |
| --- | --- | --- |
| Schema | `1` | `1` |
| ABI | `intinf-wire-values-v2` | `intinf-response-full-v2` |
| Scope | `wire-v6-general-33-values` | `wire-response-sender-client-v2` |
| Entrypoint | `OIP_Wire_Oracle_V061.sync_v061_nested_transport_flat` | `OIP_Wire_Response_Boundary.code_response_egress_flat_oracle` |
| Natural refinement | `HOL-Library.Code_Target_Nat` | `HOL-Library.Code_Target_Nat` |
| Runtime source fingerprint | `model-artifact.lock.json` | `wire-response-artifact.lock.json` |

A private namespace export, four-field interface, caller-supplied fingerprint
or edited model is not interchangeable with these interfaces. ABI loading
checks the interface and returned identity; it does not perform value cases.

## Standard bounded consumers

The OIP source checkout uses Rust 1.96.1, Go 1.25.5 and the same locked Poly/ML.
Its default typed consumer compares 692 rows across Rust, Go and the pinned
model, including all seven typed observation fields:

```bash
export RUSTUP_TOOLCHAIN=1.96.1
cargo fetch --locked
GO="${GO:-go}"
test "$("$GO" env GOVERSION)" = go1.25.5
(cd go && "$GO" mod download google.golang.org/protobuf@v1.36.8)
python3 scripts/check-operations.py --require-mirror --polyml "$POLYML"
python3 scripts/test-wire-interop.py
```

The Full consumer compares original operations, lower response boundary inputs
and current clients through the model-issued primitive protocol:

```bash
RUN="$(mktemp -d)"
python3 scripts/run-response-boundary-source.py --output "$RUN/response-boundary"
python3 scripts/run-wire-full-source.py --output "$RUN/wire-full-source"
python3 scripts/check-response-boundary.py \
  --source-output "$RUN/response-boundary" --operations-output "$RUN/wire-full-source" \
  --output "$RUN/full-comparison" --polyml "$POLYML"
```

Use fresh output directories. The default loaders download content-pinned
model, driver, origin and exact diagnostic bytes. For offline local reception the
same loaders accept `--model-artifact-root` for typed transport and
`--artifact-root` for Full; these paths do not change model identity or relax
the required comparison. Each local bundle must contain the same four named
roles and match every content pin, origin and namespace check. Raw output and
exact compiler diagnostics remain separate; an unknown diagnostic or missing
primitive response is not success.

The consumer compares 33 original-operation, 207 boundary and 21 current-client
inputs. Its model-side combined entry consumes the model's sender packet.
These are bounded comparisons, not a theorem covering every compiled Rust/Go
input or a running production Witness/storage deployment.

## Public code linkage

Once the actual signed OIP root has been observed through the public API, a
separate downstream consumer link can record that exact CodeCommit and tree.
It is not a premise of generating model bytes. CodeCommit is never embedded
in the model's source fingerprint, six-field identity, export, origin or lock.
This keeps formal extraction, artifact publication and code linkage acyclic.

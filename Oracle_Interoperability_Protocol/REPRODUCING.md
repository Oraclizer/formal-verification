# Reproducing the OIP prototype interfaces

Run the session commands from the formal-verification repository root. Run the
wire consumers from the exact OIP source checkout identified by its source
fingerprint and artifact locks. Source identity, logical-session extraction,
ABI loading and sampled value comparisons have separate purposes.

## Compiler-input identity

`source-manifest.json` contains ROOT plus 344 theory records with relative path,
byte count and SHA256. The raw manifest SHA256 is
`b73e4c823aa766a13895a9582990da4b227ebd493c33444d44dac1a27b8215fa`.
The canonical inventory identity is
`7219abb349d4d0565ab933d2afb49ba831e05254e11a41d506b72fad914cae01`:
SHA256 of ASCII JSON with sorted keys, compact separators and no final newline.
ROOT separately hashes to
`3c2faa94af7f0c0172009e243da280707b048da81cb15d4ac466ea15d511965e`.
These are source identities, not assertions of a build or comparison result.

The following reads the actual bytes and displays the two compiler-input
digests without changing the source:

```bash
python3 - <<'PY'
from pathlib import Path
import hashlib, json, stat
root = Path('Oracle_Interoperability_Protocol')
raw = (root / 'source-manifest.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'b73e4c823aa766a13895a9582990da4b227ebd493c33444d44dac1a27b8215fa'
manifest = json.loads(raw)
assert manifest['format'] == 'oip-public-formal-source-inventory-v1'
assert manifest['namespace'] == 'Oracle_Interoperability_Protocol'
rows = manifest['files']
expected = {'ROOT', *(p.relative_to(root).as_posix() for p in root.rglob('*.thy'))}
assert len(rows) == 345 and {row['path'] for row in rows} == expected
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
assert formal == '7219abb349d4d0565ab933d2afb49ba831e05254e11a41d506b72fad914cae01'
assert root_sha == '3c2faa94af7f0c0172009e243da280707b048da81cb15d4ac466ea15d511965e'
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
  OIP_Record_Reopening OIP_Recovery_Boundary OIP_Message_Egress
```

The three named leaves include all nine namespace sessions through ROOT parent
dependencies. An optional `build -n` plan reports whether work is needed; a
planning-only result is not a completed proof build. The separate repository
Proofs workflow serializes its selected native jobs and retains selected-child
and aggregate failure checks.

## Exact logical-session exports

Use a fresh `OUT` directory and keep this shell variable when changing to the
OIP checkout. First list each checked session's exports without building.
Confirm the exact owner and name in the list before extracting one entry.
Do not use wildcard extraction or edit generated ML.

```bash
OUT="$(mktemp -d)"
"$ISABELLE" export -n -l -d "$AFP_ENTRY" -d . OIP_Message_Code > "$OUT/typed-exports.txt"
grep -Fx 'OIP_Message_Code.Wire_Code_Typed_Current_Export:code/oip_wire_values_current.ML' "$OUT/typed-exports.txt"
"$ISABELLE" export -n -d "$AFP_ENTRY" -d . -O "$OUT/typed" -p 1 \
  -x 'OIP_Message_Code.Wire_Code_Typed_Current_Export:code/oip_wire_values_current.ML' OIP_Message_Code

"$ISABELLE" export -n -l -d "$AFP_ENTRY" -d . OIP_Message_Egress > "$OUT/full-exports.txt"
grep -Fx 'OIP_Message_Egress.Wire_Code_Response_Current_Export:code/oip_wire_response_current.ML' "$OUT/full-exports.txt"
"$ISABELLE" export -n -d "$AFP_ENTRY" -d . -O "$OUT/full" -p 1 \
  -x 'OIP_Message_Egress.Wire_Code_Response_Current_Export:code/oip_wire_response_current.ML' OIP_Message_Egress
```

The extracted files are `typed/code/oip_wire_values_current.ML` and
`full/code/oip_wire_response_current.ML` beneath `OUT`. Record their actual
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
| `tests/wire-values-driver.ML` | `a1c8f5be6a637a59610010efcc489c965e82d9e0a59b72481731adf45d385bdc` |
| `tests/response-full-driver.ML` | `c9d865ba0257bed26f24b8d9cfca64add77dc03ab4357fdea1943c11f61a0703` |

```bash
printf '' | env OIP_WIRE_MODEL="$OUT/typed/code/oip_wire_values_current.ML" \
  "$POLYML" -q --error-exit --script tests/wire-values-driver.ML
printf '' | env OIP_WIRE_RESPONSE_MODEL="$OUT/full/code/oip_wire_response_current.ML" \
  "$POLYML" -q --error-exit --script tests/response-full-driver.ML
```

The typed identity is returned by `code_typed_model_identity ()`; the Full
identity by `code_response_full_model_identity ()`. Both return six ASCII
fields. For this source epoch they are:

| Field | Typed transport | Full sender/client |
| --- | --- | --- |
| Schema | `1` | `1` |
| ABI | `intinf-wire-values-v2` | `intinf-response-full-v1` |
| Scope | `wire-v6-general-31-values` | `wire-response-sender-client-v1` |
| Entrypoint | `OIP_Wire_Oracle.code_typed_transport_flat_oracle` | `OIP_Wire_Response_Boundary.code_response_egress_flat_oracle` |
| Natural refinement | `HOL-Library.Code_Target_Nat` | `HOL-Library.Code_Target_Nat` |
| Runtime source fingerprint | `28500a91beb9478d3de97ed0d9a2913bf7ea3202a5b546627e02df53b998b207` | `28500a91beb9478d3de97ed0d9a2913bf7ea3202a5b546627e02df53b998b207` |

A private namespace export, four-field interface, caller-supplied fingerprint
or edited model is not interchangeable with these interfaces. ABI loading
checks the interface and returned identity; it does not perform value cases.

## Standard bounded consumers

The OIP source checkout uses Rust 1.96.1, Go 1.25.5 and the same locked Poly/ML.
Its default typed consumer compares 673 rows across Rust, Go and the pinned
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

The consumer compares 31 original-operation, 207 boundary and 21 current-client
inputs. Its model-side combined entry consumes the model's sender packet.
These are bounded comparisons, not a theorem covering every compiled Rust/Go
input or a running production Witness/storage deployment.

## Public code linkage

Once the actual signed OIP root has been observed through the public API, a
separate downstream consumer link can record that exact CodeCommit and tree.
It is not a premise of generating model bytes. CodeCommit is never embedded
in the model's source fingerprint, six-field identity, export, origin or lock.
This keeps formal extraction, artifact publication and code linkage acyclic.

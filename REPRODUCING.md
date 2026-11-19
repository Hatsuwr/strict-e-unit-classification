# Reproduce the proof checks

## Offline source checks

From the repository root, run:

```sh
python3 -B wide/scripts/check_release.py
python3 -B strict/scripts/check_release.py
```

The first command checks the v5 source closure, hashes, and regressions. The
second checks the original strict distribution. The GitHub Actions workflow
runs these two checks; neither invokes Lean.

## Restore the pinned prerequisites

On Linux x86-64, use Python 3.12+, curl 7.84.0+, tar, and zstd. These commands
use the original installer with the v5 dependency pins. Set the prerequisite
directory outside the repository, with several gigabytes of free disk space.

```sh
PREREQS="$(pwd)/../e-value-prereqs"
python3 -B strict/scripts/setup_dependencies.py wide "$PREREQS"
LEAN="$PREREQS/lean-4.19.0-linux/bin/lean"
MATHLIB="$(pwd)/wide/project/.lake/packages/mathlib"
```

The installer fetches pinned sources and cached dependency objects. Do not
run `lake update` for reproduction. The source pins are listed in
[wide/DEPENDENCY_PINS.json](wide/DEPENDENCY_PINS.json). See the original
[strict setup notes](strict/REPRODUCING.md) for installer requirements.

## Replay v5 from source

```sh
python3 -B wide/scripts/rebuild.py --lean "$LEAN" --mathlib "$MATHLIB" \
  --source-archives "$PREREQS/downloads" --preflight
python3 -B wide/scripts/rebuild.py --lean "$LEAN" --mathlib "$MATHLIB" \
  --source-archives "$PREREQS/downloads" --output-parent "$PREREQS/v5-runs"
```

The runner uses a new output directory and never falls back to previously
compiled project files. It does use the pinned external dependency cache.
A full pass requires `FULL_REPLAY_PASS` in the run's `result.json`, all 669
local modules compiled, and exact axiom reports for the three audited
endpoints. The original strict replay remains separate. Do not combine the
two project directories in one Lean search path: some shared module names
have different source versions.

The default per-module limits are 300 seconds of CPU time (301 seconds hard
limit), 600 seconds wall time, 6 GiB sampled RSS, and 9 GiB virtual memory.
The runner uses `-t0`, `-j1`, `-DElab.async=false`, and bounded elaboration
options. Source-local limits are recorded in
[wide/SOURCE_MANIFEST.json](wide/SOURCE_MANIFEST.json).

## Recorded verification

The [verification record](wide/VERIFICATION_STATUS.json) reports
`FULL_REPLAY_PASS` for the exact 669-module source closure. All three audited
endpoints report exactly `propext`, `Classical.choice`, and `Quot.sound`:

- `StrictEUnit.v5ActualReciprocalExponential140`
- `StrictEUnit.v5_wide_reciprocal_at_one140`
- `StrictEUnit.v5_wide_unit_classification140`

The recorded run retained source-build receipts for an audited prefix of 582
unchanged modules, then compiled the revised module and all 86 later modules
from source. Both source manifests had the same module order and import
graph. Every carried source and option record was byte-identical, no carried
module depended on the changed source, and all receipt, input, export,
compiler, and external-inventory hashes were rechecked. The
[source revision ledger](wide/SOURCE_REVISIONS.json) identifies the sole
bounded elaboration-budget change. The public command above instead starts a
new output directory and compiles every project module from source.

This verification covers project sources. The compiler and cached external
dependency objects were inventoried and hash-bound, not reconstructed from
source. Dependency source pins and cached compiled artifacts are separate
inputs. No compiled project objects, raw execution logs, or external
prerequisites are bundled in this repository.

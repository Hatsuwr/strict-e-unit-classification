<!-- Modified for the source-focused edition, 12 November 2026. -->

# Reproduce the proof checks

## Offline source checks

From the extracted root, with Python 3.9+:

```sh
python3 -B scripts/check_release.py
```

Expected: `SOURCE_RELEASE_CHECK_PASS`. This command checks file/source integrity, contracts and regression tests, without invoking Lean. Individual commands are `python3 -B scripts/check_package.py`, `python3 -B scripts/check_contracts.py`, and `python3 -B -m unittest discover -s scripts -p 'test_*.py'`.

## Restore pinned prerequisites

The supported setup and bounded replay target Linux x86_64. Setup requires Python 3.12+, curl 7.84.0+ (for `--rate`), tar, zstd, several gigabytes of free disk and memory, and Internet access to the official upstream origins in `DEPENDENCY_PINS.json`.

Use a fresh extracted package and a new sibling prerequisite directory:

```sh
python3 scripts/setup_dependencies.py . ../strict-e-prereqs
```

This downloads and checks the pinned Lean 4.19.0 archive, nine dependency source archives and official Mathlib caches, then runs a dependency-import smoke test. No API key is required. Dependencies are installed locally and keep their licenses and notices. Existing sources are checked rather than silently replaced. If an interrupted installation is rejected, retain it and retry with a new extraction and prerequisite directory. Preserve the pins and lockfile; do not run `lake update` for reproduction.

## Preflight

```sh
python3 -B scripts/rebuild.py \
  --lean ../strict-e-prereqs/lean-4.19.0-linux/bin/lean \
  --source-archives ../strict-e-prereqs/downloads \
  --preflight
```

Expected: `PREFLIGHT_PASS`. Supply the actual compiler binary, not an Elan shim. This checks the compiler version, dependency source pins and project source closure. The setup command separately checks installed toolchain bytes against the pinned official release archive. Exact clean Git dependency checkouts may use the same command without `--source-archives`.

## Fresh Lean replay

```sh
python3 -B scripts/rebuild.py \
  --lean ../strict-e-prereqs/lean-4.19.0-linux/bin/lean \
  --source-archives ../strict-e-prereqs/downloads
```

Every attempt creates a new `replay/fresh-*` directory with empty project output and log directories. The runner uses only project objects accepted in the current run and the external dependencies. It verifies source hashes, dependency object hashes before and after use, all accepted objects at completion, and the compiler/dependency inventory before and after execution.

Flags for each module: `-t0 -j1 -DElab.async=false -DmaxHeartbeats=200000 -DsynthInstance.maxHeartbeats=20000`.

Per-process limits: 300/301 CPU seconds, 600 wall seconds, a 4,831,838,208-byte sampled RSS stop, and a 7,516,192,768-byte address-space cap. A failure stops the run without substituting prior outputs or increasing proof limits.

Success requires a new `result.json` with `FRESH_REPLAY_PASS`, 986 accepted modules, `final_project_exports_rechecked_after_run: true`, and completed source/environment rechecks. The three audit logs must contain the expected declarations and only `propext`, `Classical.choice`, and `Quot.sound`. Identical repeated reports are allowed; conflicting reports fail.

Preserve the first failure's module, log, and resource outcome. A retry starts a new run. Review newly produced logs for local paths and other identifiers before sharing them.

The bounded Python replay is the supported verification route. `project/lakefile.lean` and its lockfile are included for Lean tooling; an ordinary `lake build` is not claimed to be tested for this edition. Offline CI is not a full Lean replay. See [VALIDATION.md](VALIDATION.md).

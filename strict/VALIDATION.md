<!-- Modified for the source-focused edition, 12 November 2026. -->

# Source-edition validation

This source-focused edition has 986 proof/audit modules totaling 4,105,339 bytes. Their bytes are unchanged from the supplied source distribution. The Lean toolchain identifier and dependency lockfile are unchanged.

`python3 -B scripts/check_release.py` checks:

- Complete file integrity against `MANIFEST.json` and source integrity against `SOURCE_MANIFEST.json`.
- The project import ordering and narrow disallowed-token/heartbeat checks.
- Exact source signatures, contexts and reference bindings for 20 contracts, 17 definitions and 7 indexed intermediate obligations across 30 modules.
- Offline regression tests, including controlled compiler fixtures for the replay runner.

The expected success status is `SOURCE_RELEASE_CHECK_PASS`. This command does not run Lean. A passing result is not a theorem-verification certificate.

## Verification boundary

No fresh Lean execution has been performed for this edition. Earlier execution logs, receipts, environment inventories, review documents, and nested evidence archives are deliberately omitted. They have not been edited or presented as new evidence. The original package is preserved separately for private recovery.

The source manifest's `audit_results` are expected outputs for a new run, not observations from a run of this edition. Follow [REPRODUCING.md](REPRODUCING.md) for fresh checking. The final theorem and principal audits must report only `propext`, `Classical.choice`, and `Quot.sound`.

The contract index records exact surface Lean syntax, not freshly elaborated types. No independent external peer review or authenticated Lean execution attestation is claimed.

## Hosted source checks

The [GitHub Actions workflow](.github/workflows/check.yml) runs the same offline Python command on pushes, pull requests and manual dispatch. It does not install Lean or compile the proof. A green workflow establishes only the checks listed above for its recorded commit.

The initial source commit `f4bff67ba5db6fb03aa85597ee77c92352b91cf5` passed [run 43148922314](https://github.com/Hatsuwr/strict-e-unit-classification/actions/runs/43148922314). That run is historical evidence for that commit, not for later changes. Consult the [workflow runs](https://github.com/Hatsuwr/strict-e-unit-classification/actions/workflows/check.yml) for the exact commit being evaluated.

## Changes and status

The mathematical sources, toolchain identifier and lockfile are unchanged. Supporting checks and documentation have been changed to cover this smaller source distribution, without assuming historical evidence files are present. The runner retains source-pin, source-hash, import-binding, final-output and before/after environment checks; its optional historical-environment mode is omitted.

Version 1.0.2 is a public source-focused release. Its documentation and release metadata have been updated for public readers. See [CHANGELOG.md](CHANGELOG.md). Publication status and passing source checks do not establish a fresh Lean replay or independent mathematical review.

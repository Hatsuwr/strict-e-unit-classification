# Changelog

## v5 · Broad classification

- Make the classification of units among values of broad Siegel E-functions the main result. The normalized reciprocal theorem and the arbitrary-argument unit equivalence are both proved.
- Construct the exact algebraic fiber relation and use a pointed Kummer cover to obtain a marked lift with a first-order differential equation.
- Keep the strict-only edition available at its [original commit](https://github.com/Hatsuwr/strict-e-unit-classification/tree/340c7435608e0f1aa1d9b08a0100721a4fd23005).

All 669 modules in the broad source closure passed Lean 4.19.0 verification.
An audited transition retained 582 byte-identical, dependency-closed
source-build receipts and compiled the remaining 87 modules from source.
All source, import, option, receipt, input, export, compiler, and external
inventory checks passed. Each of the three terminal endpoints reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The only Lean change from the selected source baseline raises the finite
elaboration budget in `V5GenericFixedEquiv123` from 150,000 to 300,000
heartbeats. Statements, proof bodies, imports, and kernel trust settings are
unchanged. The replay helper uses bounded 6 GiB RSS and 9 GiB virtual-memory
limits. See [SOURCE_REVISIONS.json](wide/SOURCE_REVISIONS.json) for hashes and
the exact change.

Pinned external dependency objects were cached and hash-bound to the run,
not rebuilt from source. The original strict distribution remains byte-exact;
its historical verification claims are unchanged.

## 1.0.2 · 12 November 2026

Public source-release preparation:

- Separate the mathematical reading path, reproduction instructions, status and license in the README.
- Identify dot as an AI assistant powered by OpenAI, without model-specific authorship or ownership claims.
- Replace stale private-release status and explain the exact scope of hosted source checks.
- Remove publication-authorization fields from check output and release metadata. Offline tests cannot authorize publication.
- Add release-metadata regression checks and refresh the distribution hashes and recorded offline results.

All 986 proof/audit modules (4,105,339 bytes), the source manifest, source contracts, dependency pins, toolchain identifier and dependency lockfile are unchanged from 1.0.1. The Apache-2.0 license text and mathematical references are retained. No fresh Lean replay or independent external peer review is claimed.

## 1.0.1 · 12 November 2026

Initial source-focused distribution with proof modules, mathematical documentation, source-bound contracts, offline checks, pinned prerequisites and a bounded fresh-replay runner. Historical execution and review bundles were omitted. No fresh Lean replay was performed for that source edition.

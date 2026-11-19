# Broad E-value units

A Lean formalization of the unit classification for broad (wide) Siegel E-values.

A nonzero complex number and its reciprocal are both values of broad E-functions at algebraic arguments exactly when the number is α exp(β), with algebraic α ≠ 0 and algebraic β.

The endpoint is [`StrictEUnit.v5_wide_unit_classification140`](wide/project/V5WideFinal140.lean). The proof includes the strict case. The [strict-only source edition](https://github.com/Hatsuwr/strict-e-unit-classification/tree/340c7435608e0f1aa1d9b08a0100721a4fd23005) remains available at its original commit and as an [unchanged release](strict/README.md) in this repository.

Developed by dot, an AI assistant powered by OpenAI.

## Read the mathematics

- [THEOREM.md](THEOREM.md): exact statement and definitions.
- [PROOF-v5.md](PROOF-v5.md): mathematical argument and important hypotheses.
- [strict/CITATION.md](strict/CITATION.md) and [strict/references.bib](strict/references.bib): mathematical foundations and software references for the strict baseline.

## Reproduce the checks

The package includes 669 v5 proof modules and a separate, unchanged strict
distribution. Follow [REPRODUCING.md](REPRODUCING.md) for the supported checks.
The GitHub Actions workflow runs offline checks only, not Lean.

## Status

The complete 669-module v5 source closure passed verification with Lean
4.19.0. An audited transition retained source-build receipts for 582
byte-identical modules in a dependency-closed prefix and compiled the remaining
87 modules from source. All three terminal endpoints report exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The pinned external dependency objects were cached, inventoried, and bound to
the verification by hashes; they were not rebuilt from source. See the
[verification record](wide/VERIFICATION_STATUS.json) and
[source revision ledger](wide/SOURCE_REVISIONS.json) for the precise scope.

No independent external peer review is claimed. See [CHANGELOG.md](CHANGELOG.md)
for the change in scope.

## License

Original project source, supporting scripts and documentation are provided under the Apache License 2.0, to the extent applicable rights subsist. See [LICENSE](LICENSE) and [NOTICE](NOTICE). Third-party dependencies retain their own licenses and notices. No copyright ownership is assigned to an AI assistant.

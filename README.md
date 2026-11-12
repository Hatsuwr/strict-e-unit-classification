<!-- Modified for the source-focused edition, 12 November 2026. -->

# Strict E-value units

A Lean formalization of the unit classification for strict E-values.

A nonzero complex number and its reciprocal are both values of strict E-functions at algebraic arguments exactly when the number is α exp(β), with algebraic α ≠ 0 and algebraic β.

The endpoint is `StrictEUnit.strictEValueUnit_iff_algebraic_scalar_exp`.

Developed by dot, an AI assistant powered by OpenAI.

## Read the mathematics

- [THEOREM.md](THEOREM.md): exact statement and definitions.
- [PROOF.md](PROOF.md): mathematical argument and important hypotheses.
- [CONTRACTS.json](CONTRACTS.json): source-bound interfaces and dependencies.
- [CITATION.md](CITATION.md) and [references.bib](references.bib): mathematical foundations and software references.

## Reproduce the checks

Run `python3 -B scripts/check_release.py` for offline integrity, source-contract and regression checks. These checks do not run Lean.

The distribution contains 986 proof/audit modules, pinned dependency information and a bounded fresh-replay runner. Follow [REPRODUCING.md](REPRODUCING.md) to install the prerequisites and run Lean. The status and limits are stated in [VALIDATION.md](VALIDATION.md) and [AUDIT.md](AUDIT.md).

## Status

Version 1.0.2 is a public source-focused edition. No fresh Lean replay has been performed for this edition. Earlier execution and review bundles are not included, and the offline checks do not verify them. No independent external peer review is claimed.

[Source checks on GitHub Actions](https://github.com/Hatsuwr/strict-e-unit-classification/actions/workflows/check.yml) run the offline Python checks only, not Lean. Check the run for the exact commit you are using. See [VALIDATION.md](VALIDATION.md) for the verification boundary and [CHANGELOG.md](CHANGELOG.md) for release changes.

The theorem concerns strict E-functions. It does not replace their geometric coefficient bounds with the broader subfactorial bounds.

## License

Original project source, supporting scripts and documentation are provided under the Apache License 2.0, to the extent applicable rights subsist. See [LICENSE](LICENSE) and [NOTICE](NOTICE). Third-party dependencies retain their own licenses and notices. No copyright ownership is assigned to an AI assistant.

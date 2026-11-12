<!-- Modified for the source-focused edition, 12 November 2026. -->

# Strict E-value units

A Lean formalization of the unit classification for strict E-values.

A nonzero complex number and its reciprocal are both values of strict E-functions at algebraic arguments exactly when the number is α exp(β), with algebraic α ≠ 0 and algebraic β.

The endpoint is `StrictEUnit.strictEValueUnit_iff_algebraic_scalar_exp`.

Developed by dot, an AI assistant.

## Read the mathematics

- [THEOREM.md](THEOREM.md): exact statement and definitions.
- [PROOF.md](PROOF.md): mathematical argument and important hypotheses.
- [CONTRACTS.json](CONTRACTS.json): source-bound interfaces and dependencies.
- [CITATION.md](CITATION.md) and [references.bib](references.bib): mathematical foundations and software references.

## Check and reproduce

Run `python3 -B scripts/check_release.py` for offline integrity, source-contract and regression checks. These checks do not run Lean.

The distribution contains 986 proof/audit modules, pinned dependency information and a bounded fresh-replay runner. Follow [REPRODUCING.md](REPRODUCING.md) to install the prerequisites and run Lean. The status and limits are stated in [VALIDATION.md](VALIDATION.md) and [AUDIT.md](AUDIT.md).

## Status and license

Version 1.0.1 is a source-focused edition prepared for a private repository. No fresh Lean replay has been performed for this edition. Earlier execution and review bundles are not part of this distribution, and the offline check makes no claim to verify them.

The theorem concerns strict E-functions. It does not replace their geometric coefficient bounds with the broader subfactorial bounds.

Original project source, supporting scripts and documentation are provided under Apache-2.0, to the extent applicable rights subsist. See [LICENSE](LICENSE) and [NOTICE](NOTICE). Dependencies retain their own terms. No copyright ownership is assigned to an AI assistant.

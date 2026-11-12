<!-- Modified for the source-focused edition, 12 November 2026. -->

# Citation and mathematical foundations

**Suggested citation:** *Strict E-value units: Lean formalization*. Version 1.0.2, public source-focused edition, 12 November 2026. [Repository](https://github.com/Hatsuwr/strict-e-unit-classification). Include the exact Git commit; for a downloaded source archive, also record its SHA-256 checksum.

Developed by dot, an AI assistant powered by OpenAI. This is a development credit, not a claim that an AI assistant owns copyright or is a legal author.

The contribution presented here is the formal construction and assembly leading to the strict E-value unit classification. Relation lifting, arithmetic differential-equation theory, product-unit and group-character results, and the units–characters–Picard framework have established antecedents. The references below identify mathematical context and counterparts; exact formal hypotheses and dependencies are indexed in [CONTRACTS.json](CONTRACTS.json). No exhaustive publication-priority or external peer-review claim is made.

## Mathematical references

1. **`fischler-rivoal-2026`** — S. Fischler and T. Rivoal, [*The ring of values of E-functions is not a field*](https://arxiv.org/abs/2610.16603v1), arXiv:2610.16603v1 (2026). Conjecture 1.2 is the target unit classification; Theorem 1.3 treats finite sums of algebraic exponentials. Printed pp. 3–4 distinguish strict bounds from the broader Siegel formulation. [Author PDF](https://www.imo.universite-paris-saclay.fr/~fischler/Ecroix.pdf).

2. **`rivoal-roques-2015`** — T. Rivoal and J. Roques, [*E-functions of order 2 and units of E-values*](https://rivoal.perso.math.cnrs.fr/articles/unitse.pdf), preprint dated 6 November 2015. Printed p. 3 states the unit question; Theorem 5 proves the case of two functions satisfying a two-dimensional first-order system.

3. **`beukers-2006`** — F. Beukers, [*A refined version of the Siegel–Shidlovskii theorem*](https://doi.org/10.4007/annals.2006.163.369), *Annals of Mathematics* **163**(1) (2006), 369–379. Antecedent for lifting algebraic relations among E-values to functional relations.

4. **`andre-2000`** — Y. André, [*Séries Gevrey de type arithmétique, I. Théorèmes de pureté et de dualité*](https://doi.org/10.2307/121045), *Annals of Mathematics* **151**(2) (2000), 705–740. Arithmetic differential-equation and E-operator background.

5. **`conrad-units`** — B. Conrad, [*Units on product varieties*](https://virtualmath1.stanford.edu/~conrad/papers/unitthm.pdf), undated mathematical note. Theorem 1.1 and Corollary 1.2 explain the Rosenlicht product-unit and group-character mechanisms.

6. **`sansuc-1981`** — J.-J. Sansuc, [*Groupe de Brauer et arithmétique des groupes algébriques linéaires sur un corps de nombres*](https://doi.org/10.1515/crll.1981.327.12), *Journal für die reine und angewandte Mathematik* **327** (1981), 12–80. Proposition 6.10, printed p. 43, gives the units–characters–Picard sequence for torsors under connected linear groups, with its stated smoothness hypotheses.

7. **`maurischat-2014`** — A. Maurischat, [*Picard-Vessiot theory of differentially simple rings*](https://doi.org/10.1016/j.jalgebra.2014.04.005), *Journal of Algebra* **409** (2014), 162–181; [arXiv:1304.7663v2](https://arxiv.org/abs/1304.7663v2). Background for Picard–Vessiot torsors over differential rings.


## Software and license

The formalization uses [Lean 4.19.0](https://github.com/leanprover/lean4/releases/tag/v4.19.0) and [mathlib4 at revision c44e0c8ee63ca166450922a373c7409c5d26b00b](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b). [DEPENDENCY_PINS.json](DEPENDENCY_PINS.json) and [project/lake-manifest.json](project/lake-manifest.json) identify all pinned upstream inputs.

Dependency sources and binaries are not bundled. They retain their own licenses and notices when installed. Original project source, supporting scripts and documentation are provided under Apache-2.0, to the extent applicable rights subsist. See [LICENSE](LICENSE) and [NOTICE](NOTICE).

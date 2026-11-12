<!-- Modified for the source-focused edition, 12 November 2026. -->

# Proof guide

Let $k=\overline{\mathbb Q}\subset\mathbb C$, and let $\mathcal E$ be the ring of strict E-values defined in [THEOREM.md](THEOREM.md). The endpoint proves

$$
\mathcal E^\times=\{\alpha e^\beta:\alpha\in k^\times,\ \beta\in k\}.
$$

This guide states the principal interfaces and explains their assembly. The Lean declarations specify the formal claim; [CONTRACTS.json](CONTRACTS.json) binds 20 central interfaces and their supporting definitions to exact source signatures, surrounding context and file hashes. Bibliographic roles are recorded in [CITATION.md](CITATION.md).

## 1. The problem is numerical

A unit gives separate strict E-functions representing $u$ and $u^{-1}$. Their product need only equal one at the evaluation point. For example,

$$
f(z)=e^z+z-1,\qquad g(z)=e^{-z}
$$

satisfy $f(1)g(1)=1$, although $f(z)g(z)=1+(z-1)e^{-z}$ and $f(0)=0$. The proof therefore constructs a different functional unit from the numerical relation.

Algebraic rescaling normalizes the evaluation arguments to one. Closure under addition, multiplication and negation makes the original numerical class a subring; `strictEValueUnit_iff_exists_unit` identifies its units with the original predicate.

## 2. Arithmetic frame and lifting inputs

**Coefficient bridge.** Every strict E-function has all its defining coefficients in one number field. The proof derives this from a nonzero polynomial differential equation and a recurrence, including the finitely many exceptional initial coefficients. The actual/formal series bridge uses the *same* factorial-normalized coefficient sequence; changing the series witness does not change the function. These are contracts C02–C03.

**Common frame.** Given strict E-functions $f,g$, contract C04 constructs a finite matrix $F$ of strict E-functions, a Laurent-polynomial matrix $A(z)$, and a constant algebraic matrix $M$ such that

$$
zF'(z)=A(z)F(z)-F(z)M,\qquad \det F(1)\ne0.
$$

Every root of the minimal polynomial of $M$ is rational. The same Laurent system contains strict E-solution vectors having $f,g$ as coordinates. The resulting value-coverage theorem C07 places both $u$ and $u^{-1}$ in the algebra generated over $k$ by the entries of $F(1)$.

The arithmetic normal-form construction supplies the rational-power and logarithmic factors separately from the entire amplitudes. Its denominator bounds, rank statements and other arithmetic properties are retained for the same selected objects. A minimal differential equation may have apparent singularities; the construction does not assume that every minimal operator is ordinary everywhere.

**Exact relation lifting.** Contract C06 states: for a vector $f$ of strict E-functions satisfying a Laurent first-order system, any polynomial relation $P(f(1))=0$ lifts to

$$
Q(z,f(z))=0,\qquad Q(1,X)=P(X),
$$

with $Q\in k[z,X]$. Laurent coefficients are regular at one. The scalar input C05 assumes a nonzero strict E-function, its chosen minimal cyclic equation, and regularity of that equation at one; it concludes nonvanishing there. Galois-block and quotient arguments prove this scalar input, then linear and homogeneous lifting yield C06. Regularity is an explicit hypothesis of the scalar theorem, not an assumption imposed on every E-function.

The normal-form and lifting routes relate to André's arithmetic differential-equation theory and Beukers's refinement of Siegel–Shidlovskii. The package proves the interfaces it uses; those references provide mathematical antecedents rather than extra Lean assumptions.

## 3. Formal torsor and exact numerical fiber

Rational exponents allow a positive ramification $z=t^N$ and an invertible matrix $Z$ over

$$
B=k[t,t^{-1},\ell].
$$

Here $\ell$ is an independent polynomial variable. Contract C08 constructs a fundamental matrix

$$
Y=\widehat{F(t^N)}Z
$$

for the ramified differential system, with $Z(1,0)=I$. Let $R=B[Y,\det(Y)^{-1}]$ be the constructed differential algebra. Its Picard–Vessiot structure supplies faithful flatness, finite type, constants $k$, and the canonical torsor isomorphism

$$
R\otimes_k H\simeq R\otimes_B R,
$$

where $H$ is the algebra of diagonal differential constants. This is the differential-ring torsor framework underlying the unit argument; see Maurischat for background.

The numerical map is constructed from actual functions and the base point $(t,\ell)=(1,0)$. No evaluation of arbitrary formal Laurent series at one is used.

Contracts C09–C10 establish

$$
\ker(R\longrightarrow\mathbb C)=(t-1,\ell)R,
\qquad S:=k\otimes_B R\hookrightarrow\mathbb C.
$$

Relation lifting is applied to the original functions *before* ramification. After substitution, divisibility by $z-1$ yields divisibility by $t-1$, since $t^N-1$ is divisible by $t-1$. Inverting the determinant preserves the exact kernel because its value at one is nonzero. The invertible base change preserves the generated algebra. This avoids assuming that $F(t^N)$ is again strict E.

Both reciprocal values lie in the image of the whole fiber $S$. Its injectivity makes their preimages inverse units and proves that $S$ is a domain. The torsor's fiber trivialization transfers the domain property to $H$ (C11).

## 4. From a fiber unit to a regular unit

Over an algebraically closed field, units of a tensor product of two domains are pure tensors (C12). Applied to $H\otimes_k H$ and the fiber coaction, this yields a character from a fiber unit, up to a scalar. This is the Rosenlicht product-unit/character mechanism.

The base $B$ is a UFD. The development proves that its invertible fractional ideals are principal and uses this to lift the character to a regular unit $v\in R^\times$ satisfying a first-order differential equation over $B$ (C13). Contract C14 then expresses the original fiber unit as an algebraic scalar unit times the specialization of $v$. The corresponding classical obstruction is described by the units–characters–Picard sequence of Sansuc.

These hypotheses are essential. For the torsor $x\mapsto x^2$ on $\mathbb G_m$, the fiber over one has the unit $(1,2)$, while global units $cx^n$ restrict to $(c,(-1)^n c)$. Thus a factorial base alone does not give arbitrary fiber-unit lifting. The domain of the *whole* fiber, proved above, is a substantive part of this application.

## 5. Arithmetic classification and assembly

Logarithm removal (C15) puts the regular unit and its inverse in the Laurent/determinant-inverse coefficient algebra. That algebra has a genuine analytic realization on $\mathbb C^\times$, built from the ramified entire functions. Its inherited coefficient arithmetic and order-$N$ growth bounds permit C16 to prove

$$
h(t)=c\,t^q\exp(P(t)),\qquad
q\in\mathbb Z,\quad c\in k^\times,\quad
P\in k[t],\quad P(0)=0,\quad\deg P\le N.
$$

At one this is $c\exp(P(1))$, with algebraic parameters. C17 assembles the exact fiber, regular-unit lift and coefficient classification. C18 combines this with the common-frame coverage. C01 supplies the proved common-frame and lifting inputs to C18, so neither remains a hypothesis of the final equivalence.

For the reverse implication, $z\mapsto\alpha e^{\beta z}$ and its reciprocal construction satisfy all strict E conditions when $\alpha\ne0$ and $\alpha,\beta$ are algebraic (C19).

## Scope and historical status

The endpoint addresses the strict growth class in Fischler–Rivoal's Conjecture 1.2; Rivoal–Roques (2015) gives an earlier unit question and a special case. The proposed contribution is the complete strict-class classification and its formal development. Classical geometric and arithmetic ingredients retain their existing attribution; exhaustive priority is not asserted.

Earlier module comments describing an input as “unproved” record the state of that intermediate layer. The `historical_obligations` table in [CONTRACTS.json](CONTRACTS.json) identifies the later closing declarations, including tensor-unit factorization and both final arithmetic inputs. The preserved proof sources remain unchanged.

The theorem supplies an existence classification. It does not give a general recognition algorithm for E-values or settle the broader Siegel-growth formulation. Uniqueness of the algebraic scalar/exponent pair follows additionally from Hermite–Lindemann; that consequence is not asserted here as a separately formalized endpoint.

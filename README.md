This is a proof in Lean 4 of [Descartes' rule of signs](https://en.wikipedia.org/wiki/Descartes%27_rule_of_signs).

First we define the following two operations. `coeffList` turns a polynomial into a `List` of its coefficients, from leading coefficient down to the constant coefficient.
```lean
--auxiliary_defs.lean
variable {α : Type*} [Semiring α] {P : Polynomial α} [DecidableEq α]

noncomputable def coeffList (P : Polynomial α) : List α :=
  if P=0 then [] else (List.range (P.natDegree+1)).reverse.map P.coeff
```
The `sign_variations` definition first filters out all zeros from the list, removes adjacent duplicates (`destutter (·≠·)`), and then takes the length minus one.
```lean
--sign_variations.lean
variable {α : Type*} [LinearOrderedSemiring α] (P : Polynomial α) [DecidableEq α]

noncomputable def sign_variations : ℕ :=
    let coeff_signs := (coeffList P).map SignType.sign;
    let nonzero_signs := coeff_signs.filter (·≠0);
    (nonzero_signs.destutter (·≠·)).length - 1
```
Descartes' Rule of Signs is then stated as the following theorem: the number of strictly positive roots is ≤ the number of sign variations.
```lean
variable {α : Type*} [LinearOrderedField α] (P : Polynomial α) [DecidableEq α]

theorem descartes_rule_of_signs (num_pos_roots : ℕ) (h : num_pos_roots = P.roots.countP (λ x ↦ x > 0)) :
  num_pos_roots ≤ sign_variations P
```
This is true for polynomials with coefficients over any _linearly ordered field_ with _decdiable equality_. Usually Descartes' Rule of Signs is stated over the real numbers, which are a linearly ordered field.

The "decidable equality" seems inconvenient, but technically annoying to remove, because of the way real numbers are defined. For instance, I can define `c` to be the sum of `(Re z - 1/2)/ 2^|Im z|` over all nontrivial roots `z` of the Riemann zeta function, I know this converges to some real number. Now the polynomial `X - c` has either 0 or 1 positive roots depending on the value of `c`, and it has either 0 or 1 sign variations again depending on the value of `c`. For the polynomial `c * X^2 - X - c` it's not even clear whether the degree is 1 or 2. Although Descartes' Rule of Signs holds for any of the three possible signs of `c`, the values `num_pos_roots`, `coeffList P`, and `sign_variations P` are each individiaully noncomputable, in general.

For now, it suffices to say that Descartes' Rule of Signs is proved over the algebraic numbers, which _are_ a linearly ordered field with decidable equality.

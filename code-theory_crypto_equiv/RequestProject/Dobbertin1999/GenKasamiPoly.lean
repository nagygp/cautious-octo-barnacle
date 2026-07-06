import RequestProject.Dobbertin1999.AdditivePolyRootCount
import RequestProject.FiniteField.Thm32

/-!
# Dobbertin (1999) — the generalized Kasami polynomial `q_α`, the MCM polynomial `P_β`, and the linearized polynomial `ℓ` (Layer B)

This module is **Layer B** of the full-paper roadmap
([`DOBBERTIN1999_FULL_ROADMAP.md`](../../DOBBERTIN1999_FULL_ROADMAP.md)) for
Dobbertin (1999), *"Kasami Power Functions, Permutation Polynomials and Cyclic
Difference Sets"*.  It sits directly on the Mathlib-rooted core
(`RequestProject/Dobbertin1999/Core.lean`) and on the linearized-polynomial
root-count tool of Layer A
(`RequestProject/Dobbertin1999/AdditivePolyRootCount.lean`), and provides the
function-level definitions of the paper's Section 2 polynomials that the
permutation criterion (Theorem 1, Layer C) is stated about.

All rational functions use the field convention `0⁻¹ = 0` (so a rational function
is read as the polynomial obtained by replacing `1/z^e` with `z^{(2ⁿ−1)−e}`, and
the map vanishes wherever the denominator vanishes — exactly the convention of
Dillon–Dobbertin, *New cyclic difference sets with Singer parameters*, Section 3).

## The generalized Kasami polynomial `q_α` (Dobbertin [17]; Dillon–Dobbertin `Q_{k,k'}`)

With `k' = 1/k (mod n)`, the paper's permutation polynomial is
```
                  α  +  Σ_{i=1}^{k'} X^{2^{ik}}
   q_α(X)  =  ───────────────────────────────────── ,       α ∈ {0, 1},
                          X^{2^k + 1}
```
where `α = 0` when `k'` is odd and `α = 1` when `k'` is even (the two cases of the
Müller–Cohen–Matthews polynomial).  This is `Q_{k,k'}` of Dillon–Dobbertin
(their eq. before (8)).

## The MCM polynomial `P_β` (paper Section 2)

With `L_k(z) = Σ_{i=0}^{k-1} z^{2^i}` the truncated (linearized) trace and
`Tr z = L_n(z) = Σ_{i=0}^{n-1} z^{2^i}` the absolute trace (valued in the prime
subfield `𝔽₂ ⊆ F`),
```
              (L_k(z) + β·Tr z)^{2^k + 1}
   P_β(z)  =  ────────────────────────────,        β ∈ {0, 1}.
                        z^{2^k}
```

## The linearized polynomial `ℓ` of paper eq. (2)

```
   ℓ(x)  =  c^{2^k}·x^{2^{2k}}  +  x^{2^k}  +  c·x  +  1 .
```
Its `1`-free part `c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x` is an `𝔽₂`-linearized
(additive) polynomial, so — by Layer A — the equation `ℓ(x) = 0` has `0` or
`#(ker)` solutions.  This "0 or a power of two" count is precisely the
root-counting input of Theorem 1.

## Main definitions

* `genKasamiPoly α k k' X` — the generalized Kasami polynomial `q_α`.
* `mcmPoly β k n z` — the MCM polynomial `P_β`.
* `affineLinPoly c k x` — the linearized polynomial `ℓ` of eq. (2).

## Main results

* `genKasamiPoly_zero`, `mcmPoly_zero` — `q_α(0) = 0`, `P_β(0) = 0`.
* `mcmPoly_beta_zero` — `P₀(z) = L_k(z)^{2^k+1}·(z^{2^k})⁻¹`.
* `affineLinPoly_eq_sum_add_one` — `ℓ(x) = (Σ_{i<2k+1} aᵢ·x^{2^i}) + 1`,
  exhibiting `ℓ` as (affine) linearized in the exact shape of Layer A.
* `affineLinPoly_root_count` — via Layer A, `ℓ(x) = 0` has `0` or `#(ker L)`
  solutions.

Everything is `sorry`-free on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace Dobbertin1999.GenKasamiPoly

open Finset DempwolffMueller

variable {F : Type*} [Field F] [CharP F 2]

/-! ## The generalized Kasami polynomial `q_α` -/

/-- The **generalized Kasami polynomial** `q_α` (Dobbertin's `Q_{k,k'}`):
```
   q_α(X) = (α + Σ_{i=1}^{k'} X^{2^{ik}}) · (X^{2^k + 1})⁻¹,
```
with `α = 0` for `k'` odd and `α = 1` for `k'` even, under the convention
`0⁻¹ = 0`. -/
noncomputable def genKasamiPoly (α : F) (k k' : ℕ) (X : F) : F :=
  (α + ∑ i ∈ Finset.range k', X ^ (2 ^ ((i + 1) * k))) * (X ^ (2 ^ k + 1))⁻¹

/-
`q_α(0) = 0` (the map vanishes at `0`, where the denominator vanishes).
-/
omit [CharP F 2] in
theorem genKasamiPoly_zero (α : F) (k k' : ℕ) (hk : 0 < k) :
    genKasamiPoly α k k' (0 : F) = 0 := by
  unfold genKasamiPoly; simp +decide [ hk.ne' ] ;

/-! ## The MCM polynomial `P_β` -/

/-- The **MCM polynomial** `P_β` (paper Section 2):
```
   P_β(z) = (L_k(z) + β·Tr z)^{2^k + 1} · (z^{2^k})⁻¹,
```
where `L_k = truncTrace k` and `Tr = truncTrace n` (the absolute trace, valued in
`𝔽₂ ⊆ F`), under the convention `0⁻¹ = 0`. -/
noncomputable def mcmPoly (β : F) (k n : ℕ) (z : F) : F :=
  (truncTrace k z + β * truncTrace n z) ^ (2 ^ k + 1) * (z ^ (2 ^ k))⁻¹

/-
`P_β(0) = 0`.
-/
omit [CharP F 2] in
theorem mcmPoly_zero (β : F) (k n : ℕ) : mcmPoly β k n (0 : F) = 0 := by
  unfold mcmPoly;
  simp +decide [ DempwolffMueller.truncTrace_zero ]

/-
The classical case `β = 0`: `P₀(z) = L_k(z)^{2^k+1} · (z^{2^k})⁻¹` — the
Müller–Cohen–Matthews permutation polynomial.
-/
omit [CharP F 2] in
theorem mcmPoly_beta_zero (k n : ℕ) (z : F) :
    mcmPoly (0 : F) k n z = truncTrace k z ^ (2 ^ k + 1) * (z ^ (2 ^ k))⁻¹ := by
  simp +decide [ mcmPoly ]

/-! ## The linearized polynomial `ℓ` of eq. (2) -/

/-- The linearized polynomial `ℓ(x) = c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x + 1` of
Dobbertin's eq. (2). -/
noncomputable def affineLinPoly (c : F) (k : ℕ) (x : F) : F :=
  c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1

/-- The coefficient sequence exhibiting the `1`-free part of `ℓ` as a Layer-A
linearized polynomial `Σ_i aᵢ·x^{2^i}`: `a₀ = c`, `a_k = 1`, `a_{2k} = c^{2^k}`,
all others `0`. -/
noncomputable def ellCoeff (c : F) (k : ℕ) : ℕ → F :=
  fun i => if i = 0 then c else if i = k then 1 else if i = 2 * k then c ^ (2 ^ k) else 0

/-
`ℓ(x) = (Σ_{i<2k+1} aᵢ·x^{2^i}) + 1`, exhibiting `ℓ` as an affine-linearized
polynomial in the exact `Σ aᵢ·x^{2^i}` shape consumed by Layer A.
-/
theorem affineLinPoly_eq_sum_add_one (c : F) (k : ℕ) (hk : 0 < k) (x : F) :
    affineLinPoly c k x =
      (∑ i ∈ Finset.range (2 * k + 1), ellCoeff c k i * x ^ (2 ^ i)) + 1 := by
  unfold affineLinPoly ellCoeff; simp +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', hk.ne' ] ;
  grind

variable [Fintype F] [DecidableEq F]

/-- **Root count of `ℓ` (via Layer A).**  The equation `ℓ(x) = 0` has `0` or
`#(ker L)` solutions, where `L` is the linear part of `ℓ`.  This is the finite
"0 or a power of two" root count that Theorem 1's permutation criterion rests on;
it is `Dobbertin1999.AdditivePolyRootCount.card_fiber_affine_linearized`
specialised to the coefficient sequence of `ℓ`. -/
theorem affineLinPoly_root_count (c : F) (k : ℕ) (hk : 0 < k) :
    Nat.card {x : F // affineLinPoly c k x = 0} = 0 ∨
    Nat.card {x : F // affineLinPoly c k x = 0} =
      Nat.card {x : F //
        (∑ i ∈ Finset.range (2 * k + 1), ellCoeff c k i * x ^ (2 ^ i)) = 0} := by
  have key : ∀ x : F, affineLinPoly c k x = 0 ↔
      (∑ i ∈ Finset.range (2 * k + 1), ellCoeff c k i * x ^ (2 ^ i)) + 1 = 0 := by
    intro x; rw [affineLinPoly_eq_sum_add_one c k hk]
  have e : {x : F // affineLinPoly c k x = 0} ≃
      {x : F // (∑ i ∈ Finset.range (2 * k + 1), ellCoeff c k i * x ^ (2 ^ i)) + 1 = 0} :=
    Equiv.subtypeEquivRight key
  rw [Nat.card_congr e]
  exact AdditivePolyRootCount.card_fiber_affine_linearized (ellCoeff c k) (2 * k + 1) 1

end Dobbertin1999.GenKasamiPoly
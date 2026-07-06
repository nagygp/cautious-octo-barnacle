import RequestProject.Steiner.CCZ

/-!
# The Flystel structure (Section 2.3)

We transcribe Definition 2.4 (open and closed Flystel), the functional
representation of the closed Flystel (Eq. (11)), and Proposition 2.5
(CCZ-equivalence of the open and closed Flystel).

We identify `Fq²` with `Fin 2 → Fq` for compatibility with the Walsh transform,
and also provide the more readable `Fq × Fq` presentation of the closed Flystel.
-/

open scoped BigOperators

namespace Flystel

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- **Definition 2.4 (2) / Eq. (11)** (closed Flystel, `Fq × Fq` form).
For a permutation `E : Fq → Fq` and functions `Q_γ, Q_δ : Fq → Fq`, the closed
Flystel of `(Q_γ, E, Q_δ)` is
`V (y, v) = (E (y - v) + Q_γ y, E (y - v) + Q_δ v)`. -/
def closedFlystelProd (E Qγ Qδ : Fq → Fq) : Fq × Fq → Fq × Fq :=
  fun p => (E (p.1 - p.2) + Qγ p.1, E (p.1 - p.2) + Qδ p.2)

/-- The closed Flystel as a map `Fq² = (Fin 2 → Fq) → (Fin 2 → Fq)`. -/
def closedFlystel (E Qγ Qδ : Fq → Fq) :
    (Fin 2 → Fq) → (Fin 2 → Fq) :=
  fun p => ![E (p 0 - p 1) + Qγ (p 0), E (p 0 - p 1) + Qδ (p 1)]

/-!
## Correction logged — the open Flystel uses `E⁻¹`

The first transcription used the *forward* map `E` in the middle Feistel round:

```
-- def openFlystelProd (E Qγ Qδ : Fq → Fq) : Fq × Fq → Fq × Fq :=
--   fun p =>
--     let x₁ := p.1 - Qγ p.2
--     let y₁ := p.2 - E x₁          -- ← should be E⁻¹ x₁
--     (x₁ + Qδ y₁, y₁)
-- def openFlystel (E Qγ Qδ : Fq → Fq) : (Fin 2 → Fq) → (Fin 2 → Fq) :=
--   fun p =>
--     let x₁ := p 0 - Qγ (p 1)
--     let y₁ := p 1 - E x₁          -- ← should be E⁻¹ x₁
--     ![x₁ + Qδ y₁, y₁]
```

That wiring makes **Proposition 2.5 false**: a `#eval` over `F₁₁` with the
*non-involutive* power permutation `E = x³` shows `Γ_H ≠ A(Γ_V)` for the paper's
matrix `A` (it only coincidentally held for involutive `E`, e.g. `x⁵` over
`F₇`).  Reading Fig. 1a against `Γ_H = A(Γ_V)` forces the middle round to use the
*inverse* permutation `E⁻¹`, so that `y₁ = y − E⁻¹(x₁) = v` recovers the second
closed-Flystel coordinate.  We therefore correct the definitions to use
`Function.invFun E`, a genuine two-sided inverse exactly when `E` is bijective
(the standing hypothesis "`E` is a permutation").  With this fix Proposition 2.5
is provable; see `closed_openFlystel_CCZEquiv`.
-/

/-- **Definition 2.4 (1)** (open Flystel, `Fq × Fq` form).
The open Flystel is the three-round Feistel network of Fig. 1a.  With input
`(x, y)` it computes
`x ← x − Q_γ y;  y ← y − E⁻¹ x;  x ← x + Q_δ y`, returning the updated `(x, y)`,
where `E⁻¹ = Function.invFun E`.  (See the correction note above.) -/
noncomputable def openFlystelProd (E Qγ Qδ : Fq → Fq) : Fq × Fq → Fq × Fq :=
  fun p =>
    let x₁ := p.1 - Qγ p.2
    let y₁ := p.2 - Function.invFun E x₁
    (x₁ + Qδ y₁, y₁)

/-- The open Flystel as a map `Fq² = (Fin 2 → Fq) → (Fin 2 → Fq)`. -/
noncomputable def openFlystel (E Qγ Qδ : Fq → Fq) :
    (Fin 2 → Fq) → (Fin 2 → Fq) :=
  fun p =>
    let x₁ := p 0 - Qγ (p 1)
    let y₁ := p 1 - Function.invFun E x₁
    ![x₁ + Qδ y₁, y₁]

/-
**Proposition 2.5** ([Anemoi, Proposition 1]).
Let `Fq` be a finite field, `E : Fq → Fq` a permutation, and `Q_γ, Q_δ : Fq → Fq`
functions.  Then the closed and open Flystel of `(Q_γ, E, Q_δ)` are
CCZ-equivalent.

The proof exhibits the permutation matrix
`A = ![![0,0,1,0], ![1,0,0,0], ![0,0,0,1], ![0,1,0,0]]`
and verifies `Γ_H = A (Γ_V)`.
-/
omit [Fintype Fq] in
theorem closed_openFlystel_CCZEquiv (E Qγ Qδ : Fq → Fq) (hE : Function.Bijective E) :
    CCZEquiv (openFlystel E Qγ Qδ) (closedFlystel E Qγ Qδ) := by
  -- Define the affine permutation A.
  let A : AffinePerm 4 Fq := ⟨
    !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
    0,
    by
      refine' ⟨ _, _ ⟩;
      · intro x y hxy; simp_all +decide [ ← List.ofFn_inj ] ;
        tauto;
      · intro b; use Matrix.vecCons ( b 1 ) ( Matrix.vecCons ( b 3 ) ( Matrix.vecCons ( b 0 ) ( Matrix.vecCons ( b 2 ) 0 ) ) ) ; ext i; fin_cases i <;> simp +decide ;
  ⟩
  generalize_proofs at *;
  refine' ⟨ A, _ ⟩;
  ext ⟨x, y⟩; simp [graph, openFlystel, closedFlystel];
  constructor <;> intro h;
  · refine' ⟨ fun i => if i = 0 then x 1 else x 1 - Function.invFun E ( x 0 - Qγ ( x 1 ) ), _, _ ⟩ <;> simp +decide [ ← h, Fin.append ];
    · ext i; fin_cases i <;> simp +decide [ A, AffinePerm.toFun ] ;
      · simp +decide [ Fin.addCases, Matrix.vecHead, Matrix.vecTail ];
        rw [ Function.invFun_eq ( hE.2 _ ), sub_add_cancel ];
      · simp +decide [ Matrix.vecHead, Fin.addCases ];
    · simp +decide [ A, AffinePerm.toFun ];
      simp +decide [ Fin.addCases, Matrix.vecHead, Matrix.vecTail ];
      ext i; fin_cases i <;> simp +decide [ Function.invFun_eq ( hE.2 _ ) ] ;
  · obtain ⟨ a, rfl, rfl ⟩ := h; simp +decide [ A, AffinePerm.toFun ] ;
    simp +decide [ Fin.addNat, Matrix.vecHead, Matrix.vecTail, Fin.append ];
    simp +decide [ Fin.addCases ];
    rw [ Function.leftInverse_invFun hE.injective ] ; aesop

/-! ## Conjecture 2.6 (the Anemoi designers' conjecture)

For a prime `p`, a non-trivial additive character `ψ`, and an open Flystel `H`
over `F_p`, the Anemoi designers conjectured
`max_{a ∈ F_p², b ∈ F_p² \ {0}} |W_H(ψ, a, b)| ≤ p · log p`.

The present paper *resolves this conjecture in the affirmative* for `E` a power
permutation and `Q_γ, Q_δ` quadratic with identical leading coefficient
(see `RequestProject.MainResults`). -/

/-- **Conjecture 2.6** ([Anemoi, Conjecture 1]), transcribed.
`max_{a, b ≠ 0} |W_H(ψ, a, b)| ≤ p · log p`. -/
def Conjecture26 (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ)
    (E Qγ Qδ : ZMod p → ZMod p) : Prop :=
  ∀ a b : Fin 2 → ZMod p, b ≠ 0 →
    ‖walshTransform ψ (openFlystel E Qγ Qδ) a b‖ ≤ (p : ℝ) * Real.log p

end Flystel
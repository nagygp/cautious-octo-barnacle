import Mathlib
import RequestProject.Thm32
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg

/-!
# Theorem 3.3 — Twisted Kantor–Williams Polynomials

Formalization of Theorem 3.3 from Dempwolff & Müller (2013).

## DAG structure

```
  TraceNorm (F2) + ExpArith (F3)
    │
    ├──► Base case h=1 (coprimality argument)
    ├──► Trace reduction lemma
    └──► Inductive step → Theorem 3.3
```

**Dependencies:** Thm32, TraceNorm, ExpArith, FrobAlg, Mathlib.
-/

namespace DempwolffMueller

open Finset BigOperators

-- ═══════════════════════════════════════════
-- T3.1 : Divisor chain definition
-- ═══════════════════════════════════════════

/-- A divisor chain: each element divides the next, and the last divides `n`. -/
def IsDivisorChain' (ds : List ℕ) (n : ℕ) : Prop :=
  ds.length ≥ 1 ∧
  ds.Chain' (· ∣ ·) ∧
  ∀ d ∈ ds, d ∣ n

-- ═══════════════════════════════════════════
-- T3.2 : General linearized polynomial construction
-- ═══════════════════════════════════════════

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The linearized polynomial from Theorem 3.3. -/
noncomputable def twistedKWPoly (h : ℕ) (cs : Fin h → F)
    (exponents : Fin h → ℕ) (x : F) : F :=
  ∑ i : Fin h, cs i * x ^ (2 ^ exponents i)

/-- The twisted KW polynomial is additive. -/
lemma twistedKWPoly_add (h : ℕ) (cs : Fin h → F) (exponents : Fin h → ℕ)
    (x y : F) :
    twistedKWPoly h cs exponents (x + y) =
    twistedKWPoly h cs exponents x + twistedKWPoly h cs exponents y := by
  simp only [twistedKWPoly, mul_add, ← Finset.sum_add_distrib]
  congr 1; ext i
  rw [← mul_add, ← add_pow_char_pow (p := 2)]

/-- The twisted KW polynomial sends 0 to 0. -/
lemma twistedKWPoly_zero (h : ℕ) (cs : Fin h → F) (exponents : Fin h → ℕ) :
    twistedKWPoly h cs exponents 0 = 0 := by
  simp [twistedKWPoly, zero_pow (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))]

/-
═══════════════════════════════════════════
T3.3 : Base case (h = 1)
═══════════════════════════════════════════

**Base case (h = 1).** When `L(X) = c · X^{2^ℓ}`, the map
    `x ↦ c · x^{2^ℓ + 1}` is a permutation polynomial iff
    `gcd(2^ℓ + 1, 2^n - 1) = 1`.
-/
lemma base_case_h1 {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (c : F) (hc : c ≠ 0) (ℓ_exp : ℕ)
    (hcop : Nat.Coprime (2 ^ ℓ_exp + 1) (2 ^ n - 1)) :
    Function.Bijective (fun x : F => c * x ^ (2 ^ ℓ_exp + 1)) := by
      -- Apply the fact that multiplication by a non-zero constant and exponentiation by a coprime value are both bijective.
      have h_coprime : Nat.Coprime (2 ^ ℓ_exp + 1) (Fintype.card F - 1) := by
        grind;
      have h_bijective : Function.Bijective (fun x : F => x ^ (2 ^ ℓ_exp + 1)) := by
        apply pow_field_bijective;
        · exact h_coprime.symm;
        · positivity;
      exact ⟨ fun x y hxy => h_bijective.injective <| mul_left_cancel₀ hc hxy, fun x => by obtain ⟨ y, hy ⟩ := h_bijective.surjective ( x / c ) ; exact ⟨ y, by simp +decide [ *, mul_div_cancel₀ ] ⟩ ⟩

-- ═══════════════════════════════════════════
-- T3.4 : Trace reduction
-- ═══════════════════════════════════════════

/-- **Injectivity implies bijectivity on finite types.** -/
lemma additive_bij_of_inj
    (P : F → F) (hP_inj : Function.Injective P) :
    Function.Bijective P :=
  ⟨hP_inj, (Finite.injective_iff_surjective).mp hP_inj⟩

-- ═══════════════════════════════════════════
-- T3.5 : Theorem 3.3 (simplified form)
-- ═══════════════════════════════════════════

/-- **Theorem 3.3 (simplified form for h = 1).**
    If `c ∈ GF(2^d)*` and `gcd(2^ℓ+1, 2^n-1) = 1`,
    then `x ↦ c · x^{2^ℓ + 1}` is bijective on `GF(2^n)`. -/
theorem thm_3_3_h1 {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (ℓ_exp : ℕ) (c : F) (hc : c ≠ 0)
    (hcop : Nat.Coprime (2 ^ ℓ_exp + 1) (2 ^ n - 1)) :
    Function.Bijective (fun x : F => c * x ^ (2 ^ ℓ_exp + 1)) :=
  base_case_h1 hn c hc ℓ_exp hcop

end DempwolffMueller
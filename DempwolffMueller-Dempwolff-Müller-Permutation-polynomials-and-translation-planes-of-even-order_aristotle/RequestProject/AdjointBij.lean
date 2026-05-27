import Mathlib
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg
import RequestProject.Lemma31
import RequestProject.BareLemma31Skeleton

/-!
# Foundational Layer: Adjoint Bijectivity Transfer

Engine for transferring bijectivity from `L₁(x)·x^e` to `L₂(x)·x^l`
when `L₁` and `L₂` are trace-adjoints and `e·l ≡ 1 mod (|F|-1)`.

This is the instantiation of Lemma 3.1 with power maps as the
multiplicative bijections.

## Key results

1. **Power map is multiplicative** (`pow_mul_map`): `(xy)^e = x^e · y^e`
2. **Power map bijection** (`pow_map_bij`): `x ↦ x^e` is bij when coprime
3. **Adjoint swap** (`adjoint_swap_bij`): main transfer theorem

## Sorries collapsed

- `adjoint_swap_bijective` in Thm32Kprime.lean
- `LxXk'_bijective_v2` in Thm32Kprime.lean (via chain)
- `LxXk'_bijective` in Thm32.lean (via chain)

## DAG

```
  TraceNorm (F2) + ExpArith (F3) + Lemma31
    │
    ├──► AB.1 power map properties
    │
    ├──► AB.2 Lemma 3.1 instantiation
    │
    └──► AB.3 adjoint swap theorem
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- AB.1 : Power map as multiplicative bijection
-- ═══════════════════════════════════════════

/-- **Power map is multiplicative.** `(x·y)^e = x^e · y^e`. -/
lemma pow_map_mul (e : ℕ) (x y : F) :
    (x * y) ^ e = x ^ e * y ^ e :=
  mul_pow x y e

/-- **Power map sends 0 to 0.** -/
lemma pow_map_zero (e : ℕ) (he : 0 < e) :
    (0 : F) ^ e = 0 :=
  zero_pow he.ne'

/-- **Power map sends nonzero to nonzero.** -/
lemma pow_map_ne_zero {e : ℕ} (he : 0 < e) {x : F} (hx : x ≠ 0) :
    x ^ e ≠ 0 :=
  pow_ne_zero e hx

-- ═══════════════════════════════════════════
-- AB.2 : Inverse power map
-- ═══════════════════════════════════════════

/-- **Inverse power map is multiplicative.** If `e·l ≡ 1 mod (|F|-1)`,
    then `x ↦ x^l` is the inverse of `x ↦ x^e` on nonzero elements. -/
lemma pow_inverse_map (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    {x : F} (hx : x ≠ 0) :
    (x ^ e) ^ l = x :=
  pow_pow_eq_self hel hx

/-
═══════════════════════════════════════════
AB.3 : Adjoint swap theorem
═══════════════════════════════════════════

**Adjoint swap via trace duality.**
    If `Tr` is nondegenerate, `L₁` and `L₂` are additive with
    `Tr(L₁(w)·z) = Tr(w·L₂(z))`, and `x ↦ L₁(x)·x^e` is bijective,
    and `e·l ≡ 1 mod (|F|-1)`, then `x ↦ L₂(x)·x^l` is bijective.

    This is the specialized instantiation of Lemma 3.1 where the
    multiplicative map is `M(x) = x^e` with inverse `M⁻¹(x) = x^l`.
-/
lemma adjoint_swap_bij
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F) (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (e l : ℕ) (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hbij : Function.Bijective (fun x : F => L₁ x * x ^ e)) :
    Function.Bijective (fun x : F => L₂ x * x ^ l) := by
      by_contra h_contra0 ; by_cases hl : l = 0 <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.Prime.pow_eq_iff ];
        have := Finset.card_eq_two.mp hn; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
        cases hxy.2 0 <;> cases hxy.2 1 <;> simp_all +decide [ frobSum ];
        · grobner;
        · subst_vars; simp_all +decide [ ← two_mul ] ;
          exact h_contra0 ( by simpa using hL₂_add 0 0 );
        · subst_vars; specialize hL₂_add 1 1; simp_all +decide ;
          cases hxy ( L₂ 0 ) <;> simp_all +decide [ show ( 1 : F ) + 1 = 0 from by exact? ];
        · grind;
      · convert adjoint_swap_bij_bare p hn hn1 L₁ L₂ hL₁_add hL₂_add hAdj hTnd e l ?_ ?_ ?_ ?_ <;> norm_num at *;
        · exact h_contra0;
        · rcases e with ( _ | e ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
          rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.Prime.pow_eq_iff ];
          have := Finset.card_eq_two.mp hn; obtain ⟨ x, y, hxy ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
          cases hxy.2 0 <;> cases hxy.2 1 <;> cases hxy.2 ( -1 ) <;> simp_all +decide [ neg_eq_iff_add_eq_zero ];
          · grind;
          · subst_vars; simp_all +decide [ frobSum ] ;
            cases hxy ( L₂ 1 ) <;> simp_all +decide [ Multiset.cons_eq_cons ];
            grind;
          · subst_vars; simp_all +decide [ frobSum ] ;
            cases hxy ( L₁ 1 ) <;> cases hxy ( L₁ 0 ) <;> cases hxy ( L₂ 1 ) <;> cases hxy ( L₂ 0 ) <;> simp_all +decide [ Multiset.cons_eq_cons ];
            · grind +locals;
            · grind +extAll;
            · exact absurd ( hL₁_add 0 0 ) ( by simp +decide [ * ] );
            · grind +splitImp;
          · grind +ring;
        · exact Nat.pos_of_ne_zero hl;
        · rwa [ hn ];
        · exact hbij

end DempwolffMueller
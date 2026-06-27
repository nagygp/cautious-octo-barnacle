import ConjecturesMTupleTripleCount.Foundations.KasamiAxKatzAK3
import Mathlib

/-!
# Foundations, Layer AK3.1 — the Teichmüller character of GF(2ⁿ) (first sub-sub-layer)

This module opens the **sub-sub-path of Layer AK3** laid out in
`Docs/VanishFutureDirections.md` §7.  Layer AK3 (`KasamiAxKatzAK3.lean`)
supplied the digit-sum preliminaries and the Gauss-sum structural toolkit; its
open deep core is **Stickelberger's congruence** — the `2`-adic valuation
`v₂(g(χ))` of a Gauss sum read off the base-`2` digit sum of the *exponent* of
the multiplicative character `χ`.  Following the program note, that core needs
three new pieces of supporting theory, organized here as a refined chain:

```
   AK3.1:  the Teichmüller character ω of GF(2ⁿ)               ◑ THIS MODULE
           — a generator of the character group, order q−1;
             every χ is a power ωᵏ, and the exponent k carries
             the digit sum s₂(k) Stickelberger acts on
           │
           ▼
   AK3.2:  the prime above 2 in the cyclotomic ring ℤ[μ]       ⏳ TODO
           — μ a primitive (q−1)-th root; the local valuation v
             at a prime over 2, with v(g(χ)) the target quantity
           │
           ▼
   AK3.3:  the Gross–Koblitz / Stickelberger factorization     ⏳ TODO
           — v(g(ω^{-s})) = s₂(s) (the digit sum), the deep core
```

This module establishes the **first step**, AK3.1: the Teichmüller character and
the cyclotomic-integer framework, all from Mathlib's `MulChar` infrastructure.

## What is established (sorry-free)

Fix a target integral domain `R` with a primitive `(q−1)`-th root of unity `μ`
(the cyclotomic setting `ℤ[μ] ⊆ R`, `q = #F`).

1. **Existence of the Teichmüller character** `ω` — a multiplicative character of
   `F` of order exactly `q−1` (`exists_teichmuller_char`,
   `teichmuller_order_eq_card_sub_one`).

2. **`ω` generates the character group** — every multiplicative character `χ` is
   a power of `ω` (`mulChar_mem_zpowers_teichmuller`), so `χ = ω^{-s}` for a
   well-defined exponent `s`; this exponent is what Stickelberger's digit sum
   `s₂` is applied to.

3. **The character-value / root-of-unity dictionary** — every nonzero value
   `χ(a)` is a power `μ^k` of the fixed primitive root
   (`mulChar_apply_eq_root_pow`), and all values lie in the cyclotomic ring
   `ℤ[μ]` (`mulChar_value_mem_cyclotomic_adjoin`) — the ring in which AK3.2's
   prime above `2` lives.

## Scope

This layer is sorry-free.  It builds the Teichmüller-character + cyclotomic-ring
framework on which Stickelberger's valuation operates.  The prime-above-`2`
valuation (AK3.2) and the digit-sum factorization (AK3.3) — the genuinely deep
`p`-adic / Gross–Koblitz content absent from Mathlib — are the open frontier,
deliberately neither axiomatized nor `sorry`-ed.

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5 (multiplicative characters of finite
fields, the Teichmüller character); Ireland–Rosen, *A Classical Introduction to
Modern Number Theory*, Ch. 14 (Gauss sums, Stickelberger); Washington,
*Introduction to Cyclotomic Fields*, Ch. 6.
-/

namespace Vanish.Foundations

open MulChar BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R]

/-! ## 1. Existence of the Teichmüller character -/

omit [IsDomain R] in
/-- **The Teichmüller character exists.**  Given a primitive `(q−1)`-th root of
unity `μ` in the target, there is a multiplicative character `ω` of `F` of order
exactly `q − 1 = #Fˣ`.  (A restatement of Mathlib's
`MulChar.exists_mulChar_orderOf_eq_card_units`.) -/
theorem exists_teichmuller_char {μ : R} (hμ : IsPrimitiveRoot μ (Fintype.card Fˣ)) :
    ∃ ω : MulChar F R, orderOf ω = Fintype.card Fˣ :=
  MulChar.exists_mulChar_orderOf_eq_card_units F hμ

omit [IsDomain R] in
/-- **The Teichmüller order is `q − 1`.**  Restating the order of `ω` through
`#Fˣ = #F − 1`. -/
theorem teichmuller_order_eq_card_sub_one {ω : MulChar F R}
    (hω : orderOf ω = Fintype.card Fˣ) : orderOf ω = Fintype.card F - 1 := by
  rw [hω, Fintype.card_units]

/-! ## 2. The Teichmüller character generates the character group -/

/-
**`ω` generates the character group.**  Since the group `MulChar F R` has
order `#Fˣ` (when the target has enough roots of unity) and `ω` has order `#Fˣ`,
every multiplicative character `χ` is an integer power of `ω`; equivalently
`χ = ω^{-s}` for the Stickelberger exponent `s`.
-/
theorem mulChar_mem_zpowers_teichmuller {μ : R}
    (hμ : IsPrimitiveRoot μ (Fintype.card Fˣ)) {ω : MulChar F R}
    (hω : orderOf ω = Fintype.card Fˣ) (χ : MulChar F R) :
    χ ∈ Subgroup.zpowers ω := by
  convert Subgroup.mem_top χ;
  have h_card : Nat.card (MulChar F R) = Fintype.card Fˣ := by
    convert MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity F R;
    · rw [ Nat.card_eq_fintype_card ];
    · have h_exp : Monoid.exponent Fˣ = Fintype.card Fˣ := by
        rw [ Monoid.exponent_eq_iSup_orderOf ];
        · obtain ⟨g, hg⟩ : ∃ g : Fˣ, orderOf g = Fintype.card Fˣ := by
            have := IsCyclic.exists_generator ( α := Fˣ );
            obtain ⟨ g, hg ⟩ := this; use g; rw [ orderOf_eq_card_of_forall_mem_zpowers hg ] ; simp +decide ;
          exact le_antisymm ( ciSup_le fun x => Nat.le_of_dvd ( Fintype.card_pos ) ( orderOf_dvd_card ) ) ( hg ▸ le_ciSup ( Finite.bddAbove_range fun x : Fˣ => orderOf x ) g );
        · exact fun g => orderOf_pos g;
      constructor;
      · exact ⟨ μ, h_exp.symm ▸ hμ ⟩;
      · exact inferInstance;
  exact Subgroup.eq_top_of_card_eq _ ( by aesop )

/-! ## 3. The character-value / root-of-unity dictionary -/

/-
**Character values are powers of the primitive root.**  For a primitive
`(q−1)`-th root `μ` and `a ≠ 0`, `χ(a) = μ^k` for some `k < q − 1`.  (The
discrete-logarithm dictionary underlying Stickelberger's digit-sum exponent.)
-/
theorem mulChar_apply_eq_root_pow {μ : R}
    (hμ : IsPrimitiveRoot μ (Fintype.card Fˣ)) (χ : MulChar F R) {a : F}
    (ha : a ≠ 0) : ∃ k < Fintype.card Fˣ, χ a = μ ^ k := by
  convert MulChar.exists_apply_eq_pow ( show χ ^ Fintype.card Fˣ = 1 from ?_ ) hμ ?_ using 1
  all_goals generalize_proofs at *;
  · exact MulChar.pow_card_eq_one χ;
  · exact ha

/-
**Character values are cyclotomic integers.**  Every value `χ(a)` lies in the
ring `ℤ[μ]` generated by a primitive `(q−1)`-th root of unity — the cyclotomic
ring in which AK3.2's prime above `2` lives.
-/
theorem mulChar_value_mem_cyclotomic_adjoin {μ : R}
    (hμ : IsPrimitiveRoot μ (Fintype.card Fˣ)) (χ : MulChar F R) (a : F) :
    χ a ∈ Algebra.adjoin ℤ {μ} := by
  by_cases ha : a = 0;
  · aesop;
  · obtain ⟨ k, hk₁, hk₂ ⟩ := mulChar_apply_eq_root_pow hμ χ ha;
    exact hk₂.symm ▸ Subalgebra.pow_mem _ ( Algebra.subset_adjoin ( Set.mem_singleton μ ) ) _

end Vanish.Foundations
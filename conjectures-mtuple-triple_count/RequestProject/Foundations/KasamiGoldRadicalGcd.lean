import RequestProject.Foundations.RankSpectrum
import RequestProject.Foundations.GoldQuadratic
import Mathlib

/-!
# Foundations — Direction (DD), first-principles module DD-fp-4c: the Frobenius fixed-point gcd count

This module is a **further from-scratch foundational rung of direction (DD)**
(the Dillon–Dobbertin equation (12) programme of
`Docs/VanishFutureDirections.md`, §15), supplying the **gcd computation** named in
DD-fp-4 / DD-fp-5 — the step that pins the auxiliary Gold-form radical to a single
dimension.

The radical of a Gold polar form is the kernel of an explicit linearized
polynomial (`KasamiGoldPolar.lean`), and the size of such a kernel is governed by
the **gcd of the Frobenius exponents with `n`**.  The clean reusable building block
is the cardinality of the fixed set of a Frobenius power: in `GF(2ⁿ)`,

```
   #{ u | u^{2^a} = u }  =  2^{gcd(a, n)}.
```

The set `{u | u^{2^a} = u}` is the fixed field of `φ^a` (`φ = ` the Frobenius
`x ↦ x²`), i.e. the subfield `GF(2^{gcd(a,n)})`, whose order is `2^{gcd(a,n)}`.
Equivalently it is the set of roots of the additive (linearized) polynomial
`X^{2^a} − X = X^{2^a} + X`, and the polynomial-gcd identity
`gcd(X^{2^a} + X, X^{2^n} + X) = X^{2^{gcd(a,n)}} + X` counts them.

The DD core needs the case `gcd = 1`, giving a **two-element** (one-dimensional)
fixed set — exactly the `|radical| = 2` shape consumed by
`quadForm_radical_two_spectrum` (`KasamiGoldRadical.lean`).

## Results

* `frobeniusFixed_card_eq_two_pow_gcd` — `#{u | u^{2^a} = u} = 2^{gcd(a,n)}`.
* `frobeniusFixed_card_eq_two_of_coprime` — for `gcd(a,n) = 1`, the fixed set has
  exactly `2` elements (the one-dimensional case).

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is the gcd-of-exponents root count for
linearized polynomials.  Identifying the auxiliary Gold-form radical *with* such a
fixed set for the Kasami parameters is the remaining DD-fp-4 content, the carried
core.

## Sources

Dillon–Dobbertin (FFA 2004), Appendix A.4; Lidl–Niederreiter, *Finite Fields*,
Ch. 2–3 (subfields, linearized polynomials).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
**The Frobenius fixed-point gcd count.**  In a field `F` of order `2ⁿ`, the set
of elements fixed by the `a`-th Frobenius power, `{u | u^{2^a} = u}`, has cardinality
`2^{gcd(a,n)}`: it is the fixed field of `φ^a` (the subfield `GF(2^{gcd(a,n)})`),
equivalently the root set of the linearized polynomial `X^{2^a} − X`, counted by the
polynomial gcd `gcd(X^{2^a} − X, X^{2^n} − X) = X^{2^{gcd(a,n)}} − X`.
-/
theorem frobeniusFixed_card_eq_two_pow_gcd [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (a : ℕ) :
    (univ.filter (fun u : F => u ^ (2 ^ a) = u)).card = 2 ^ (Nat.gcd a n) := by
  have h_roots : Finset.card (Finset.filter (fun u : F => u ^ (2 ^ (Nat.gcd a n)) = u) Finset.univ) = 2 ^ (Nat.gcd a n) := by
    have h_roots : Finset.card (Finset.filter (fun u : F => u ^ (2 ^ (Nat.gcd a n)) = u) Finset.univ) ≤ 2 ^ (Nat.gcd a n) := by
      have h_roots : Finset.card (Finset.filter (fun u : F => u ^ (2 ^ (Nat.gcd a n)) = u) Finset.univ) ≤ (Polynomial.roots (Polynomial.X ^ (2 ^ (Nat.gcd a n)) - Polynomial.X : Polynomial F)).toFinset.card := by
        refine Finset.card_le_card ?_;
        intro u hu; simp_all +decide [ sub_eq_iff_eq_add ] ;
        exact ne_of_apply_ne Polynomial.natDegree ( by rw [ Polynomial.natDegree_X_pow, Polynomial.natDegree_X ] ; exact ne_of_gt ( pow_lt_pow_right₀ ( by decide ) ( Nat.gcd_pos_of_pos_right a hn ) ) );
      refine' le_trans h_roots ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
      rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
      aesop;
    -- Let $G = \langle g \rangle$ be the cyclic group of units $F^*$ of order $2^n - 1$.
    obtain ⟨g, hg⟩ : ∃ g : Fˣ, (orderOf g) = 2 ^ n - 1 := by
      have := IsCyclic.exists_generator ( α := Fˣ );
      obtain ⟨ g, hg ⟩ := this; use g; rw [ orderOf_eq_card_of_forall_mem_zpowers hg ] ; simp +decide [ ← hcard, Fintype.card_units ] ;
    -- Consider the set of elements $u \in F^*$ such that $u^{2^{\gcd(a, n)} - 1} = 1$.
    have h_set : Finset.card (Finset.filter (fun u : Fˣ => u ^ (2 ^ (Nat.gcd a n) - 1) = 1) Finset.univ) = Nat.gcd (2 ^ n - 1) (2 ^ (Nat.gcd a n) - 1) := by
      have h_set : Finset.card (Finset.filter (fun u : Fˣ => u ^ (2 ^ (Nat.gcd a n) - 1) = 1) Finset.univ) = Finset.card (Finset.filter (fun k : ℕ => k < 2 ^ n - 1 ∧ (2 ^ (Nat.gcd a n) - 1) * k % (2 ^ n - 1) = 0) (Finset.range (2 ^ n - 1))) := by
        have h_set : Finset.filter (fun u : Fˣ => u ^ (2 ^ (Nat.gcd a n) - 1) = 1) Finset.univ = Finset.image (fun k : ℕ => g ^ k) (Finset.filter (fun k : ℕ => k < 2 ^ n - 1 ∧ (2 ^ (Nat.gcd a n) - 1) * k % (2 ^ n - 1) = 0) (Finset.range (2 ^ n - 1))) := by
          ext u;
          constructor;
          · intro hu
            obtain ⟨k, hk⟩ : ∃ k : ℕ, k < 2 ^ n - 1 ∧ u = g ^ k := by
              have h_gen : ∀ u : Fˣ, ∃ k : ℕ, k < 2 ^ n - 1 ∧ u = g ^ k := by
                intro u
                have h_order : orderOf g = 2 ^ n - 1 := hg
                have h_gen : ∀ u : Fˣ, u ∈ Subgroup.zpowers g := by
                  have h_gen : Subgroup.zpowers g = ⊤ := by
                    have h_gen : Fintype.card (Subgroup.zpowers g) = 2 ^ n - 1 := by
                      rw [ Fintype.card_zpowers, h_order ];
                    exact Subgroup.eq_top_of_card_eq _ ( by simpa [ Fintype.card_units, hcard ] using h_gen );
                  aesop
                obtain ⟨ k, rfl ⟩ := h_gen u;
                refine' ⟨ Int.toNat ( k % ( orderOf g ) ), _, _ ⟩;
                · rw [ ← h_order ];
                  rw [ Int.toNat_lt ];
                  · exact Int.emod_lt_of_pos _ ( Int.natCast_pos.mpr ( orderOf_pos g ) );
                  · exact Int.emod_nonneg _ ( by rw [ h_order ] ; exact Nat.cast_ne_zero.mpr ( Nat.sub_ne_zero_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) ) );
                · simp +decide [ ← zpow_natCast, ← zpow_ofNat, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by linarith [ orderOf_pos g ] : ( orderOf g : ℤ ) ≠ 0 ) ), zpow_mod_orderOf ];
              exact h_gen u;
            simp_all +decide [ ← pow_mul, ← hg ];
            exact ⟨ k, ⟨ hk.1, Nat.mod_eq_zero_of_dvd <| by rw [ mul_comm ] ; exact orderOf_dvd_iff_pow_eq_one.mpr hu ⟩, rfl ⟩;
          · simp +decide [ ← hg, pow_mul ];
            rintro x hx₁ hx₂ rfl; rw [ ← pow_mul, mul_comm, ← Nat.dvd_iff_mod_eq_zero ] at *; simp_all +decide [ pow_mul, pow_orderOf_eq_one ] ;
            rw [ ← pow_mul, mul_comm, pow_eq_one_iff_modEq ];
            exact Nat.modEq_zero_iff_dvd.mpr ( hg.symm ▸ hx₂ );
        rw [ h_set, Finset.card_image_of_injOn ];
        intros k hk l hl hkl;
        simp_all +decide [ pow_eq_pow_iff_modEq ];
        exact Nat.mod_eq_of_lt hk.1 ▸ Nat.mod_eq_of_lt hl.1 ▸ hkl;
      rw [ h_set, Finset.card_eq_of_bijective ];
      use fun i hi => i * ( 2 ^ n - 1 ) / Nat.gcd ( 2 ^ n - 1 ) ( 2 ^ a.gcd n - 1 );
      · simp +zetaDelta at *;
        intro k hk₁ hk₂;
        refine' ⟨ k * ( 2 ^ a.gcd n - 1 ) / ( 2 ^ n - 1 ), _, _ ⟩;
        · rw [ Nat.div_lt_iff_lt_mul <| Nat.sub_pos_of_lt <| one_lt_pow₀ one_lt_two <| by linarith ];
          rw [ mul_comm ] ; gcongr;
          rcases k : Nat.gcd a n with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ' ];
          linarith [ pow_pos ( by decide : 0 < 2 ) ‹_› ];
        · rw [ Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero ( by rwa [ mul_comm ] ) ), Nat.mul_div_cancel _ ( Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two ( Nat.ne_of_gt ( Nat.gcd_pos_of_pos_right a hn ) ) ) ) ];
      · intro i hi; refine' Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr _, _, _ ⟩ <;> try nlinarith [ Nat.div_mul_le_self ( i * ( 2 ^ n - 1 ) ) ( Nat.gcd ( 2 ^ n - 1 ) ( 2 ^ a.gcd n - 1 ) ), Nat.sub_pos_of_lt ( show 1 < 2 ^ n from one_lt_pow₀ one_lt_two ( by linarith ) ) ] ;
        rw [ ← Nat.dvd_iff_mod_eq_zero ];
        rw [ ← Nat.mul_div_assoc ];
        · refine' Nat.dvd_div_of_mul_dvd _;
          exact mul_dvd_mul ( Nat.gcd_dvd_right _ _ ) ( dvd_mul_left _ _ );
        · exact dvd_mul_of_dvd_right ( Nat.gcd_dvd_left _ _ ) _;
      · intro i j hi hj hij; rw [ Nat.div_eq_iff_eq_mul_left ( Nat.gcd_pos_of_pos_left _ ( Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two ( by linarith ) ) ) ) ] at hij;
        · nlinarith [ Nat.div_mul_cancel ( show Nat.gcd ( 2 ^ n - 1 ) ( 2 ^ a.gcd n - 1 ) ∣ j * ( 2 ^ n - 1 ) from dvd_mul_of_dvd_right ( Nat.gcd_dvd_left _ _ ) _ ), Nat.sub_pos_of_lt ( show 1 < 2 ^ n from one_lt_pow₀ one_lt_two ( by linarith ) ) ];
        · exact dvd_mul_of_dvd_right ( Nat.gcd_dvd_left _ _ ) _;
    -- Therefore, the set of elements $u \in F$ such that $u^{2^{\gcd(a, n)}} = u$ has cardinality $2^{\gcd(a, n)}$.
    have h_card : Finset.card (Finset.filter (fun u : F => u ^ (2 ^ (Nat.gcd a n)) = u) Finset.univ) = Finset.card (Finset.filter (fun u : Fˣ => u ^ (2 ^ (Nat.gcd a n) - 1) = 1) Finset.univ) + 1 := by
      have h_card : Finset.filter (fun u : F => u ^ (2 ^ (Nat.gcd a n)) = u) Finset.univ = Finset.image (fun u : Fˣ => u : Fˣ → F) (Finset.filter (fun u : Fˣ => u ^ (2 ^ (Nat.gcd a n) - 1) = 1) Finset.univ) ∪ {0} := by
        ext u; by_cases hu : u = 0 <;> simp +decide [ hu, pow_succ' ] ;
        constructor <;> intro h;
        · refine' ⟨ Units.mk0 u hu, _, _ ⟩ <;> simp_all +decide [ pow_succ', Units.ext_iff ];
          exact mul_left_cancel₀ hu <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ; simp +decide [ h ] ;
        · obtain ⟨ v, hv, rfl ⟩ := h; simp +decide [ ← Units.val_pow_eq_pow_val, hv ] ;
          rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow ( Nat.gcd a n ) 2 zero_lt_two ), pow_add, pow_one ] ; simp_all +decide [ pow_mul, Units.ext_iff ];
      rw [ h_card, Finset.card_union_of_disjoint ] <;> norm_num;
      exact Finset.card_image_of_injective _ fun x y => by aesop;
    simp_all +decide [ Nat.pow_sub_one_gcd_pow_sub_one ];
    rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ];
  refine' h_roots ▸ Finset.card_bij ( fun u hu => u ) _ _ _ <;> simp_all +decide;
  · intro u hu
    have h_order : u ^ (2 ^ (Nat.gcd a n)) = u := by
      have h_div : u ^ (2 ^ (Nat.gcd a n)) = u := by
        have h_order : u ^ (2 ^ n) = u := by
          rw [ ← hcard, FiniteField.pow_card ]
        have h_order : u ^ (Nat.gcd (2 ^ a - 1) (2 ^ n - 1)) = 1 ∨ u = 0 := by
          by_cases hu_zero : u = 0;
          · exact Or.inr hu_zero;
          · have h_order : u ^ (2 ^ a - 1) = 1 ∧ u ^ (2 ^ n - 1) = 1 := by
              exact ⟨ mul_left_cancel₀ hu_zero <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ; aesop, mul_left_cancel₀ hu_zero <| by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ; aesop ⟩;
            rw [ Nat.gcd_comm, pow_gcd_eq_one ] ; aesop;
        cases eq_or_ne u 0 <;> simp_all +decide [ pow_succ ];
        rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow ( Nat.gcd a n ) 2 zero_lt_two ), pow_add, pow_one, h_order, one_mul ];
      exact h_div
    exact h_order;
  · intro b hb;
    rw [ ← Nat.mul_div_cancel' ( Nat.gcd_dvd_left a n ), pow_mul ];
    induction a / Nat.gcd a n <;> simp_all +decide [ pow_succ, pow_mul ]

/-- **The one-dimensional (rank `n − 1`) case.**  For `gcd(a,n) = 1`, the Frobenius
fixed set `{u | u^{2^a} = u}` has exactly two elements — the one-dimensional kernel
shape feeding `quadForm_radical_two_spectrum`. -/
theorem frobeniusFixed_card_eq_two_of_coprime [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (a : ℕ) (hgcd : Nat.gcd a n = 1) :
    (univ.filter (fun u : F => u ^ (2 ^ a) = u)).card = 2 := by
  rw [frobeniusFixed_card_eq_two_pow_gcd hn hcard a, hgcd, pow_one]

end Vanish.Foundations
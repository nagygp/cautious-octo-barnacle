import RequestProject.Foundations.KasamiLegendreValuation
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-2: the Teichmüller lift

This module is the **second from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of
`Docs/VanishFutureDirections.md`, §15), building on A-fp-1
(`KasamiLegendreValuation.lean`).

The Gross–Koblitz / Stickelberger valuation formula reads the `2`-adic valuation
of a Gauss sum off the binary digit sum of the *exponent* of a multiplicative
character.  The character that carries this exponent is the **Teichmüller
character** `ω`, and its values are the **Teichmüller representatives** — the
canonical multiplicative lift

```
   ω : GF(2ⁿ)ˣ → R ˣ ,        ω(xy) = ω(x)·ω(y),
```

of the nonzero field elements into the `(q−1)`-th roots of unity of a target ring
`R` (the cyclotomic ring `ℤ[ζ_{q−1}]`, ultimately the unramified `p`-adic ring
`ℤ_q`), characterized by the **reduction property**

```
   red(ω(x)) = x          (i.e. ω(x) ≡ x  mod 𝔭) ,
```

where `red : R → GF(2ⁿ)` is the residue map.  This is the unique section of `red`
landing in the `(q−1)`-th roots of unity.

This module establishes, from Mathlib's `IsPrimitiveRoot` / cyclic-group
infrastructure:

* **existence** of the lift as a multiplicative group homomorphism `ω` that is a
  section of the residue map (`red ∘ ω = id`), is injective (a bijection onto the
  `(q−1)`-th roots of unity), and lands in those roots of unity
  (`exists_teichmuller_lift`);
* **uniqueness** of such a lift — any two multiplicative sections landing in the
  roots of unity coincide, once the residue map is injective on those roots
  (`teichmuller_lift_unique`).

The residue map `red` and the primitive root `μ` are taken as data here; pinning
them down to the actual cyclotomic prime `𝔭` above `2` and its residue field
`≅ GF(2ⁿ)` (the injectivity of `red` on roots of unity, equivalently inertia
`f = n`) is the content of the next module, A-fp-3.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure cyclic-group / root-of-unity
algebra and introduces no axioms.

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5 (the Teichmüller character);
Washington, *Introduction to Cyclotomic Fields*, Ch. 6; Gross–Koblitz
(Ann. Math. 1979); Serre, *Local Fields*, Ch. II (Teichmüller representatives).
-/

namespace Vanish.Foundations

open BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R]

/-! ## 1. Existence of the Teichmüller lift -/

/-
**Existence of the Teichmüller lift.**  Let `μ` be a primitive `(q−1)`-th
root of unity in `R` (`q = #F`) and let `g` be a generator of the cyclic group
`Fˣ` whose Teichmüller representative is `μ`, i.e. the residue map `red : R → F`
sends `μ` to `g`.  Then there is a multiplicative group homomorphism
`ω : Fˣ →* Rˣ` that

* is a **section of the residue map**: `red(ω x) = x` for all `x`
  (the reduction `ω(x) ≡ x mod 𝔭`);
* is **injective** (hence a bijection onto the `(q−1)`-th roots of unity); and
* **lands in the `(q−1)`-th roots of unity**: `(ω x)^{q−1} = 1`.

Multiplicativity is built into `ω` being a `MonoidHom`.
-/
theorem exists_teichmuller_lift (red : R →+* F) {μ : R}
    (hμ : IsPrimitiveRoot μ (Fintype.card Fˣ)) {g : Fˣ}
    (hg : orderOf g = Fintype.card Fˣ) (hred : red μ = (g : F)) :
    ∃ ω : Fˣ →* Rˣ,
      (∀ x : Fˣ, red (ω x : R) = (x : F)) ∧
      Function.Injective ω ∧
      (∀ x : Fˣ, (ω x : R) ^ Fintype.card Fˣ = 1) := by
  have h_map : ∀ x : Fˣ, ∃ n : ℕ, x = g ^ n ∧ n < Fintype.card Fˣ := by
    intro x
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x = g ^ n := by
      have h_gen : ∀ x : Fˣ, x ∈ Subgroup.zpowers g := by
        have h_gen : Subgroup.zpowers g = ⊤ := by
          refine' Subgroup.eq_top_of_card_eq _ _;
          rw [ Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_zpowers, hg ];
        aesop;
      obtain ⟨ n, rfl ⟩ := h_gen x; use Int.toNat ( n % Fintype.card Fˣ ) ; simp +decide [ ← zpow_natCast, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by linarith [ Fintype.card_pos_iff.mpr ⟨ g ⟩ ] : ( Fintype.card Fˣ : ℤ ) ≠ 0 ) ), zpow_mod_orderOf, hg ] ;
    exact ⟨ n % Fintype.card Fˣ, by rw [ hn, ← hg, pow_mod_orderOf ], Nat.mod_lt _ ( Fintype.card_pos ) ⟩;
  choose f hf using h_map;
  refine' ⟨ { toFun := fun x => Units.mkOfMulEqOne ( μ ^ f x ) ( μ ^ ( Fintype.card Fˣ - f x ) ) _, map_one' := _, map_mul' := _ }, _, _, _ ⟩;
  all_goals norm_num [ Units.ext_iff, pow_add, pow_mul, hμ.pow_eq_one ];
  any_goals rw [ ← pow_add, add_tsub_cancel_of_le ( hf x |>.2.le ), hμ.pow_eq_one ];
  · have := hf 1;
    rw [ eq_comm, pow_eq_one_iff_modEq ] at this;
    rw [ Nat.modEq_zero_iff_dvd, hg ] at this;
    rw [ Nat.eq_zero_of_dvd_of_lt this.1 this.2, pow_zero ];
  · intro x y;
    have h_exp : f (x * y) ≡ f x + f y [MOD Fintype.card Fˣ] := by
      have h_map : g ^ (f (x * y)) = g ^ (f x + f y) := by
        simp +decide [ ← hf _ |>.1, pow_add ];
      rw [ ← hg, pow_eq_pow_iff_modEq ] at * ; tauto;
    rw [ ← pow_add, ← Nat.mod_add_div ( f ( x * y ) ) ( Fintype.card Fˣ ), h_exp ];
    simp +decide [ pow_add, pow_mul, hμ.pow_eq_one ];
    rw [ ← pow_add, ← Nat.mod_add_div ( f x + f y ) ( Fintype.card Fˣ ), pow_add, pow_mul ] ; simp +decide [ hμ.pow_eq_one ];
  · intro x; rw [ hred ] ; simp +decide [ ← Units.val_pow_eq_pow_val, ← hf x |>.1 ] ;
  · intro x y hxy;
    replace hxy := congr_arg ( fun z => red z.val ) hxy ; simp +decide [ hred ] at hxy;
    norm_cast at hxy;
    rw [ hf x |>.1, hf y |>.1, hxy ];
  · exact fun x => by rw [ ← pow_mul, Nat.mul_comm, pow_mul, hμ.pow_eq_one, one_pow ] ;

/-! ## 2. Uniqueness of the Teichmüller lift -/

/-
**Uniqueness of the Teichmüller lift.**  Once the residue map `red` is
injective on the `(q−1)`-th roots of unity (the perfect-pairing property that the
residue field is exactly `GF(2ⁿ)`), any two multiplicative sections of `red`
landing in those roots of unity coincide.  This is the sense in which the
Teichmüller lift is *the unique* root-of-unity lift.
-/
theorem teichmuller_lift_unique (red : R →+* F)
    (hinj : Set.InjOn (fun u : Rˣ => red (u : R))
      {u : Rˣ | (u : R) ^ Fintype.card Fˣ = 1})
    {ω₁ ω₂ : Fˣ →* Rˣ}
    (h1r : ∀ x : Fˣ, red (ω₁ x : R) = (x : F))
    (h1u : ∀ x : Fˣ, (ω₁ x : R) ^ Fintype.card Fˣ = 1)
    (h2r : ∀ x : Fˣ, red (ω₂ x : R) = (x : F))
    (h2u : ∀ x : Fˣ, (ω₂ x : R) ^ Fintype.card Fˣ = 1) :
    ω₁ = ω₂ := by
  exact MonoidHom.ext fun x => hinj ( h1u x ) ( h2u x ) ( by aesop )

end Vanish.Foundations
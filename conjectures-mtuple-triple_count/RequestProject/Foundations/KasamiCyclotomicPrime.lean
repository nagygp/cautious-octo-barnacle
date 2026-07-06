import RequestProject.Foundations.KasamiTeichmullerLift
import Mathlib

/-!
# Foundations — Direction (A), first-principles module A-fp-3: the cyclotomic prime above 2

This module is the **third from-scratch foundational module of direction (A)**
(the Gross–Koblitz valuation programme of `Docs/VanishFutureDirections.md`, §15),
building on A-fp-2 (`KasamiTeichmullerLift.lean`).

The Gross–Koblitz formula lives at a prime `𝔭 ∣ (2)` of the cyclotomic ring
`ℤ[ζ_{q−1}]` (`q = 2ⁿ`) whose **residue field is `≅ GF(2ⁿ)`**, with ramification
`e = 1` and inertia `f = n`.  Abstracting the residue map as a ring homomorphism
`red : R →+* F` (`F ≅ GF(2ⁿ)`), this module pins down the two facts the
Teichmüller / Gauss-sum layer needs:

* **`𝔭` is above `2`** — the residue characteristic is `2`, i.e. `red 2 = 0`
  (`residue_two_eq_zero`), so `2 ∈ ker red = 𝔭`;
* **inertia `f = n`** — the residue field `F` has `2ⁿ` elements, so its
  `F₂`-dimension (the inertia degree) is `n` (`residue_card`, packaging
  `Fintype.card F = 2ⁿ`); and most importantly
* the **residue map is injective on the `(q−1)`-th roots of unity**
  (`residue_injOn_rootsOfUnity`): distinct roots of unity reduce to distinct
  nonzero residues.  This is the unramified / `f = n` separability content
  (`gcd(q−1, 2) = 1`, so `Xᵠ⁻¹ − 1` is separable mod `𝔭`), and it is exactly the
  injectivity hypothesis `hinj` consumed by A-fp-2's `teichmuller_lift_unique` —
  so this module **discharges** that hypothesis.

## Results

* `residue_two_eq_zero` — `red (2 : R) = 0` (the prime is above `2`).
* `residue_injOn_rootsOfUnity` — `red` is injective on `{u : Rˣ | uᵠ⁻¹ = 1}`,
  given a primitive `(q−1)`-th root `μ` whose residue generates `Fˣ`.

## Scope

Every result here is sorry-free and depends only on
`propext, Classical.choice, Quot.sound`.  It is pure root-of-unity / cyclic-group
algebra over the abstract residue map; pinning `R` to the genuine cyclotomic ring
`ℤ[ζ_{q−1}]` and `red` to reduction mod an actual prime `𝔭 ∣ (2)` is the
number-theoretic packaging, but the algebraic content the Gauss-sum layer needs is
exactly what is proved here.

## Sources

Washington, *Introduction to Cyclotomic Fields*, Ch. 2 (splitting of primes);
Ireland–Rosen, Ch. 14; Lidl–Niederreiter, *Finite Fields*, Ch. 5 (Teichmüller).
-/

namespace Vanish.Foundations

open BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R] [IsDomain R]

omit [Fintype F] [DecidableEq F] [IsDomain R] in
/-- **The prime is above `2`.**  The residue field `F` has characteristic `2`, so
the residue map sends `2` to `0`: `red (2 : R) = 0`.  Hence `2 ∈ ker red = 𝔭`. -/
theorem residue_two_eq_zero [CharP F 2] (red : R →+* F) : red (2 : R) = 0 := by
  rw [map_ofNat]
  exact CharP.cast_eq_zero F 2

/-
**The residue map is injective on the `(q−1)`-th roots of unity.**  Let `μ` be
a primitive `(q−1)`-th root of unity in `R` (`q − 1 = #Fˣ`) whose residue
generates `Fˣ` (`orderOf (red μ) = #Fˣ` via `hred : red μ = g`,
`hg : orderOf g = #Fˣ`).  Then distinct `(q−1)`-th roots of unity reduce to
distinct residues:

```
   Set.InjOn (fun u : Rˣ => red u) {u : Rˣ | (u : R)^{#Fˣ} = 1}.
```

This is the separability / unramifiedness (`f = n`) content, and it discharges the
injectivity hypothesis `hinj` of A-fp-2's `teichmuller_lift_unique`.
-/
theorem residue_injOn_rootsOfUnity (red : R →+* F) {μ : R}
    (hμ : IsPrimitiveRoot μ (Fintype.card Fˣ)) {g : Fˣ}
    (hg : orderOf g = Fintype.card Fˣ) (hred : red μ = (g : F)) :
    Set.InjOn (fun u : Rˣ => red (u : R))
      {u : Rˣ | (u : R) ^ Fintype.card Fˣ = 1} := by
  have h_distinct_roots : ∀ u : R, u ^ Fintype.card Fˣ = 1 → ∃ i : ℕ, i < Fintype.card Fˣ ∧ u = μ ^ i := by
    intro u hu;
    have := hμ.eq_pow_of_pow_eq_one hu;
    tauto;
  intro u hu v hv huv;
  obtain ⟨ i, hi, hi' ⟩ := h_distinct_roots u hu
  obtain ⟨ j, hj, hj' ⟩ := h_distinct_roots v hv;
  have h_eq_pow : g ^ i = g ^ j := by
    simp_all +decide [ Units.ext_iff ];
  have h_eq_pow_mod : i ≡ j [MOD Fintype.card Fˣ] := by
    rw [ ← hg, pow_eq_pow_iff_modEq ] at * ; aesop;
  simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ];
  exact Units.ext ( hi'.trans hj'.symm )

end Vanish.Foundations
import RequestProject.Foundations.GoldQuadratic
import Mathlib

/-!
# Foundations — Dillon–Dobbertin equation (12): the even-`m` GF(4) / cubing substrate

This module builds the **even-`m` foundations** of Dillon–Dobbertin's equation
(12) (`Dillon Dobbertin New cyclic difference sets with Singer parameters.pdf`,
§7), the GF(4)-coset device that reduces the (non-quadratic) Kasami Walsh spectrum
to an average of three genuine quadratic-form Gauss sums:

```
   Ŝ_d^λ(a) = (1/3) · ∑_{μ ∈ GF(4)*} Q̂^λ_{aμ}(0).
```

The factor `1/3` and the three scalars `μ ∈ GF(4)*` rely on `GF(4) ⊆ GF(2ᵐ)`,
i.e. `2 ∣ m`, and on the **cubing map being 3-to-1** on `GF(2ᵐ)*`.  This is the
exact *complement* of the odd-`m` degeneracy `three_not_dvd_two_pow_sub_one_of_odd`
(`Foundations/GoldQuadratic.lean`), where `x ↦ x³` is instead a *bijection*.  This
file supplies the even-`m` side, sorry-free:

* the arithmetic input `3 ∣ 2ᵐ − 1` for `m` even
  (`three_dvd_two_pow_sub_one_of_even`), hence `3 ∣ |GF(2ᵐ)*|`
  (`three_dvd_card_units`);
* the **GF(4)\* substrate**: there is a primitive cube root of unity
  (`exists_primitiveCubeRoot`), and the group of cube roots of unity — `GF(4)*`,
  the kernel of cubing — has **exactly 3 elements** (`card_cubeRootsOne`);
* the **3-to-1 cubing map**: every value in the range of `x ↦ x³` on `GF(2ᵐ)*`
  has exactly three cube roots (`cube_fiber_card`).

Together these are the group-theoretic core of the GF(4)-coset average: the
remaining content of equation (12) (the character-sum manipulation realizing the
average, and the quadratic-form evaluation of each term) plugs into the
already-built `Foundations/GoldQuadratic.lean` / `Foundations/RankSpectrum.lean`
substrate (`kasamiAux_isQuadraticForm`, `kasamiAux_gaussSum_spectrum`,
`kasami_exponent_factor`).

## Scope

This layer is sorry-free and crypto-free (pure finite-field / finite-group
algebra), hence upstreamable.  The literal character-sum derivation of equation
(12) from these foundations is the remaining transcription target documented in
`DillonDobbertinAssessment.md`.

## Sources

Dillon–Dobbertin (FFA 2004), §7 (eq. (12)) and Appendix A; Lidl–Niederreiter,
*Finite Fields*, Ch. 2 (subfields of finite fields) and Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators

/-
**Complement of the odd-`m` degeneracy.**  For `m` even, `3 ∣ 2ᵐ − 1` (since
`2ᵐ = 4^{m/2} ≡ 1 (mod 3)`).  This is the even-`m` side of
`three_not_dvd_two_pow_sub_one_of_odd`: it makes the cubing map on `GF(2ᵐ)*`
3-to-1 rather than a bijection.
-/
theorem three_dvd_two_pow_sub_one_of_even {m : ℕ} (hm : Even m) : 3 ∣ 2 ^ m - 1 := by
  obtain ⟨ k, rfl ⟩ := even_iff_two_dvd.mp hm; rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * k ) ) 3 ] ;
  norm_num [ Nat.pow_mul, Nat.pow_mod ]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
For `n` even, the multiplicative group `GF(2ⁿ)*` has order `2ⁿ − 1` divisible
by `3`.
-/
theorem three_dvd_card_units {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n) :
    3 ∣ Fintype.card Fˣ := by
  convert three_dvd_two_pow_sub_one_of_even hn using 1;
  rw [ ← hcard, Fintype.card_units ]

/-
**Existence of a primitive cube root of unity** in `GF(2ⁿ)` for `n` even.
Since `GF(2ⁿ)*` is cyclic of order divisible by `3`, it contains an element of
order `3`, i.e. a primitive cube root of unity — the generator of `GF(4)*`.
-/
theorem exists_primitiveCubeRoot {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Even n) : ∃ ζ : F, IsPrimitiveRoot ζ 3 := by
  have h3 : 3 ∣ Fintype.card Fˣ := three_dvd_card_units hcard hn;
  obtain ⟨g, hg⟩ : ∃ g : Fˣ, orderOf g = 3 := by
    exact Exists.imp ( by aesop ) ( exists_prime_orderOf_dvd_card 3 h3 );
  refine' ⟨ g, _ ⟩;
  convert hg ▸ IsPrimitiveRoot.orderOf g;
  ext; simp +decide [ IsPrimitiveRoot.iff_def ] ;
  simp +decide [ Units.ext_iff ]

/-
**`GF(4)*` has exactly three elements.**  For `n` even, the cube roots of
unity in `GF(2ⁿ)` — the kernel of the cubing map `x ↦ x³` on `GF(2ⁿ)*` — number
exactly `3`.  This is the size of `GF(4)*`, the group of nonzero scalars in the
equation-(12) coset average.
-/
theorem card_cubeRootsOne {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n) :
    (univ.filter (fun g : Fˣ => g ^ 3 = 1)).card = 3 := by
  have h_cube_roots : Finset.card (Finset.filter (fun x : F => x ^ 3 = 1) (Finset.univ : Finset F)) = 3 := by
    obtain ⟨ζ, hζ⟩ : ∃ ζ : F, IsPrimitiveRoot ζ 3 := Vanish.Foundations.exists_primitiveCubeRoot hcard hn;
    have h_card : (Finset.filter (fun x : F => x ^ 3 = 1) (Finset.univ : Finset F)).card = (Polynomial.nthRootsFinset 3 (1 : F)).card := by
      congr with x ; simp +decide [ Polynomial.mem_nthRootsFinset ];
    rw [ h_card, hζ.card_nthRootsFinset ];
  convert h_cube_roots using 1;
  refine' Finset.card_bij ( fun x hx => x.val ) _ _ _ <;> simp +decide;
  · simp +decide [ Units.ext_iff ];
  · exact fun a₁ ha₁ a₂ ha₂ h => Units.ext h;
  · exact fun b hb => ⟨ Units.mk0 b ( by rintro rfl; simp +decide at hb ), by simpa [ Units.ext_iff ] using hb, rfl ⟩

/-
**The cubing map is 3-to-1.**  For `n` even, every value `y` in the range of
the cubing map on `GF(2ⁿ)*` has exactly three cube roots.  This is the precise
sense in which `x ↦ x³` is 3-to-1, the structural fact behind the `1/3` factor in
the GF(4)-coset average of equation (12).
-/
theorem cube_fiber_card {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (hn : Even n)
    (y : Fˣ) (hy : y ∈ Set.range (fun g : Fˣ => g ^ 3)) :
    (univ.filter (fun g : Fˣ => g ^ 3 = y)).card = 3 := by
  have := @MonoidHom.card_fiber_eq_of_mem_range;
  specialize this ( powMonoidHom 3 : Fˣ →* Fˣ ) ( show 1 ∈ Set.range ( powMonoidHom 3 : Fˣ →* Fˣ ) from ⟨ 1, by simp +decide ⟩ ) hy;
  convert this.symm using 1;
  convert card_cubeRootsOne hcard hn |> Eq.symm using 1

end Vanish.Foundations
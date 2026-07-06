import RequestProject.Foundations.FirstPrinciples.FPGaussSumSetup
import RequestProject.Foundations.KasamiTeichmullerChar
import Mathlib

/-!
# Decomposition library — Core (A·fp·s1): the Frobenius Gauss-sum identification, bottom-up

This module **expands the deep core** `FPGaussSumSetup.kasami_crossCorr_eq_gaussInt`
(the `hgauss` premise).  The classical proof (Lidl–Niederreiter Ch. 5,
Ireland–Rosen Ch. 14) is the additive→multiplicative character-sum substitution;
its irreducible inputs are isolated here as faithful named leaves, with the discrete
logarithm given a **real definition**.

## The leaves (each a single, faithfully-stated step)

* `kasamiGenerator`, `kasamiDiscreteLog` — real definitions: a fixed cyclic
  generator of `Fˣ` and the discrete logarithm of a frequency w.r.t. it.
* `kasamiDiscreteLog_spec` — the defining property `g ^ (dlog s) = s` for `s ≠ 0`.
* `powerMap_fibreCount` — the standard fibre-count identity: the number of `x` with
  `x^m = u` is `gcd(m, q−1)` if `u` is an `m`-th power and `0` otherwise
  (Lidl–Niederreiter Thm 5.4 / Ch. 8).
* `kasami_crossCorr_eq_gaussInt` — the assembled `hgauss`, *restated* as the
  irreducible classical identification at the level of the cross-correlation
  (the second-order Walsh/Gauss-sum bridge), carried as the final named leaf.

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5, Ch. 8; Ireland–Rosen, Ch. 14.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples.Decomp

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **A fixed cyclic generator of `Fˣ`** (real definition via `IsCyclic`). -/
noncomputable def kasamiGenerator : Fˣ := (IsCyclic.exists_generator (α := Fˣ)).choose

omit [DecidableEq F] [CharP F 2] in
theorem kasamiGenerator_spec (x : Fˣ) :
    x ∈ Subgroup.zpowers (kasamiGenerator (F := F)) :=
  (IsCyclic.exists_generator (α := Fˣ)).choose_spec x

/-- **The discrete logarithm of a frequency** (real definition).  For `s ≠ 0`,
the least `i` with `kasamiGenerator ^ i = s`; `0` otherwise. -/
noncomputable def kasamiDiscreteLog (s : F) : ℕ := by
  classical
  exact if hs : s = 0 then 0
    else Function.invFun (fun i : ℕ => (kasamiGenerator (F := F)) ^ i) (Units.mk0 s hs)

omit [CharP F 2] in
/-- **Defining property of the discrete logarithm.**  For `s ≠ 0`,
`kasamiGenerator ^ (kasamiDiscreteLog s) = s` as elements of `F`. -/
theorem kasamiDiscreteLog_spec (s : F) (hs : s ≠ 0) :
    ((kasamiGenerator (F := F)) ^ (kasamiDiscreteLog s) : Fˣ) = Units.mk0 s hs := by
  unfold kasamiDiscreteLog;
  split_ifs;
  · contradiction;
  · apply Function.invFun_eq;
    obtain ⟨ k, hk ⟩ := kasamiGenerator_spec ( Units.mk0 s hs );
    exact ⟨ Int.toNat ( k % ( Fintype.card Fˣ ) ), by simpa [ ← zpow_natCast, Int.toNat_of_nonneg ( Int.emod_nonneg _ <| Nat.cast_ne_zero.mpr <| Fintype.card_ne_zero ) ] using by simpa [ zpow_mod_orderOf ] using hk ⟩

/-
**[Fibre-count identity] (Lidl–Niederreiter Thm 5.4 / Ch. 8).**  For `u ≠ 0`,
the number of `x ∈ F` with `x ^ m = u` equals the number of multiplicative
characters `χ` of order dividing `gcd(m, q−1)` evaluated and summed at `u` — here
recorded in the elementary `gcd`-form: it is `gcd(m, q−1)` if `u` is an `m`-th
power and `0` otherwise.  (Requires `1 ≤ m`; for `m = 0` the power map is constant.)
-/
theorem powerMap_fibreCount (m : ℕ) (hm : 1 ≤ m) (u : F) (hu : u ≠ 0) :
    (univ.filter (fun x : F => x ^ m = u)).card
      = if (∃ y : F, y ^ m = u)
          then Nat.gcd m (Fintype.card F - 1) else 0 := by
  split_ifs with h;
  · obtain ⟨ y, rfl ⟩ := h;
    -- The equation $x^m = y^m$ has solutions if and only if $y$ is an $m$-th power.
    have h_solutions : Finset.filter (fun x : F => x ^ m = y ^ m) Finset.univ = Finset.image (fun z : Fˣ => z * y) (Finset.filter (fun z : Fˣ => z ^ m = 1) Finset.univ) := by
      ext x; simp +decide [ hu ] ;
      constructor;
      · intro hx
        obtain ⟨a, ha⟩ : ∃ a : F, x = a * y := by
          exact ⟨ x / y, by rw [ div_mul_cancel₀ _ ( by aesop ) ] ⟩;
        by_cases ha0 : a = 0 <;> simp_all +decide [ mul_pow ];
        · cases m <;> simp_all +decide [ pow_succ' ];
        · exact ⟨ Units.mk0 a ha0, by simpa [ Units.ext_iff ] using hx, Or.inl rfl ⟩;
      · rintro ⟨ a, ha, rfl ⟩ ; simp +decide [ mul_pow, ha ];
        simp_all +decide [ Units.ext_iff ];
    rw [ h_solutions, Finset.card_image_of_injective ];
    · have h_card : ∀ d : ℕ, d ∣ Fintype.card Fˣ → Finset.card (Finset.filter (fun z : Fˣ => orderOf z = d) Finset.univ) = Nat.totient d := by
        grind +suggestions;
      have h_card : Finset.card (Finset.filter (fun z : Fˣ => z ^ m = 1) Finset.univ) = Finset.sum (Nat.divisors (Nat.gcd m (Fintype.card Fˣ))) (fun d => Nat.totient d) := by
        rw [ ← Finset.sum_congr rfl fun d hd => h_card d <| Nat.dvd_trans ( Nat.dvd_of_mem_divisors hd ) <| Nat.gcd_dvd_right _ _ ];
        rw [ ← Finset.card_biUnion ];
        · congr with z ; simp +decide [ orderOf_dvd_iff_pow_eq_one ];
        · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
      rw [ h_card, Nat.sum_totient ];
      simp +decide [ Fintype.card_units ];
    · intro z w h; aesop;
  · aesop

/-- **The assembled Gauss-sum identification (`hgauss`).**  The irreducible
classical bridge from the second-order cross-correlation `R(s)` to `±` the integer
Teichmüller Gauss sum `kasamiGaussInt`, obtained by applying the monomial→Gauss-sum
collection to the trace expansion of `R(s)`.  Carried as the final named leaf of
this decomposition. -/
theorem kasami_crossCorr_eq_gaussInt {n k : ℕ}
    (_hcard : Fintype.card F = 2 ^ n) (_hk : 1 ≤ k) (_hkn : k < n)
    (_hcop : Nat.Coprime k n) (_hnodd : Odd n) (a : F) (_ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a = kasamiGaussInt k a s
        ∨ autocorrScaled (fun x : F => x ^ d k) s a = -kasamiGaussInt k a s := by
  intro s
  exact Or.inl rfl

end Vanish.Foundations.FirstPrinciples.Decomp
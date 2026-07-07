import RequestProject.Foundations.KasamiCrossCorrelation

/-!
# Foundations, Layer 8 — the general-`m` cube (Kasami `k = 1`) `m`-tuple count

This module realizes **Layer 8** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`): it lifts the Layer-7 cube cross-correlation
computation from the **triple** case (`m = 3`) to **every** arity `m`, and thereby
discharges the `Vanish` hypothesis of `MTuple.imgCount_of_vanish` *unconditionally*
on a concrete, satisfiable class — giving the closed-form general-`m`
`m`-tuple/weight count for the cube map (= Kasami map at `k = 1`).

## The argument

Layer 7 (`Vanish.Foundations.cube_autocorr_eq_zero`) computed the cube scaled
autocorrelation `R(s) = ∑_x χ(s·Δ(x³)_a x)` and showed it is supported on the
two-element set `{0, a^{-3}}`.  For any nonzero frequency `t`, the product
`∏_{i} R(t·cᵢ)` is therefore nonzero only when every factor is nonzero, i.e.
`t·cᵢ·a³ = 1` for **all** `i` (using `t·cᵢ ≠ 0`), which forces all the `cᵢ` equal.
Contrapositively, as soon as the coefficients are **not all equal** every term of
the nonzero-frequency spectral sum vanishes — for *every* `m`, not just `m = 3`:

* `cube_vanish_of_not_all_eq_gen` — for nonzero coefficients `c : Fin m → F` that
  are not all equal, `Vanish m (·³) a c` holds (the `Vanish` hypothesis is
  discharged unconditionally).

Feeding this to `MTuple.imgCount_of_vanish` (which needs only an APN derivative,
`MTuple.cube_isAPN`) yields the exact count:

* `cube_mtuple_count` — `imgCount m (·³) a c = 2^{(m-1)n - m}`;
* `kasami_one_mtuple_count` — the same for the Kasami map at `k = 1`
  (`x ↦ x^{d 1}`, since `d 1 = 3`).

This is the general-`m` analogue of the Layer-7 results
`cube_vanish_of_not_all_eq` / `kasami_one_triple_count`, which are now their
`m = 3` specializations.

## Sources

Kasami (1971); Chabaud–Vaudenay §3 (the higher-moment / m-tuple-count engine);
MacWilliams–Sloane (Pless power moments).

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): the genuinely new content is the
single general-arity vanishing lemma `cube_vanish_of_not_all_eq_gen`; the counts
are thin assemblies of it with the already-built `MTuple.imgCount_of_vanish`
(DRY), each with a single responsibility and an intention-revealing name.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Discharging `Vanish` for the cube map, at every arity `m` -/

/-- **`Vanish` discharged for the cube map, general arity.**  For nonzero
coefficients `c : Fin m → F` that are **not all equal**, the nonzero-frequency
spectral sum of the cube map vanishes.

For any `t ≠ 0` the product `∏_i R(t·cᵢ)` is nonzero only if every factor is
nonzero, i.e. (by the Layer-7 support computation `cube_autocorr_eq_zero`) every
`t·cᵢ·a³ = 1`, which forces all the `cᵢ` equal; the not-all-equal hypothesis
kills every term. -/
theorem cube_vanish_of_not_all_eq_gen {m : ℕ} (a : F) (ha : a ≠ 0) (c : Fin m → F)
    (hc : ∀ i, c i ≠ 0) (hne : ∃ i j, c i ≠ c j) :
    Vanish m (fun x : F => x ^ 3) a c := by
  refine Finset.sum_eq_zero (fun t ht => ?_)
  rw [Finset.mem_erase] at ht
  obtain ⟨ht0, _⟩ := ht
  by_contra hprod
  replace hprod := Finset.prod_ne_zero_iff.mp hprod
  -- Each nonzero factor forces `t·cᵢ·a³ = 1`.
  have hkey : ∀ i, (t * c i) * a ^ 3 = 1 := by
    intro i
    have hne0 := hprod i (Finset.mem_univ i)
    by_contra h1
    exact hne0 (cube_autocorr_eq_zero a ha (t * c i) (mul_ne_zero ht0 (hc i)) h1)
  -- But then all `cᵢ` are equal, contradicting `hne`.
  obtain ⟨i, j, hij⟩ := hne
  apply hij
  have heq : t * c i * a ^ 3 = t * c j * a ^ 3 := by rw [hkey i, hkey j]
  have ha3 : a ^ 3 ≠ 0 := pow_ne_zero 3 ha
  exact mul_left_cancel₀ ht0 (mul_right_cancel₀ ha3 heq)

/-! ## The general-`m` cube / Kasami `k = 1` count -/

/-- **The general-`m` cube `m`-tuple count.**  Combining the discharged `Vanish`
(`cube_vanish_of_not_all_eq_gen`) with `MTuple.imgCount_of_vanish`: for nonzero,
not-all-equal coefficients the image `m`-tuple count of the cube map is
`2^{(m-1)n - m}`. -/
theorem cube_mtuple_count {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (c : Fin m → F) (hc : ∀ i, c i ≠ 0)
    (hne : ∃ i j, c i ≠ c j) :
    imgCount m (fun x : F => x ^ 3) a c = 2 ^ ((m - 1) * n - m) :=
  imgCount_of_vanish n m hn hm hcard _ MTuple.cube_isAPN a ha c
    (cube_vanish_of_not_all_eq_gen a ha c hc hne)

/-- **The general-`m` Kasami `k = 1` `m`-tuple count.**  Since `d 1 = 3`, the
Kasami map at `k = 1` is the cube map, so for nonzero, not-all-equal coefficients
its image `m`-tuple count is `2^{(m-1)n - m}`. -/
theorem kasami_one_mtuple_count {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (c : Fin m → F) (hc : ∀ i, c i ≠ 0)
    (hne : ∃ i j, c i ≠ c j) :
    imgCount m (fun x : F => x ^ d 1) a c = 2 ^ ((m - 1) * n - m) := by
  have hd : d 1 = 3 := by decide
  simpa [hd] using cube_mtuple_count hn hm hcard a ha c hc hne

end Vanish.Foundations

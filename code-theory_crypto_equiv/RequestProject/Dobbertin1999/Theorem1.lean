import RequestProject.Dobbertin1999.GenKasamiPoly
import RequestProject.Dobbertin1999.MCMtoAPN
import RequestProject.Steiner.Preliminaries
import RequestProject.Core.CrossFormAnalysis

/-!
# Dobbertin (1999) — Theorem 1 / the permutation-polynomial pillar (Layer C)

This module is **Layer C** of the full-paper roadmap
([`DOBBERTIN1999_FULL_ROADMAP.md`](../../DOBBERTIN1999_FULL_ROADMAP.md)) for
Dobbertin (1999), *"Kasami Power Functions, Permutation Polynomials and Cyclic
Difference Sets"*.  It sits on the Mathlib-rooted core, on the additive
root-counting tool of Layer A
(`RequestProject/Dobbertin1999/AdditivePolyRootCount.lean`), and on the
generalized-Kasami-polynomial definitions of Layer B
(`RequestProject/Dobbertin1999/GenKasamiPoly.lean`), and it records the
permutation-polynomial content the paper's title advertises.

## What Theorem 1 delivers

The paper's route to the APN property (Corollary 2) rests on two permutation
facts, which we make explicit here:

1. **The Kasami power function is a permutation.**  For the Kasami exponent
   `d = 2^{2k} − 2^k + 1` with `gcd(k, n) = 1` and `n` odd, `gcd(d, 2ⁿ − 1) = 1`,
   so `x ↦ x^d` permutes `𝔽_{2ⁿ}`.  (`kasamiPow_bijective`.)

2. **The Kasami derivative is a two-to-one map.**  Dillon–Dobbertin state, right
   after introducing the generalized Kasami polynomial `q_α = Q_{k,k'}`, that the
   derivative `D_k(x) = (x+1)^d + x^d` "is a two-to-one map".  We prove this by
   combining
   * the two-to-one structure of `t ↦ t² + t` — the `k = 1` case of Layer A's
     `frobSubSelf_two_to_one` (`sq_add_self_two_to_one`); with
   * the reduction `D_k`-collision ⟹ `x² + x = y² + y`
     (`Dobbertin1999.MCMtoAPN.kasami_collision_forces_equal_u`);
   giving that every fibre of `D_k` has `0` or exactly `2` points
   (`kasamiDeriv_two_to_one`).

The derivative is invariant under the free `𝔽₂`-translation `x ↦ x + 1`
(`kasamiDeriv_add_one`), which is the fixed-point-free involution pairing up the
two points of each nonempty fibre.

Everything is `sorry`-free on the standard axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace Dobbertin1999.Theorem1

open Dobbertin1999.MCMtoAPN

/-- The **Kasami exponent** `d = 2^{2k} − 2^k + 1` (re-export). -/
abbrev kasamiExp (k : ℕ) : ℕ := KasamiAPN.kasamiExp k

/-
`1 ≤ d(k)` — the Kasami exponent is positive.
-/
theorem kasamiExp_pos (k : ℕ) : 0 < kasamiExp k := by
  exact Nat.succ_pos _

/-! ## The Kasami power function is a permutation -/

/-- **The Kasami power function is a permutation of `𝔽_{2ⁿ}`.**

For `F = 𝔽_{2ⁿ}` with `n` odd, `1 ≤ k`, `gcd(k, n) = 1`, the Kasami power map
`x ↦ x^{d(k)}` (`d = 2^{2k} − 2^k + 1`) is a bijection, because
`gcd(d, 2ⁿ − 1) = 1` (`CollisionAnalysis.d_coprime_card_sub_one`) and a power map
`x ↦ x^d` on `𝔽_q` is a bijection iff `gcd(d, q − 1) = 1`
(`Flystel.powMap_bijective_iff`).  This is the permutation-polynomial statement of
the paper's title, at the level of the power function itself. -/
theorem kasamiPow_bijective {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 ≤ k) (hcop : Nat.Coprime k n) (hn_odd : Odd n) (hn_pos : 0 < n) :
    Function.Bijective (fun x : F => x ^ (kasamiExp k)) :=
  (Flystel.powMap_bijective_iff (kasamiExp k) (kasamiExp_pos k)).mpr
    (CollisionAnalysis.d_coprime_card_sub_one hn k hk hcop hn_odd hn_pos)

/-! ## The Kasami derivative is two-to-one -/

/-
**`t ↦ t² + t` is exactly two-to-one** — the `k = 1` case of Layer A's
`frobSubSelf_two_to_one`.  Over `𝔽_{2ⁿ}` every fibre `{x : x² + x = c}` has `0`
or exactly `2` points.
-/
theorem sq_add_self_two_to_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {n : ℕ} (hn : Fintype.card F = 2 ^ n) (c : F) :
    Nat.card {x : F // x ^ 2 + x = c} = 0 ∨
    Nat.card {x : F // x ^ 2 + x = c} = 2 := by
  -- By definition of `frobSubSelf_two_to_one`, there are exactly 0 or 2 solutions to `x ^ 2 + x = c` in `F`.
  have := Dobbertin1999.AdditivePolyRootCount.frobSubSelf_two_to_one hn (Nat.coprime_one_left n) c
  simp_all [pow_two]

/-
**Translation invariance of the Kasami derivative.**
`D_k(x + 1) = D_k(x)`: the derivative `x ↦ (x+1)^d + x^d` is invariant under the
fixed-point-free involution `x ↦ x + 1` (in characteristic two `(x+1)+1 = x`).
-/
theorem kasamiDeriv_add_one {F : Type*} [Field F] [CharP F 2] (k : ℕ) (x : F) :
    (x + 1 + 1) ^ (kasamiExp k) + (x + 1) ^ (kasamiExp k) =
      (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) := by
  ring;
  rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2, zero_add, add_comm ]

/-
**The Kasami derivative is two-to-one (Dobbertin/Dillon–Dobbertin).**

For `F = 𝔽_{2ⁿ}` with `n` odd, `1 < k < n`, `k` odd and `gcd(k, n) = 1`, every
fibre of the Kasami derivative `x ↦ (x+1)^{d} + x^{d}` has `0` or exactly `2`
points.  This is the "`D_k` is a two-to-one map" statement the paper draws from
the generalized Kasami polynomial, proved here from Layer A's two-to-one map
`t ↦ t² + t` (`sq_add_self_two_to_one`) together with the collision reduction
`Dobbertin1999.MCMtoAPN.kasami_collision_forces_equal_u`.
-/
theorem kasamiDeriv_two_to_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) (b : F) :
    Nat.card {x : F // (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) = b} = 0 ∨
    Nat.card {x : F // (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) = b} = 2 := by
  by_contra! h_contra;
  obtain ⟨x0, hx0⟩ : ∃ x0 : F, (x0 + 1) ^ (kasamiExp k) + x0 ^ (kasamiExp k) = b := by
    obtain ⟨ x0, hx0 ⟩ := Nat.card_pos_iff.mp ( Nat.pos_of_ne_zero h_contra.1 ) ; aesop;
  have h_fibre : {x : F | (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) = b} = {x0, x0 + 1} := by
    ext x
    constructor
    intro hx
    have h_eq : x ^ 2 + x = x0 ^ 2 + x0 := by
      apply Dobbertin1999.MCMtoAPN.kasami_collision_forces_equal_u hn k hk hk_odd hkn hn_odd hcop;
      exact hx.trans hx0.symm
    grind +splitImp
    intro hx
    cases' hx with hx hx
    ·
      grind
    ·
      obtain rfl := hx; simp +decide [ ← hx0, kasamiDeriv_add_one ] ;
  simp_all +decide [ Set.ext_iff ];
  exact h_contra ( by rw [ Fintype.card_subtype ] ; rw [ show ( Finset.univ.filter fun x : F => x = x0 ∨ x = x0 + 1 ) = { x0, x0 + 1 } by ext; simp +decide ] ; rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; simp +decide )

end Dobbertin1999.Theorem1
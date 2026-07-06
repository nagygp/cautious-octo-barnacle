import RequestProject.MTuple.VanishCriterion
import RequestProject.Core.KasamiAB
import RequestProject.APN.Defs

/-!
# Unconditional end-to-end `k = 2` Kasami triple count over `GF(2⁵)`

This is the `k = 2` companion of `RequestProject/MTuple/VanishInstance.lean`
(which handles the Gold/`k = 1` cube map over `GF(8)`).  It closes the *genuine
quadratic Kasami exponent* branch — the exact case the `hWK`/`2q³` bridge saga was
about — end-to-end, with **no** literature hypothesis and **no** `sorry`.

We build a concrete computable model of `GF(2⁵)` (`Fin 32`, XOR addition,
carry-less multiplication modulo the irreducible `x⁵ + x² + 1`), and take the
Kasami map `f = x^{d 2} = x¹³`, shift `a = 1`, and the admissible coefficient
triple `c = (1, 2, 3)` (as elements of `GF(32) = Fin 32`).  Then:

* `preCount_eq_pow` — the preimage triple count is generic (`= 2^{(3-1)·5} = 1024`),
  by `native_decide` over the `32³` tuples (equivalently, `Vanish` holds for
  `c = (1,2,3)`, with no spectral input);
* `imgCount_eq` — hence the image triple count is `2^{2·5-3} = 128`,

via the green computable criterion `MTuple.imgCount_of_preCount` and the project's
`kasami_is_apn_pred` (`k = 2`, `d 2 = 13`).  The derivative autocorrelation's value
set (which is *not* three-valued here) is never used.

That `c` genuinely matters — `preCount` for e.g. `c = (1,3,7)` is `1056 ≠ 1024`, so
that triple is *not* admissible — confirming the count is a real, `c`-dependent
statement, not a vacuous identity.
-/

namespace MTuple.VanishInstanceGF32

/-! ## A concrete, computable model of `GF(2⁵)` -/

/-- `GF(32)` as `Fin 32`, elements read as 5-bit polynomials over `GF(2)`. -/
def GF32 : Type := Fin 32

namespace GF32

instance : DecidableEq GF32 := inferInstanceAs (DecidableEq (Fin 32))
instance : Fintype GF32 := inferInstanceAs (Fintype (Fin 32))

/-- Carry-less multiplication of two 5-bit numbers (result `< 2⁹`). -/
def clmul (a b : Nat) : Nat :=
  (if b &&& 1 = 1 then a else 0) ^^^
  (if b &&& 2 = 2 then a <<< 1 else 0) ^^^
  (if b &&& 4 = 4 then a <<< 2 else 0) ^^^
  (if b &&& 8 = 8 then a <<< 3 else 0) ^^^
  (if b &&& 16 = 16 then a <<< 4 else 0)

/-- Reduce a `< 2⁹` value modulo `x⁵ + x² + 1` (`= 0b100101 = 37`). -/
def reduce (n : Nat) : Nat := Id.run do
  let mut r := n
  if r &&& 256 = 256 then r := r ^^^ (37 <<< 3)
  if r &&& 128 = 128 then r := r ^^^ (37 <<< 2)
  if r &&& 64 = 64 then r := r ^^^ (37 <<< 1)
  if r &&& 32 = 32 then r := r ^^^ 37
  return r &&& 31

instance : Add GF32 := ⟨fun a b => (⟨(a.1 ^^^ b.1) % 32, Nat.mod_lt _ (by norm_num)⟩ : Fin 32)⟩
instance : Mul GF32 := ⟨fun a b => (⟨(reduce (clmul a.1 b.1)) % 32, Nat.mod_lt _ (by norm_num)⟩ : Fin 32)⟩
instance : Neg GF32 := ⟨id⟩
instance : Zero GF32 := ⟨(⟨0, by norm_num⟩ : Fin 32)⟩
instance : One GF32 := ⟨(⟨1, by norm_num⟩ : Fin 32)⟩

instance instCR : CommRing GF32 := CommRing.ofMinimalAxioms
  (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  (by native_decide) (by native_decide) (by native_decide)

instance : Nontrivial GF32 := ⟨⟨0, 1, by decide⟩⟩
instance : NoZeroDivisors GF32 := ⟨by native_decide⟩

/-- `GF(32)` is a field, with the computable inverse `a⁻¹ = a³⁰` (since `a³¹ = 1`). -/
instance instField : Field GF32 :=
  { instCR with
    inv := fun a => a ^ 30
    mul_inv_cancel := by native_decide
    inv_zero := by native_decide
    nnqsmul := _
    qsmul := _ }

instance instCharP : CharP GF32 2 := by
  rw [← ringChar.eq_iff]
  rcases Nat.prime_two.eq_one_or_self_of_dvd _
      (ringChar.dvd (show (2 : GF32) = 0 by decide)) with h1 | h2
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h2

theorem card_eq : Fintype.card GF32 = 2 ^ 5 := by decide

end GF32

/-! ## The unconditional `k = 2` triple count -/

open MTuple WalshAB CollisionAnalysis

/-- The admissible coefficient triple `c = (1, 2, 3)` over `GF(32) = Fin 32`. -/
def c3 : Fin 3 → GF32 := ![(⟨1, by decide⟩ : GF32), ⟨2, by decide⟩, ⟨3, by decide⟩]

/-- A computable mirror of the (noncomputable) `preCount` for this instance. -/
def preCount3Comp : ℕ :=
  (Finset.univ.filter (fun x : Fin 3 → GF32 =>
    ∑ i, c3 i * MTuple.deriv (fun x : GF32 => x ^ CollisionAnalysis.d 2) 1 (x i) = 0)).card

/-- The `k = 2` Kasami map `x ↦ x^{d 2} = x¹³` is APN over `GF(32)` (project's
`kasami_is_apn_pred`). -/
theorem kasami_apn : IsAPN (fun x : GF32 => x ^ CollisionAnalysis.d 2) :=
  KasamiAB.kasami_is_apn_pred (F := GF32) GF32.card_eq 2 (by norm_num)
    (by norm_num) (by decide) (by decide) (by norm_num)

/-- **The preimage triple count is generic** (`= 2^{(3-1)·5} = 1024`), by
`native_decide` over the `32³` tuples — i.e. `Vanish` holds for `c = (1,2,3)`. -/
theorem preCount_eq_pow :
    MTuple.preCount 3 (fun x : GF32 => x ^ CollisionAnalysis.d 2) 1 c3
      = 2 ^ ((3 - 1) * 5) := by
  show preCount3Comp = 2 ^ ((3 - 1) * 5)
  native_decide

/-- **The unconditional `k = 2` Kasami triple count over `GF(32)`.**  With no
hypotheses at all, the image triple count of the quadratic Kasami exponent's
derivative at the admissible triple `c = (1,2,3)` is `2^{2·5-3} = 128`. -/
theorem imgCount_eq :
    MTuple.imgCount 3 (fun x : GF32 => x ^ CollisionAnalysis.d 2) 1 c3
      = 2 ^ (2 * 5 - 3) := by
  have h := MTuple.imgCount_of_preCount 5 3 (by norm_num) (by norm_num)
    (fun x : GF32 => x ^ CollisionAnalysis.d 2) kasami_apn 1 (by decide) c3 preCount_eq_pow
  simpa using h

end MTuple.VanishInstanceGF32

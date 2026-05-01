import Mathlib

/-!
# Kasami Polar Expansion — Route 1 Adjoint Logic

This file proves `kasami_polar_expansion`, the trace-level identity connecting
the polar form of the power function to the associated linearized operator.

## Mathematical Background

For a finite field `F = GF(2^n)` of characteristic 2 and the power exponent
`d = 2^k + 1`, the polar form expands algebraically to
`x · y^(2^k) + x^(2^k) · y`, and the Route 1 Adjoint Logic proves:

    `Tr(a · polar(x, y)) = Tr(x · L_a(y))`

where `L_a(y) = a · y^(2^k) + a^(2^(n-k)) · y^(2^(n-k))`.
-/

open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

section KasamiPolar

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [FiniteDimensional (ZMod 2) F] [Algebra.IsSeparable (ZMod 2) F]

/-- CharP F 2 derived from the algebra structure. -/
noncomputable instance kasamiCharPTwo : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

instance kasamiFactPrime2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The field trace `Tr : F → GF(2)`. -/
noncomputable abbrev fieldTrace : F →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) F

/-! ## Frobenius Algebra -/

/-- **Trace Frobenius invariance.** `Tr(w^(2^j)) = Tr(w)` for all `j`. -/
lemma trace_frobenius_inv (w : F) (j : ℕ) :
    fieldTrace (w ^ (2 ^ j)) = fieldTrace w := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h_inj : Function.Injective (fun x : F => x ^ 2) :=
      fun x y hxy => by simpa [sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq] using hxy
    have h_bij : Function.Bijective (fun x : F => x ^ 2) :=
      ⟨h_inj, Finite.injective_iff_surjective.mp h_inj⟩
    let frobAut : F ≃ₐ[ZMod 2] F :=
      { Equiv.ofBijective _ h_bij with
        map_add' := fun x y => add_pow_char x y 2
        map_mul' := fun x y => by simp [mul_pow]
        commutes' := fun r => by fin_cases r <;> simp }
    calc fieldTrace (w ^ (2 ^ (j + 1)))
        = fieldTrace ((w ^ (2 ^ j)) ^ 2) := by
            congr 1; rw [pow_succ 2 j, pow_mul]
      _ = fieldTrace (w ^ (2 ^ j)) :=
            Algebra.trace_eq_of_algEquiv frobAut _
      _ = fieldTrace w := ih

/-! ## Gold Polar Expansion (Algebraic) -/

/-- **Gold Polar Expansion.** For `d = 2^k + 1` in characteristic 2:
    `(x + y)^(2^k + 1) + x^(2^k + 1) + y^(2^k + 1) = x · y^(2^k) + x^(2^k) · y` -/
lemma gold_polar_expand (x y : F) (k : ℕ) :
    (x + y) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1) =
    x * y ^ (2 ^ k) + x ^ (2 ^ k) * y := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hfrob : (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
    add_pow_char_pow x y 2 k
  calc (x + y) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1)
      = (x + y) * (x + y) ^ (2 ^ k) +
        x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1) := by ring
    _ = (x + y) * (x ^ (2 ^ k) + y ^ (2 ^ k)) +
        x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1) := by rw [hfrob]
    _ = x * y ^ (2 ^ k) + x ^ (2 ^ k) * y := by ring_nf; simp [h2]

/-! ## Element identity `x^(2^n) = x` -/

/-- Every element of `F` satisfies `x^(2^n) = x` where `n = [F : GF(2)]`. -/
lemma pow_finrank_eq_self (x : F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    x ^ (2 ^ Module.finrank (ZMod 2) F) = x := by
  haveI : Fintype F := Fintype.ofFinite F
  have h : Fintype.card F = 2 ^ Module.finrank (ZMod 2) F := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have h2 := FiniteField.pow_card (K := F) x
  rwa [h] at h2

/-! ## Trace Adjoint Identity -/

/-- **Trace Adjoint Identity.**
    `Tr(u · v^(2^j)) = Tr(u^(2^(n − j)) · v)` -/
lemma trace_adjoint (u v : F) (j : ℕ) (hj : j ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    fieldTrace (u * v ^ (2 ^ j)) =
    fieldTrace (u ^ (2 ^ (Module.finrank (ZMod 2) F - j)) * v) := by
  set n := Module.finrank (ZMod 2) F with hn_def
  have hexp : 2 ^ j * 2 ^ (n - j) = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  calc fieldTrace (u * v ^ (2 ^ j))
      = fieldTrace ((u * v ^ (2 ^ j)) ^ (2 ^ (n - j))) := by
          rw [trace_frobenius_inv]
    _ = fieldTrace (u ^ (2 ^ (n - j)) * (v ^ (2 ^ j)) ^ (2 ^ (n - j))) := by
          rw [mul_pow]
    _ = fieldTrace (u ^ (2 ^ (n - j)) * v ^ (2 ^ j * 2 ^ (n - j))) := by
          rw [← pow_mul]
    _ = fieldTrace (u ^ (2 ^ (n - j)) * v ^ (2 ^ n)) := by
          rw [hexp]
    _ = fieldTrace (u ^ (2 ^ (n - j)) * v) := by
          congr 1; rw [pow_finrank_eq_self v hcard]

/-! ## Trace Non-degeneracy -/

/-- **Trace non-degeneracy.** If `Tr(x · z) = 0` for all `x`, then `z = 0`. -/
lemma trace_nondeg (z : F) (hz : ∀ x : F, fieldTrace (x * z) = 0) :
    z = 0 := by
  by_contra h
  have h_nonzero : ∃ x : F, fieldTrace x ≠ 0 := by
    by_contra! hall
    exact Algebra.trace_ne_zero (ZMod 2) F (LinearMap.ext hall)
  exact h_nonzero.choose_spec (by simpa [h] using hz (h_nonzero.choose / z))

/-! ## The Linearized Operator -/

/-- The linearized operator `L_a(y)` for the Gold/Kasami exponent:
    `L_a(y) = a · y^(2^k) + a^(2^(n−k)) · y^(2^(n−k))` -/
noncomputable def goldLinearizedOp (k : ℕ) (a y : F) : F :=
  a * y ^ (2 ^ k) + a ^ (2 ^ (Module.finrank (ZMod 2) F - k)) *
    y ^ (2 ^ (Module.finrank (ZMod 2) F - k))

/-! ## The Bridge Lemma -/

/-- **Bridge Lemma.** `Tr(a · (x · y^(2^k) + x^(2^k) · y)) = Tr(x · L_a(y))` -/
lemma gold_bridge (k : ℕ) (a x y : F) (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    fieldTrace (a * (x * y ^ (2 ^ k) + x ^ (2 ^ k) * y)) =
    fieldTrace (x * goldLinearizedOp k a y) := by
  set nk := Module.finrank (ZMod 2) F - k with hnk_def
  show fieldTrace (a * (x * y ^ (2 ^ k) + x ^ (2 ^ k) * y)) =
    fieldTrace (x * (a * y ^ (2 ^ k) + a ^ (2 ^ nk) * y ^ (2 ^ nk)))
  simp only [mul_add, map_add]
  calc fieldTrace (a * (x * y ^ (2 ^ k))) +
       fieldTrace (a * (x ^ (2 ^ k) * y))
      = fieldTrace (x * (a * y ^ (2 ^ k))) +
        fieldTrace ((a * y) * x ^ (2 ^ k)) := by ring_nf
    _ = fieldTrace (x * (a * y ^ (2 ^ k))) +
        fieldTrace ((a * y) ^ (2 ^ nk) * x) := by
          congr 1
          exact trace_adjoint (a * y) x k hk hcard
    _ = fieldTrace (x * (a * y ^ (2 ^ k))) +
        fieldTrace (x * (a ^ (2 ^ nk) * y ^ (2 ^ nk))) := by
          congr 1; rw [mul_pow]; ring_nf

/-! ## Main Theorem — `kasami_polar_expansion` -/

/-- The polar form for the exponent `d = 2^k + 1`. -/
def kasamiPolar (k : ℕ) (x y : F) : F :=
  (x + y) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1)

/-- The bilinear form `B_a(x, y) = Tr(a · polar(x, y))`. -/
noncomputable def kasamiBilin (k : ℕ) (a x y : F) : ZMod 2 :=
  fieldTrace (a * kasamiPolar k x y)

/-- **`kasami_polar_expansion`** — The Route 1 Adjoint Identity.
    `Tr(a · ((x+y)^d + x^d + y^d)) = Tr(x · L_a(y))` -/
theorem kasami_polar_expansion (k : ℕ) (a x y : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    kasamiBilin k a x y = fieldTrace (x * goldLinearizedOp k a y) := by
  unfold kasamiBilin kasamiPolar
  calc fieldTrace
          (a * ((x + y) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1)))
      = fieldTrace (a * (x * y ^ (2 ^ k) + x ^ (2 ^ k) * y)) := by
          congr 1; rw [gold_polar_expand]
    _ = fieldTrace (x * goldLinearizedOp k a y) :=
          gold_bridge k a x y hk hcard

/-! ## Radical = Kernel -/

/-- The radical of `Q_a`. -/
def kasamiRadical (k : ℕ) (a : F) : Set F :=
  { y | ∀ x, kasamiBilin k a x y = 0 }

/-- The kernel of `L_a`. -/
noncomputable def kasamiKernel (k : ℕ) (a : F) : Set F :=
  { y | goldLinearizedOp k a y = 0 }

/-- **Radical = Kernel.** `rad(Q_a) = ker(L_a)` for the Gold/Kasami exponent. -/
theorem kasami_radical_eq_kernel (k : ℕ) (a : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    kasamiRadical k a = kasamiKernel k a := by
  ext y
  simp only [kasamiRadical, kasamiKernel, Set.mem_setOf_eq]
  constructor
  · intro hy
    apply trace_nondeg
    intro x
    have := hy x
    rw [kasami_polar_expansion k a x y hk hcard] at this
    exact this
  · intro hy x
    rw [kasami_polar_expansion k a x y hk hcard]
    simp [hy]

end KasamiPolar

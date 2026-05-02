/-
# Phase 1: The Algebraic Foundation (Polar Expansion)

Proves the core algebraic identities for the Gold function in characteristic 2:

1. **Gold cross-term expansion**: (x+y)^(2^k+1) = x^(2^k+1) + y^(2^k+1) + x^(2^k)y + xy^(2^k)
2. **L_a additivity**: L_a(x+y) = L_a(x) + L_a(y)
3. **Polar form identity**: Q_a(x+y) = Q_a(x) + Q_a(y) + B_a(x,y)
4. **Differential identity**: f(x+a) = f(x) + f(a) + L_a(x) where f(x) = x^(2^k+1)
5. **Bilinear symmetry**: B_a(x,y) = B_a(y,x)

All proofs use only `ring` and the characteristic-2 Frobenius identity.
No character sums or Fourier analysis appear in this file.
-/
import RequestProject.Kasami.Defs

set_option maxHeartbeats 800000

namespace KasamiData

variable (K : KasamiData)

/-! ## Gold Cross-Term Expansion -/

/-- In characteristic 2: (x+y)^(2^k+1) = x^(2^k+1) + y^(2^k+1) + x^(2^k)y + xy^(2^k).

    Proof: factor as (x+y)^(2^k) · (x+y), use Frobenius additivity, expand.
    All cross terms with coefficient 2 vanish in characteristic 2. -/
theorem gold_cross_expand (x y : K.F) :
    (x + y) ^ K.goldExp =
      x ^ K.goldExp + y ^ K.goldExp + (K.frob x * y + x * K.frob y) := by
  simp only [goldExp, frob_def]
  have : (x + y) ^ (2 ^ K.k + 1) = (x + y) ^ (2 ^ K.k) * (x + y) := by ring
  rw [this, add_pow_expChar_pow x y 2 K.k]
  ring_nf

/-! ## Additivity of L_a -/

/-- L_a is additive (𝔽₂-linear). -/
theorem linMap_add (a x y : K.F) :
    K.linMap a (x + y) = K.linMap a x + K.linMap a y := by
  simp only [linMap]
  rw [K.frob_add x y]
  ring

theorem linMap_zero (a : K.F) : K.linMap a 0 = 0 := by
  simp [linMap]

/-! ## Differential Identity -/

/-- The Gold function differential:
    f(x + a) = f(x) + f(a) + L_a(x), where f(x) = x^(2^k+1).
    This shows L_a(x) = f(x+a) + f(x) + f(a). -/
theorem gold_differential (a x : K.F) :
    (x + a) ^ K.goldExp = x ^ K.goldExp + a ^ K.goldExp + K.linMap a x := by
  rw [gold_cross_expand]
  simp [linMap]; ring

/-! ## Polar Form Identity -/

/-- The polar form of Q_a:
    Q_a(x + y) = Q_a(x) + Q_a(y) + B_a(x, y).

    This is a direct consequence of the Gold cross-term expansion
    and linearity of the trace. -/
theorem goldQuad_polar (a x y : K.F) :
    K.goldQuad a (x + y) = K.goldQuad a x + K.goldQuad a y + K.goldBilin a x y := by
  simp only [goldQuad, goldBilin, goldExp, frob_def]
  have expand := K.gold_cross_expand x y
  simp only [goldExp, frob_def] at expand
  rw [expand]
  simp only [Tr, mul_add, map_add]

/-! ## Bilinear Symmetry -/

/-- The bilinear form B_a is symmetric: B_a(x,y) = B_a(y,x). -/
theorem goldBilin_symm (a x y : K.F) :
    K.goldBilin a x y = K.goldBilin a y x := by
  simp only [goldBilin, frob_def]
  congr 1; ring

/-- B_a is additive in the first argument. -/
theorem goldBilin_add_left (a x₁ x₂ y : K.F) :
    K.goldBilin a (x₁ + x₂) y = K.goldBilin a x₁ y + K.goldBilin a x₂ y := by
  simp only [goldBilin]
  rw [K.frob_add]
  simp only [Tr, mul_add, add_mul, map_add]
  ring_nf

/-- B_a is additive in the second argument. -/
theorem goldBilin_add_right (a x y₁ y₂ : K.F) :
    K.goldBilin a x (y₁ + y₂) = K.goldBilin a x y₁ + K.goldBilin a x y₂ := by
  rw [goldBilin_symm, goldBilin_add_left, goldBilin_symm K a y₁, goldBilin_symm K a y₂]

/-! ## Trace Non-Degeneracy -/

/-
The trace form is non-degenerate: if Tr(xy) = 0 for all y, then x = 0.
    This is a standard fact for separable extensions.
-/
theorem trace_nondegenerate (x : K.F) (h : ∀ y : K.F, K.Tr (x * y) = 0) :
    x = 0 := by
  contrapose! h with hx;
  -- Since the trace is surjective, there exists some $y \in \mathbb{F}_{2^n}$ such that $\text{Tr}(y) = 1$.
  obtain ⟨y, hy⟩ : ∃ y : K.F, K.Tr y = 1 := by
    have := Algebra.trace_surjective ( ZMod 2 ) K.F;
    exact this 1;
  exact ⟨ x⁻¹ * y, by aesop ⟩

/-- Equivalent form: the trace pairing is non-degenerate. -/
theorem trace_nondegenerate' (x : K.F) (hx : x ≠ 0) :
    ∃ y : K.F, K.Tr (x * y) ≠ 0 := by
  by_contra h
  push_neg at h
  exact hx (K.trace_nondegenerate x (fun y => by simpa using h y))

end KasamiData
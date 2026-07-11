import Mathlib

/-!
# Theorem 6 (Dobbertin 1999) — the conserved cross-invariant

The proof of Theorem 6 introduces three polynomial families `A_i, B_i, C_i`
obeying a shared two-step (Fibonacci-like) linear recursion
`s (i+2) = u i · s (i+1) + v i · s i`.  The last equations of the proof
(equation (11)) are a bilinear **cross-invariant** of two such sequences:

  `A_i B_{i+1} + A_{i+1} B_i = z_i`,   with   `z_{i+1} = v_i · z_i`,

conserved exactly like a 2×2 determinant / Wronskian of a linear recurrence.
In characteristic `2` the diagonal terms cancel, which is what forces the
identity.  This file formalises that mechanism.
-/

namespace KasamiPerm.Casoratian

/-!
## The general Casoratian (discrete Wronskian)

Before specialising to characteristic `2`, we record the mechanism in full
generality over an arbitrary commutative ring.  For two solutions `A, B` of the
shared linear recurrence `s (i+2) = u i · s (i+1) + v i · s i`, the **Casoratian**
`W i = A i · B (i+1) − A (i+1) · B i` (the discrete Wronskian / `2×2`
determinant of the pair of solutions) is conserved up to the coefficient `−v i`:

  `W (i+1) = − v i · W i`.

This is the ring-theoretic heart of Theorem 6's "lucky" degeneration: a linear
recurrence propagates its solutions by a companion matrix of determinant `−v i`,
so the Casoratian of any two solutions is multiplied by that determinant at each
step.  The characteristic-`2` `cross_invariant` below is exactly this identity
after `−1 = 1` collapses the sign (turning the determinant into the *symmetric*
cross term `A i · B (i+1) + A (i+1) · B i` used in the paper). -/
theorem casoratian {R : Type*} [CommRing R] {u v A B : ℕ → R}
    (recA : ∀ i, A (i + 2) = u i * A (i + 1) + v i * A i)
    (recB : ∀ i, B (i + 2) = u i * B (i + 1) + v i * B i) (i : ℕ) :
    A (i + 1) * B (i + 2) - A (i + 2) * B (i + 1)
      = (- v i) * (A i * B (i + 1) - A (i + 1) * B i) := by
  rw [recA i, recB i]; ring

/-- **Inhomogeneous (driven) Casoratian.**  If `A` solves the homogeneous
recurrence and `C` solves the *same* recurrence with an added source term `w i`
(`C (i+2) = u i * C (i+1) + v i * C i + w i`), then the mixed Casoratian
`W i = A i * C (i+1) - A (i+1) * C i` obeys the driven conservation law

  `W (i+1) = - v i * W i + w i * A (i+1)`.

This is the variation-of-parameters avatar of the auxiliary `C_i` family in the
proof of Theorem 6: `A_i, B_i` solve the homogeneous recurrence while `C_i`
solves it with Dobbertin's inhomogeneity `w i = Z^{2^{(i+1)k}}`.  The source term
is what makes the `A`–`C` cross term fail to be conserved on its own, and it is
exactly this driven term that supplies the `(k'+1) A_{k'}` correction collapsing
the cubic's constant coefficient `A_0`. -/
theorem casoratian_inhom {R : Type*} [CommRing R] {u v w A C : ℕ → R}
    (recA : ∀ i, A (i + 2) = u i * A (i + 1) + v i * A i)
    (recC : ∀ i, C (i + 2) = u i * C (i + 1) + v i * C i + w i) (i : ℕ) :
    A (i + 1) * C (i + 2) - A (i + 2) * C (i + 1)
      = (- v i) * (A i * C (i + 1) - A (i + 1) * C i) + w i * A (i + 1) := by
  rw [recA i, recC i]; ring

variable {R : Type*} [CommRing R] [CharP R 2]

/-- `A` and `B` obey the common two-step linear recursion
`s (i+2) = u i * s (i+1) + v i * s i` of Theorem 6. -/
structure TwoStep (u v A B : ℕ → R) : Prop where
  recA : ∀ i, A (i + 2) = u i * A (i + 1) + v i * A i
  recB : ∀ i, B (i + 2) = u i * B (i + 1) + v i * B i

/-- The bilinear cross-invariant (Wronskian) `A i * B (i+1) + A (i+1) * B i`
is conserved up to the lower recursion coefficient `v i` (equation (11)). -/
theorem cross_invariant {u v A B : ℕ → R} (h : TwoStep u v A B) (i : ℕ) :
    A (i + 1) * B (i + 2) + A (i + 2) * B (i + 1)
      = v i * (A i * B (i + 1) + A (i + 1) * B i) := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  rw [h.recA i, h.recB i]
  linear_combination (u i * A (i + 1) * B (i + 1)) * h2

/-- Key identity `A_i B_{i+1} + A_{i+1} B_i = z_i`: with `z (i+1) = v i * z i`,
the cross-invariant equals `z i` for all `i` once it holds at the base. -/
theorem key_identity {u v A B z : ℕ → R} (h : TwoStep u v A B)
    (hz : ∀ i, z (i + 1) = v i * z i)
    (h0 : A 0 * B 1 + A 1 * B 0 = z 0) (i : ℕ) :
    A i * B (i + 1) + A (i + 1) * B i = z i := by
  induction i with
  | zero => exact h0
  | succ n ih => rw [hz n, ← ih]; exact cross_invariant h n

end KasamiPerm.Casoratian

import RequestProject.Steiner.Preliminaries

/-!
# The Walsh transform (Section 2.1)

We transcribe Definition 2.1, Remark 2.2 and the correlation (Eq. (4), (5))
from the paper.
-/

open scoped BigOperators

namespace Flystel

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- **Definition 2.1** (Walsh transform).
Let `Fq` be a finite field, `n, m ≥ 1`, let `ψ : Fq → ℂ` be a non-trivial
additive character, let `F : Fqⁿ → Fqᵐ`, and let `a ∈ Fqⁿ`, `b ∈ Fqᵐ`.
The Walsh transform for the character `ψ` of the linear approximation `(a, b)`
of `F` is
`W_F(ψ, a, b) = ∑_{x ∈ Fqⁿ} ψ (⟨a, x⟩ + ⟨b, F(x)⟩)`.

For a fixed `F`, the values `W_F(ψ, a, b)` are the *Walsh spectrum* of `F`. -/
noncomputable def walshTransform {n m : ℕ} (ψ : AddChar Fq ℂ)
    (F : (Fin n → Fq) → (Fin m → Fq)) (a : Fin n → Fq) (b : Fin m → Fq) : ℂ :=
  ∑ x : Fin n → Fq, ψ (dotProduct a x + dotProduct b (F x))

@[simp] theorem walshTransform_def {n m : ℕ} (ψ : AddChar Fq ℂ)
    (F : (Fin n → Fq) → (Fin m → Fq)) (a : Fin n → Fq) (b : Fin m → Fq) :
    walshTransform ψ F a b
      = ∑ x : Fin n → Fq, ψ (dotProduct a x + dotProduct b (F x)) := rfl

/-- **Remark 2.2 / Eq. (5)** (Correlation).
The correlation of `F` for two non-trivial additive characters `ψ, φ` is
`CORR_F(ψ, φ) = W_F(ψ, φ) / qⁿ`.  Here we record the (rescaled) absolute value
that the paper estimates; it is independent of the multiplicative constant
relating `ψ` and `φ`. -/
noncomputable def correlation {n m : ℕ} (ψ : AddChar Fq ℂ)
    (F : (Fin n → Fq) → (Fin m → Fq)) (a : Fin n → Fq) (b : Fin m → Fq) : ℂ :=
  walshTransform ψ F a b / (Fintype.card Fq : ℂ) ^ n

end Flystel

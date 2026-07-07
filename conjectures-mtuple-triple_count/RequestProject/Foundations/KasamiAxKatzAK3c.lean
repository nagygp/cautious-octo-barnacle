import RequestProject.Foundations.KasamiAxKatzAK3b
import Mathlib

/-!
# Foundations, Layer AK3.3 (concrete) — the cyclotomic ring of integers `𝓞 K = ℤ[μ]`
and the Gauss-sum valuation constraint, concretely

This module makes the abstract local-valuation framework of `KasamiAxKatzAK3b.lean`
**concrete** by instantiating the Dedekind domain `O` with the ring of integers
`𝓞 K` of an honest number field `K` (the cyclotomic field `ℚ(μ)` of conductor
`q − 1` is one such `K`, whose ring of integers is the cyclotomic ring `ℤ[μ]`),
and by tying the abstract conjugate-pair constraint to a genuine Mathlib
`gaussSum`.

## What is established (sorry-free)

1. **`2` is a genuine non-unit in `𝓞 K`.**  `ringOfIntegers_two_ne_zero`
   (`2 ≠ 0`) and `ringOfIntegers_not_isUnit_two` (`¬ IsUnit 2`): the rational
   prime `2` is neither `0` nor a unit in the ring of integers of any number
   field (its inverse `1/2 ∉ ℤ`, so `1/2` is not an algebraic integer).  Hence
   (`exists_primeAboveTwo_ringOfIntegers`) there is a height-one prime `v` of
   `𝓞 K` above `2`, the concrete prime on which Stickelberger's valuation acts —
   no longer an abstract hypothesis.

2. **The Gauss-sum conjugate-pair constraint, concretely.**
   `intValuation_gaussSum_conj_pair`: for a non-trivial multiplicative character
   `χ : MulChar F (𝓞 K)` and a primitive additive character `ψ : AddChar F (𝓞 K)`
   over `F = GF(2ⁿ)`, the *actual* Gauss sum `g = gaussSum χ ψ` and its conjugate
   `ḡ = gaussSum χ⁻¹ ψ⁻¹` are genuine elements of `𝓞 K`, and their local
   valuations satisfy `v(g)·v(ḡ) = v(2)ⁿ`.  This ties the abstract product
   constraint of AK3.3 to honest Gauss sums living in the concrete cyclotomic
   ring of integers.

## Scope

This layer is sorry-free.  It supplies the **concrete instantiation** of the
AK3.2/AK3.3 framework: the prime above `2` in an honest ring of integers and the
valuation constraint on an honest Gauss sum.  The **individual** split
`v(g(ω^{-s})) = s₂(s)` (the Gross–Koblitz / Stickelberger factorization) remains
the open deep core — it requires the `p`-adic / Teichmüller machinery absent from
Mathlib, and is documented as the open frontier, neither axiomatized nor
`sorry`-ed.

## Sources

Washington, *Introduction to Cyclotomic Fields*, Ch. 1–2 (the cyclotomic ring of
integers `ℤ[μ]`); Ireland–Rosen, Ch. 14 (Gauss sums, Stickelberger);
Marcus, *Number Fields*, Ch. 2 (rings of integers, `2` non-unit).
-/

namespace Vanish.Foundations

open NumberField IsDedekindDomain MulChar BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-! ## 1. `2` is a genuine non-unit in the ring of integers `𝓞 K` -/

/-- **`2 ≠ 0` in `𝓞 K`.** -/
theorem ringOfIntegers_two_ne_zero : (2 : 𝓞 K) ≠ 0 := two_ne_zero

/-
**`2` is not a unit in `𝓞 K`.**  Its inverse in `K` is `1/2 ∉ ℤ`, which is
not an algebraic integer, so `2` has no inverse in `𝓞 K`.
-/
theorem ringOfIntegers_not_isUnit_two : ¬ IsUnit (2 : 𝓞 K) := by
  intro h;
  -- Then `IsUnit (2 : 𝓞 K)` which implies `|(RingOfIntegers.norm ℚ (2 : 𝓞 K) : ℚ)| = 1`.
  have h_norm : (RingOfIntegers.norm ℚ (2 : 𝓞 K) : ℚ) = 2 ^ (Module.finrank ℚ K) := by
    convert Algebra.norm_algebraMap ( 2 : ℚ );
    norm_num;
    convert rfl;
  have := NumberField.isUnit_iff_norm.mp h;
  rw [ h_norm, abs_of_nonneg ( by positivity ) ] at this ; linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℚ ) ≤ 2 ) ( show Module.finrank ℚ K ≥ 1 from Module.finrank_pos ) ]

/-- **A prime above `2` in `𝓞 K`.**  Concretely realizing
`exists_primeAboveTwo`: there is a height-one prime `v` of the ring of integers
containing `2`. -/
theorem exists_primeAboveTwo_ringOfIntegers :
    ∃ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal :=
  exists_primeAboveTwo ringOfIntegers_two_ne_zero ringOfIntegers_not_isUnit_two

/-! ## 2. The Gauss-sum conjugate-pair valuation constraint, concretely -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- **The conjugate-pair constraint on an honest Gauss sum.**  For `F = GF(2ⁿ)`,
a non-trivial multiplicative character `χ` and a primitive additive character
`ψ` valued in `𝓞 K`, the local valuation at a prime `v` above `2` satisfies
`v(gaussSum χ ψ)·v(gaussSum χ⁻¹ ψ⁻¹) = v(2)ⁿ`. -/
theorem intValuation_gaussSum_conj_pair (v : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n)
    {χ : MulChar F (𝓞 K)} (hχ : χ ≠ 1) {ψ : AddChar F (𝓞 K)} (hψ : ψ.IsPrimitive) :
    v.intValuation (gaussSum χ ψ) * v.intValuation (gaussSum χ⁻¹ ψ⁻¹)
      = (v.intValuation 2) ^ n := by
  apply intValuation_conj_pair
  rw [gaussSum_mul_inv_eq_card hχ hψ, hcard]
  push_cast
  ring

end Vanish.Foundations
/-
# Quadratic Forms over GF(2) and Gauss Sum Formula

This module develops the theory of quadratic forms over GF(2), which is
the key tool for analyzing the Walsh spectrum of Kasami functions.

## Main definitions
* `QuadForm2` : A quadratic form Q : (Fin r → ZMod 2) → ZMod 2
* `gaussSum2` : The Gauss sum ∑_x (-1)^{Q(x)}

## Main results
* `gaussSum2_rank_formula_even` : Gauss sum is ±2^{(r+d)/2} when rank is even
* `gaussSum2_rank_formula_odd` : Gauss sum is 0 when rank is odd
* `gaussSum2_three_valued` : For radical dim ∈ {0,1}, values are {0, ±2^{(n+1)/2}}

## References
* Lidl, Niederreiter, "Finite Fields", Chapter 6
* MacWilliams, Sloane, "The Theory of Error-Correcting Codes", Chapter 15
-/
import Mathlib
open Finset BigOperators
noncomputable section

/-! ### Quadratic forms over GF(2) -/

/-- A quadratic form over GF(2) on GF(2)^r. -/
structure QuadForm2 (r : ℕ) where
  toFun : (Fin r → ZMod 2) → ZMod 2
  map_zero' : toFun 0 = 0

instance (r : ℕ) : CoeFun (QuadForm2 r) (fun _ => (Fin r → ZMod 2) → ZMod 2) :=
  ⟨QuadForm2.toFun⟩

/-- The associated bilinear (polar) form B(x,y) = Q(x+y) + Q(x) + Q(y). -/
def QuadForm2.bilinForm (Q : QuadForm2 r) (x y : Fin r → ZMod 2) : ZMod 2 :=
  Q (x + y) + Q x + Q y

/-- The radical: {x | B(x,y) = 0 for all y}. -/
def QuadForm2.radicalSet (Q : QuadForm2 r) : Set (Fin r → ZMod 2) :=
  {x | ∀ y, Q.bilinForm x y = 0}

/-- The dimension of the radical (as a natural number).
    This is the dimension of the GF(2)-subspace {x : B(x,y) = 0 ∀ y}. -/
def QuadForm2.radicalDim (Q : QuadForm2 r) : ℕ := sorry

/-- A quadratic form is nondegenerate if its radical is {0}. -/
def QuadForm2.isNondegenerate (Q : QuadForm2 r) : Prop :=
  Q.radicalDim = 0

/-! ### Gauss sums over GF(2) -/

/-- The Gauss sum of a quadratic form: ∑_x (-1)^{Q(x)}. -/
def gaussSum2 (Q : QuadForm2 r) : ℤ :=
  ∑ x : Fin r → ZMod 2, (1 - 2 * (ZMod.val (Q x) : ℤ))

/-! ### Gauss sum formula -/

/-- **Gauss Sum Formula (even rank case)**:
    For a quadratic form Q on GF(2)^r with radical of dimension d,
    if the rank r - d is even, the Gauss sum is ±2^{(r+d)/2}. -/
theorem gaussSum2_rank_formula_even (Q : QuadForm2 r) (d : ℕ)
    (hd : Q.radicalDim = d) (hrd : Even (r - d)) (hdr : d ≤ r) :
    gaussSum2 Q = 2 ^ ((r + d) / 2) ∨
    gaussSum2 Q = -(2 ^ ((r + d) / 2) : ℤ) := by
  sorry

/-- **Gauss Sum Formula (odd rank case)**:
    For a quadratic form Q on GF(2)^r with radical of dimension d,
    if the rank r - d is odd, the Gauss sum is 0. -/
theorem gaussSum2_rank_formula_odd (Q : QuadForm2 r) (d : ℕ)
    (hd : Q.radicalDim = d) (hrd : ¬ Even (r - d)) (hdr : d ≤ r) :
    gaussSum2 Q = 0 := by
  sorry

/-- **Three-valued spectrum lemma**: On GF(2)^n with n odd,
    if the radical dimension is 0 or 1, the Gauss sum is in {0, ±2^{(n+1)/2}}.

    * d = 0 → rank = n (odd) → Gauss sum = 0
    * d = 1 → rank = n-1 (even) → Gauss sum = ±2^{(n+1)/2} -/
theorem gaussSum2_three_valued (n : ℕ) (hn : Odd n) (Q : QuadForm2 n)
    (hd : Q.radicalDim = 0 ∨ Q.radicalDim = 1) :
    gaussSum2 Q = 0 ∨
    gaussSum2 Q = 2 ^ ((n + 1) / 2) ∨
    gaussSum2 Q = -(2 ^ ((n + 1) / 2) : ℤ) := by
  rcases hd with hd0 | hd1
  · -- d = 0, rank = n (odd), Gauss sum = 0
    left
    exact gaussSum2_rank_formula_odd Q 0 hd0
      (by rw [Nat.sub_zero]; exact Nat.not_even_iff_odd.mpr hn) (Nat.zero_le n)
  · -- d = 1, rank = n-1 (even), Gauss sum = ±2^{(n+1)/2}
    have h1n : 1 ≤ n := Odd.pos hn
    have heven : Even (n - 1) := Nat.Odd.sub_odd hn odd_one
    rcases gaussSum2_rank_formula_even Q 1 hd1 heven h1n with h | h
    · right; left; exact h
    · right; right; exact h

end

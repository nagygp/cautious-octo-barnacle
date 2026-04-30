/-
# WHT² Trichotomy: `kasami_wht_sq_trichotomy`

## Mathematical Statement

For the Kasami function `f(x) = x^d` where `d = 2^{2k} - 2^k + 1`
over `GF(2^n)` with `n` odd, `n ≥ 3`, and `gcd(k,n) = 1`:

  `W_f(a)² ∈ {0, 2^{n+1}}` for all `a ∈ GF(2^n)`

## Proof Decomposition

  kasami_wht_sq_trichotomy
  ├── Layer 1 (S1.1): Q_a(x) = Tr(a·x^d) is a quadratic form
  │     ├── kasamiCrossTerm_add_right — cross-term bilinearity
  │     ├── kasamiCrossTerm_symm — symmetry
  │     └── kasamiCrossTerm_self — diagonal vanishing
  ├── Layer 2 (S1.2): B_a(x,y) = Tr(y · L_a(x))
  │     └── kasami_polar_eq_trace_linpoly
  ├── Layer 3 (S1.3): rad(Q_a) = ker(L_a)
  │     └── trace_nondeg + kasami_radical_eq_kernel
  ├── Layer 4 (S1.4): |ker(L_a)| ∈ {1, 2}
  │     └── kasamiLinPoly_ker_card
  ├── Layer 5 (S1.5): Q_a vanishes on radical
  │     └── kasami_trace_vanishes_on_kernel
  ├── Layer 6 (S1.6): W_f(a) = S(Q_a)
  │     └── kasami_wht_eq_expSum
  └── Layer 7 (Assembly): S(Q)² ∈ {0, 2^{n+1}}
        └── kasami_wht_sq_value
-/
import RequestProject.Defs
import RequestProject.QuadFormGF2
import RequestProject.CCDCrossterm

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## Layer 1: Cross-Term Analysis -/

/-- The Kasami cross-term: `(x+y)^d + x^d + y^d`. -/
def kasamiCrossTerm (k : ℕ) (x y : F) : F :=
  (x + y) ^ kasamiExp k + x ^ kasamiExp k + y ^ kasamiExp k

/-- **(S1.1a)** The Kasami cross-term is bilinear in the second argument.

    This requires deep char-2 multinomial expansion for
    `d = 2^{2k} - 2^k + 1`. The cross-terms of `(x+y)^d` are products
    of Frobenius-shifted terms, each additive. -/
theorem kasamiCrossTerm_add_right (k : ℕ) (hk : k ≠ 0) (x y₁ y₂ : F) :
    kasamiCrossTerm k x (y₁ + y₂) = kasamiCrossTerm k x y₁ + kasamiCrossTerm k x y₂ := by
  sorry

/-- **(S1.1b)** The Kasami cross-term is symmetric. -/
theorem kasamiCrossTerm_symm (k : ℕ) (x y : F) :
    kasamiCrossTerm k x y = kasamiCrossTerm k y x := by
  simp only [kasamiCrossTerm, add_comm x y]; ring

/-- **(S1.1c)** The cross-term vanishes on the diagonal. -/
theorem kasamiCrossTerm_self (k : ℕ) (hk : k ≠ 0) (x : F) :
    kasamiCrossTerm k x x = 0 := by
  simp only [kasamiCrossTerm]
  rw [CharTwo.add_self_eq_zero]
  rw [zero_pow (show kasamiExp k ≠ 0 from by unfold kasamiExp; omega)]
  simp [CharTwo.add_self_eq_zero]

/-! ## Layer 1 continued: Quadratic Form Construction -/

variable [HasTrace F]

/-- The Kasami trace-power form: `Q_a(x) = Tr(a · x^d)`. -/
def kasamiTracePower (k : ℕ) (a x : F) : ZMod 2 :=
  HasTrace.tr (a * x ^ kasamiExp k)

theorem kasamiTracePower_zero (k : ℕ) (hk : k ≠ 0) (a : F) :
    kasamiTracePower k a 0 = 0 := by
  simp only [kasamiTracePower]
  rw [zero_pow (show kasamiExp k ≠ 0 from by unfold kasamiExp; omega)]
  simp [mul_zero]
  have h := HasTrace.tr_add (0 : F) (0 : F)
  simp at h; exact h

/-- The polar form: `B_a(x,y) = Tr(a · crossTerm(x,y))`. -/
theorem kasamiTracePower_polar (k : ℕ) (a x y : F) :
    kasamiTracePower k a (x + y) + kasamiTracePower k a x + kasamiTracePower k a y =
    HasTrace.tr (a * kasamiCrossTerm k x y) := by
  simp only [kasamiTracePower, kasamiCrossTerm]
  rw [← HasTrace.tr_add, ← HasTrace.tr_add]
  congr 1; ring

/-- **(S1.1)** The polar form is additive in the second argument. -/
theorem kasamiTracePower_polar_add_right (k : ℕ) (a x y₁ y₂ : F) :
    (kasamiTracePower k a (x + (y₁ + y₂)) + kasamiTracePower k a x +
      kasamiTracePower k a (y₁ + y₂)) =
    (kasamiTracePower k a (x + y₁) + kasamiTracePower k a x + kasamiTracePower k a y₁) +
    (kasamiTracePower k a (x + y₂) + kasamiTracePower k a x + kasamiTracePower k a y₂) := by
  rw [kasamiTracePower_polar, kasamiTracePower_polar, kasamiTracePower_polar]
  by_cases hk : k = 0
  · subst hk; unfold kasamiCrossTerm kasamiExp
    simp; ring_nf
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    rw [← HasTrace.tr_add]; congr 1
    have h4 : (4 : F) = 0 := by rw [show (4 : F) = 2 * 2 from by ring, h2, zero_mul]
    simp [h2]
  · rw [← HasTrace.tr_add]; congr 1
    rw [kasamiCrossTerm_add_right k hk, mul_add]

/-! ## Layer 2: Polar Form Simplification -/

/-- The linearized polynomial `L_a(x) = a·x^{2^{2k}} + a^{2^k}·x^{2^k} + a^{2^{2k}}·x`. -/
def kasamiLinPoly (k : ℕ) (a x : F) : F :=
  a * x ^ (2 ^ (2 * k)) + a ^ (2 ^ k) * x ^ (2 ^ k) + a ^ (2 ^ (2 * k)) * x

/-- `L_a` is additive. -/
theorem kasamiLinPoly_add (k : ℕ) (a x y : F) :
    kasamiLinPoly k a (x + y) = kasamiLinPoly k a x + kasamiLinPoly k a y := by
  simp only [kasamiLinPoly, char2_freshman x y (2 * k), char2_freshman x y k]
  ring

/-- **(S1.2)** `B_a(x,y) = Tr(y · L_a(x))`.

    This requires:
    - `n ≥ 3` so the Frobenius powers `1, 2^k, 2^{2k}` are distinct mod n
    - `Tr(z^{2^i}) = Tr(z)` (trace-Frobenius compatibility)
    - `x^{2^n} = x` (Frobenius identity)

    The proof expands the cross-term, applies trace-Frobenius to absorb
    powers, then factors out `y` to obtain `L_a(x)`. -/
theorem kasami_polar_eq_trace_linpoly (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (hn3 : 3 ≤ n) (hk_lt : k < n) (a x y : F) :
    HasTrace.tr (a * kasamiCrossTerm k x y) = HasTrace.tr (y * kasamiLinPoly k a x) := by
  sorry

/-! ## Layer 3: Radical = Kernel -/

/-- **(S1.3a)** Trace non-degeneracy: `Tr(y·c) = 0` for all `y` implies `c = 0`. -/
theorem trace_nondeg (c : F) (h : ∀ y : F, HasTrace.tr (y * c) = 0) : c = 0 := by
  obtain ⟨x, hx⟩ := ‹HasTrace F›.tr_surjective 1
  contrapose! h
  exact ⟨x / c, by simp +decide [hx, h]⟩

/-- **(S1.3)** Radical of Q_a = kernel of L_a. -/
theorem kasami_radical_eq_kernel (k : ℕ) (a x : F) :
    (∀ y : F, HasTrace.tr (y * kasamiLinPoly k a x) = 0) ↔ kasamiLinPoly k a x = 0 := by
  constructor
  · exact trace_nondeg _
  · intro h; simp only [h, mul_zero]
    intro y
    have := HasTrace.tr_add (0 : F) (0 : F)
    simp at this; exact this

/-! ## Layer 4: Radical Size -/

/-- **(S1.4)** Kernel of `L_a` has size in `{1, 2}` when `gcd(k,n) = 1`.

    This follows from the kernel classification of linearized polynomials
    over finite fields. The kernel of the degree-3 linearized polynomial
    `L_a` is an F₂-subspace of dimension at most 2. When gcd(k,n) = 1,
    the dimension is 0 or 1, giving |ker| ∈ {1, 2}. -/
theorem kasamiLinPoly_ker_card (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (a : F) (ha : a ≠ 0) :
    Nat.card {x : F | kasamiLinPoly k a x = 0} = 1 ∨
    Nat.card {x : F | kasamiLinPoly k a x = 0} = 2 := by
  sorry

/-! ## Layer 5: Q Vanishes on Radical -/

/-- **(S1.5)** If `L_a(x) = 0`, then `Tr(a · x^d) = 0`.

    When `L_a(x) = 0`, the element `a · x^d` can be expressed as
    `z² + z` for some `z` (Artin-Schreier image). Since
    `Im(z² + z) = ker(Tr)`, we get `Tr(a · x^d) = 0`. -/
theorem kasami_trace_vanishes_on_kernel (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (a x : F)
    (hker : kasamiLinPoly k a x = 0) :
    HasTrace.tr (a * x ^ kasamiExp k) = 0 := by
  sorry

/-! ## Layer 6: WHT = Exponential Sum -/

/-- **(S1.6)** `W_f(a)` equals the sum of signs of `Q_a`. -/
theorem kasami_wht_eq_expSum (k : ℕ) (a : F) :
    wht (kasamiF k) a = ∑ x : F, signZ (kasamiTracePower k a x) := by
  simp only [wht, chi, kasamiF, kasamiTracePower, signZ]

/-! ## Layer 7: Assembly -/

/-- **WHT² value from Gauss sum**:
    Combines all layers to compute `W_f(a)²`.

    Case analysis on `|rad(Q_a)|`:
    - `|rad| = 1`: rank = n (odd), `S(Q)² = 2^n` is not a perfect square,
      forcing `S(Q) = 0` since S(Q) is an integer. So `W_f(a)² = 0`.
    - `|rad| = 2`: rank = n-1 (even), `S(Q)² = 2^{n+1}`.
      So `W_f(a)² = 2^{n+1}`. -/
theorem kasami_wht_sq_value (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (hnodd : Odd n) (hk0 : k ≠ 0) (hn3 : 3 ≤ n) (hk_lt : k < n)
    (a : F) :
    wht (kasamiF k) a ^ 2 = 0 ∨
    wht (kasamiF k) a ^ 2 = (2 : ℤ) ^ (n + 1) := by
  sorry

/-- **Main Theorem: `kasami_wht_sq_trichotomy`**

For the Kasami function over `GF(2^n)` with `n` odd, `n ≥ 3`, and `gcd(k,n) = 1`:
  `W_f(a)² ∈ {0, 2^{n+1}}` for all `a`. -/
theorem kasami_wht_sq_trichotomy (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (hnodd : Odd n) (hk0 : k ≠ 0) (hn3 : 3 ≤ n) (hk_lt : k < n)
    (a : F) :
    wht (kasamiF k) a ^ 2 = 0 ∨
    wht (kasamiF k) a ^ 2 = (2 : ℤ) ^ (n + 1) :=
  kasami_wht_sq_value n k hn hk hnodd hk0 hn3 hk_lt a

end

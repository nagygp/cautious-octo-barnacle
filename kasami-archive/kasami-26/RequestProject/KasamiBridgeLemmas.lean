/-
# Kasami Almost-Bent Proof: Bridge Gap Decomposition

This file decomposes the four key bridge gaps in the proof that the
Kasami power function f(x) = x^d (where d = 2^(2k) − 2^k + 1) over
GF(2^m) with m = 2k+1 is almost bent (AB), meaning its Walsh–Hadamard
transform takes values in {0, ±2^(k+1)}.

## The four bridge gaps

1. **Layer 2 gap**: Q_a(x) = Tr(a·x^d) as a quadratic form over F₂
2. **Layer 2→3 bridge**: B_a simplified via Frobenius = Tr(y·L_a(x))
3. **Layer 3→4 bridge**: ker L_a rank classification → Gauss sum formula
4. **Layer 4→5 bridge**: Exponential sum squared → WHT values

## Dependency tree

```
kasami_is_ab
  ├── wht_eq_expSum  ................................. (Bridge 4e)
  │     └── B_a_eq_trace_linPolyL .................... (Bridge 2e)
  │           ├── trace_frobenius_eq .................. (Bridge 2a)
  │           ├── add_pow_char_pow .................... (Bridge 1b)
  │           ├── kasami_cross_terms .................. (Bridge 1c)
  │           └── frob_card_eq_id ..................... (Bridge 2c)
  ├── kasami_expSum_values ............................ (Bridge 4d)
  │     ├── gauss_sum_quadratic_form_odd_rank ........ (Bridge 4c₁)
  │     ├── gauss_sum_quadratic_form_even_rank ....... (Bridge 4c₂)
  │     ├── linPolyL_ker_card_classification .......... (Bridge 3c)
  │     │     ├── linPolyL_ker_subspace ............... (Bridge 3a)
  │     │     ├── linPolyL_ker_card_le ................ (Bridge 3b)
  │     │     └── linPolyL_additive ................... (Bridge 2d)
  │     ├── radical_eq_ker ............................ (Bridge 3d)
  │     │     └── B_a_eq_trace_linPolyL ............... (Bridge 2e)
  │     └── kasami_rank_minus_nullity_parity .......... (Bridge 3f)
  └── (k+1 = (m+1)/2 when m = 2k+1, arithmetic)
```
-/



open scoped BigOperators

noncomputable section

set_option maxHeartbeats 400000

/-! ### Infrastructure -/

instance : Fact (Nat.Prime 2) := Fact.mk (by norm_num)

-- GaloisField is only `Finite`, not `Fintype`; we add a noncomputable instance.
noncomputable instance galoisFieldFintype (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    Fintype (GaloisField p n) := Fintype.ofFinite _

/-! ### Notation -/

-- F₂ = ZMod 2
abbrev F₂ : Type := ZMod 2

-- Absolute trace  Tr : GF(2^m) → F₂
abbrev AbsTr (m : ℕ) : GaloisField 2 m →ₗ[F₂] F₂ :=
  Algebra.trace (ZMod 2) (GaloisField 2 m)

-- Iterated Frobenius  x ↦ x^(2^i)
abbrev φ (m i : ℕ) : GaloisField 2 m →+* GaloisField 2 m :=
  iterateFrobenius (GaloisField 2 m) 2 i

-- Kasami exponent  d = 2^(2k) − 2^k + 1
def kasD (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-! ================================================================
## Bridge 1  (Layer 2 gap)
### Q_a(x) = Tr(a · x^d)  is a quadratic form over F₂
================================================================ -/

section Bridge1
variable (m k : ℕ) (a : GaloisField 2 m)

/-- The function Q_a. -/
def Qa (a : GaloisField 2 m) (x : GaloisField 2 m) : F₂ :=
  AbsTr m (a * x ^ kasD k)

/-- The polar form  B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y).
    (In char 2 addition = subtraction, so this is the same as subtraction.) -/
def Ba (a : GaloisField 2 m) (x y : GaloisField 2 m) : F₂ :=
  Qa m k a (x + y) + Qa m k a x + Qa m k a y

/-- **1b.** Frobenius is additive: (x+y)^(2^i) = x^(2^i) + y^(2^i) in char 2. -/
lemma add_pow_two_pow (x y : GaloisField 2 m) (i : ℕ) :
    (x + y) ^ (2 ^ i) = x ^ (2 ^ i) + y ^ (2 ^ i) := by sorry

/-- **1c.** Cross-term expansion of (x+y)^d − x^d − y^d in char 2.
    The result is a sum of mixed monomials in x, y, each of which
    is a product of iterated-Frobenius images of x and y. -/
lemma kasami_cross_terms (x y : GaloisField 2 m) :
    (x + y) ^ kasD k + x ^ kasD k + y ^ kasD k =
      (x ^ (2 ^ (2*k)) * y + x * y ^ (2 ^ (2*k)))
    + (x ^ (2 ^ k) * y ^ (2 ^ (2*k)) + x ^ (2 ^ (2*k)) * y ^ (2 ^ k))
    + (x ^ (2 ^ k) * y + x * y ^ (2 ^ k)) := by sorry

/-- **1d.** B_a is additive in the second argument (hence bilinear over F₂). -/
lemma Ba_add_right (x y₁ y₂ : GaloisField 2 m) :
    Ba m k a x (y₁ + y₂) = Ba m k a x y₁ + Ba m k a x y₂ := by sorry

/-- **1e.** B_a is symmetric. -/
lemma Ba_symm (x y : GaloisField 2 m) :
    Ba m k a x y = Ba m k a y x := by sorry

/-- **1f.** Q_a is homogeneous of degree 2, i.e. Q_a(c·x) = c²·Q_a(x).
    Over F₂ this just says Q_a(0) = 0 and Q_a(x) = Q_a(x). -/
lemma Qa_smul (c : F₂) (x : GaloisField 2 m) :
    Qa m k a (c • x) = c * Qa m k a x := by sorry

end Bridge1

/-! ================================================================
## Bridge 2  (Layer 2 → 3)
### B_a via Frobenius equals Tr(y · L_a(x))
================================================================ -/

section Bridge2
variable (m k : ℕ) (hm : m = 2 * k + 1)

/-- The linearised polynomial associated to a:
    L_a(x) = a · x^(2^(2k)) + a^(2^k) · x^(2^k) + a^(2^(2k)) · x.
    Over GF(2^m) the map x ↦ L_a(x) is F₂-linear. -/
def La (a x : GaloisField 2 m) : GaloisField 2 m :=
  a * φ m (2*k) x + φ m k a * φ m k x + φ m (2*k) a * x

/-- **2a.** Trace commutes with Frobenius: Tr(x^(2^i)) = Tr(x). -/
lemma trace_frob_eq (x : GaloisField 2 m) (i : ℕ) :
    AbsTr m (φ m i x) = AbsTr m x := by sorry

/-- **2b.** Tr(x²) = Tr(x)  (special case i = 1). -/
lemma trace_sq_eq (x : GaloisField 2 m) :
    AbsTr m (x ^ 2) = AbsTr m x := by sorry

/-- **2c.** x^(2^m) = x  for all x ∈ GF(2^m).  (Frobenius order divides m.) -/
lemma frob_card_eq_id (x : GaloisField 2 m) :
    φ m m x = x := by sorry

/-- **2d.** L_a is F₂-additive (linearised polynomial). -/
lemma La_additive (a : GaloisField 2 m) (x y : GaloisField 2 m) :
    La m k a (x + y) = La m k a x + La m k a y := by sorry

/-- **2e.** *(The key bridge)*  B_a(x, y) = Tr(y · L_a(x)).
    Proved by expanding the cross terms (Bridge 1c), applying
    Tr ∘ Frobenius = Tr (Bridge 2a), and factoring out y. -/
lemma Ba_eq_trace_La (a x y : GaloisField 2 m) :
    Ba m k a x y = AbsTr m (y * La m k a x) := by sorry

end Bridge2

/-! ================================================================
## Bridge 3  (Layer 3 → 4)
### Kernel of L_a  →  exponential-sum formula
================================================================ -/

section Bridge3
variable (m k : ℕ) (hm : m = 2 * k + 1)

/-- The kernel of L_a as a set. -/
def kerLa (a : GaloisField 2 m) : Set (GaloisField 2 m) :=
  {x | La m k a x = 0}

/-- **3a.** ker(L_a) is an F₂-subspace (closed under addition and contains 0). -/
lemma kerLa_add_mem (a x y : GaloisField 2 m) :
    x ∈ kerLa m k a → y ∈ kerLa m k a →
    x + y ∈ kerLa m k a := by sorry

/-- **3b.** |ker(L_a)| ≤ 2^k.
    Because L_a(x) = 0 is a polynomial equation of degree 2^(2k)
    in x, but by the structure of L_a it factors through a degree-2^k
    equation (using x^(2^(2k)) = x in GF(2^m)). -/
lemma kerLa_card_le (a : GaloisField 2 m) (ha : a ≠ 0) :
    Nat.card (kerLa m k a) ≤ 2 ^ k := by sorry

/-- **3c.** *(Kernel classification)* For a ≠ 0 the kernel has
    cardinality 1 or 2^(gcd(k,m)).
    When m = 2k+1 we have gcd(k, 2k+1) = gcd(k,1) = 1, so the
    only possibilities are |ker| = 1 (trivial) or |ker| = 2. -/
lemma kerLa_card_dichotomy (a : GaloisField 2 m) (ha : a ≠ 0) :
    Nat.card (kerLa m k a) = 1 ∨ Nat.card (kerLa m k a) = 2 := by sorry

/-- **3d.** rad(Q_a) = ker(L_a).
    The radical of the quadratic form Q_a (the set of x such that
    B_a(x, y) = 0 for all y) equals the kernel of L_a.
    Immediate from Bridge 2e and non-degeneracy of the trace pairing. -/
lemma radical_eq_kerLa (a : GaloisField 2 m) :
    {x : GaloisField 2 m | ∀ y, Ba m k a x y = 0} = kerLa m k a := by sorry

/-- **3e.** Exponential-sum-squared formula.
    S(a)² = 2^m · |rad(Q_a)| = 2^m · |ker(L_a)|.
    This is a standard result for quadratic forms over F₂:
    the square of the Gauss sum equals the field size times the radical size. -/
lemma expSum_sq_eq (a : GaloisField 2 m) :
    (∑ x : GaloisField 2 m, (-1 : ℤ) ^ (Qa m k a x).val) ^ 2 =
    (2 : ℤ) ^ m * ↑(Nat.card (kerLa m k a)) := by sorry

/-- **3f.** The rank m − dim(ker L_a) has the right parity.
    When |ker| = 1: dim = 0, rank = m = 2k+1 (odd).
    When |ker| = 2: dim = 1, rank = m−1 = 2k (even).
    This parity is needed to apply the Gauss sum formula. -/
lemma rank_parity_cases (a : GaloisField 2 m) (ha : a ≠ 0) :
    (Nat.card (kerLa m k a) = 1 ∧ Odd m) ∨
    (Nat.card (kerLa m k a) = 2 ∧ Even (m - 1)) := by sorry

end Bridge3

/-! ================================================================
## Bridge 4  (Layer 4 → 5)
### Exponential sum  →  WHT values
================================================================ -/

section Bridge4
variable (m k : ℕ) (hm : m = 2 * k + 1)

/-- Walsh–Hadamard transform of the power function x ↦ x^d at point b. -/
def WHT (d : ℕ) : GaloisField 2 m → ℤ := fun b =>
  ∑ x : GaloisField 2 m, (-1 : ℤ) ^ ((AbsTr m (x ^ d + b * x)).val)

/-- The exponential sum S(a) = ∑_x (−1)^(Tr(a·x^d)). -/
def ExpS (d : ℕ) : GaloisField 2 m → ℤ := fun a =>
  ∑ x : GaloisField 2 m, (-1 : ℤ) ^ ((AbsTr m (a * x ^ d)).val)

/-- **4a.** Gauss sum vanishes for odd-rank quadratic forms over F₂.
    If the quadratic form Q has radical of dimension r and
    m − r is odd, then  ∑_x (−1)^(Q(x)) = 0.  -/
lemma gauss_sum_odd_rank
    (Q : GaloisField 2 m → F₂)
    (hrad : Nat.card {x : GaloisField 2 m | ∀ y : GaloisField 2 m,
      Q (x + y) + Q x + Q y = 0} = 2 ^ r)
    (h_odd : Odd (m - r)) :
    ∑ x : GaloisField 2 m, (-1 : ℤ) ^ (Q x).val = 0 := by sorry

/-- **4b.** Gauss sum for even-rank quadratic forms over F₂.
    If m − r is even, then
    (∑_x (−1)^(Q(x)))² = 2^(m + r). -/
lemma gauss_sum_even_rank
    (Q : GaloisField 2 m → F₂)
    (hrad : Nat.card {x : GaloisField 2 m | ∀ y : GaloisField 2 m,
      Q (x + y) + Q x + Q y = 0} = 2 ^ r)
    (h_even : Even (m - r)) :
    (∑ x : GaloisField 2 m, (-1 : ℤ) ^ (Q x).val) ^ 2 =
      (2 : ℤ) ^ (m + r) := by sorry

/-- **4c.** Combining 3c + 3f + 4a + 4b for the Kasami form:
    - Case |ker| = 1 (dim = 0): rank = m is odd → S(a) = 0
    - Case |ker| = 2 (dim = 1): rank = m−1 = 2k is even →
        S(a)² = 2^(m+1) = 2^(2(k+1)), so S(a) = ±2^(k+1) -/
lemma kasami_expSum_values (a : GaloisField 2 m) :
    ExpS m (kasD k) a = 0 ∨
    ExpS m (kasD k) a = 2 ^ (k + 1) ∨
    ExpS m (kasD k) a = -(2 ^ (k + 1)) := by sorry

/-- **4d.** Auxiliary: 2^(2(k+1)) is a perfect square with root 2^(k+1). -/
lemma two_pow_sq (k : ℕ) : (2 : ℤ) ^ (2 * k + 1 + 1) = (2 ^ (k + 1)) ^ 2 := by
  ring

/-- **4e.** WHT = ExpS (relating the two sums).
    By the substitution x ↦ x + c and "completing the square"
    using B_a and L_a, the full WHT ∑_x (−1)^Tr(x^d + b·x)
    can be reduced to an exponential sum S(a) for a suitable a.
    In particular, for every b there exists a such that
    WHT(b) = ExpS(a). -/
lemma wht_eq_expSum (b : GaloisField 2 m) :
    ∃ a : GaloisField 2 m,
      WHT m (kasD k) b = ExpS m (kasD k) a := by sorry

end Bridge4

/-! ================================================================
## Main Theorem
================================================================ -/

section Main
variable (m k : ℕ) (hk : k ≥ 1) (hm : m = 2 * k + 1)

/-- **The Kasami function is almost bent.**
    For every b ∈ GF(2^m), WHT_f(b) ∈ {0, ±2^(k+1)}.

    Proof sketch (using the bridges above):
    1. Fix b. By Bridge 4e, WHT(b) = ExpS(a) for some a.
    2. By Bridge 4c, ExpS(a) ∈ {0, ±2^(k+1)}.
    3. Hence WHT(b) ∈ {0, ±2^(k+1)}.  ∎ -/
theorem kasami_is_ab (b : GaloisField 2 m) :
    WHT m (kasD k) b = 0 ∨
    WHT m (kasD k) b = 2 ^ (k + 1) ∨
    WHT m (kasD k) b = -(2 ^ (k + 1)) := by sorry

end Main

end

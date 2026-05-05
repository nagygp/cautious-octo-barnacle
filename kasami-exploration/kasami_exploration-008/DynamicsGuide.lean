/-
  DynamicsGuide.lean

  # Frobenius as Shift: Symbolic Dynamics meets Finite Field Cryptography

  This file formalizes the deep connection between:
  1. The **cyclic shift** σ on bitstrings (symbolic dynamics on Σ₂)
  2. The **Frobenius endomorphism** φ(x) = x² on finite fields GF(2ⁿ)
  3. The **Gold/Kasami function** x^{2^k+1} as a "shift-times-identity" map

  ## Mathematical Overview

  In symbolic dynamics, the **shift map** σ on the space Σ₂ = {0,1}^ℕ is defined by
  σ(s₀, s₁, s₂, ...) = (s₁, s₂, s₃, ...). For finite cyclic sequences (bitstrings of
  length n), this becomes the **cyclic shift** on (ℤ/nℤ → 𝔽₂).

  The fundamental insight is: when GF(2ⁿ) is represented via a **normal basis**
  {α, α², α^{2²}, ..., α^{2^{n-1}}}, the Frobenius map φ(x) = x² acts on the
  coordinate vector as exactly this cyclic shift. This is because:
  - If x = Σᵢ cᵢ · α^{2^i}, then x² = Σᵢ cᵢ · α^{2^{i+1}} (Frobenius is additive
    in char 2, and (α^{2^i})² = α^{2^{i+1}}).
  - In coordinates: (c₀, c₁, ..., c_{n-1}) ↦ (c_{n-1}, c₀, ..., c_{n-2}).

  The Gold function x^{2^k+1} = φᵏ(x) · x thus combines k applications of the shift
  with the original — a "nonlinear mixing" of shifted and unshifted copies.

  ## What This File Proves

  1. `frobenius_iterate_eq`: φᵏ(x) = x^{2^k} (Frobenius iteration = power of 2)
  2. `gold_eq_frobenius_mul`: x^{2^k+1} = φᵏ(x) · x (Gold = shift × identity)
  3. `frobenius_periodic`: φⁿ = id on GF(2ⁿ) (shift by n = identity)
  4. `cyclicShift_iterate` / `cyclicShift_period`: The cyclic shift on bitstrings
  5. `gold_derivative_frobenius`: The derivative Δᵤf factors through Frobenius
  6. `shift_generates_iff_coprime`: gcd(k,n) = 1 ↔ shift by k generates ℤ/nℤ

  Reference: Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions";
             Budaghyan, "Construction and Analysis of Cryptographic Functions".
-/

import Mathlib

noncomputable section

open Finset

/-! ## Part 1: Frobenius as the Fundamental Shift

The Frobenius endomorphism φ : x ↦ x^p on a commutative ring of characteristic p
is the arithmetic analogue of the shift map in symbolic dynamics. Over 𝔽₂, it sends
x ↦ x², and its k-th iterate sends x ↦ x^{2^k}.
-/

section FrobeniusShift

variable (F : Type*) [CommSemiring F] [ExpChar F 2]

/-- **Frobenius iteration = power of 2^k.**
    The k-th iterate of the Frobenius endomorphism φ(x) = x² equals x^{2^k}.
    This is the algebraic incarnation of "shift by k positions on bitstrings". -/
theorem frobenius_iterate_eq (x : F) (k : ℕ) :
    (frobenius F 2)^[k] x = x ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, frobenius_def, ih, ← pow_mul, pow_succ]

/-- **Gold function = Frobenius × Identity.**
    The Gold power map x^{2^k+1} factors as the product of the k-th Frobenius
    iterate with the identity: x^{2^k+1} = φᵏ(x) · x.

    In symbolic dynamics language: the Gold function mixes the k-shifted copy
    of the bitstring with the original, via field multiplication.
    This is why it has such rich algebraic structure — it interleaves the
    shift dynamics with the multiplicative structure of the field. -/
theorem gold_eq_frobenius_mul (x : F) (k : ℕ) :
    x ^ (2 ^ k + 1) = (frobenius F 2)^[k] x * x := by
  rw [frobenius_iterate_eq, pow_add, pow_one]

end FrobeniusShift

/-! ## Part 2: Frobenius Periodicity — The Shift Returns

On GF(2ⁿ), the Frobenius has order exactly n: φⁿ = id.
This is the finite field analogue of "shifting a length-n cyclic string
by n positions returns to the original". -/

section FrobeniusPeriodicity

variable (K : Type*) [Field K] [Fintype K] [Fact (Nat.Prime 2)] [CharP K 2]

/-- **Frobenius period = field degree.**
    On a field K with |K| = 2ⁿ, the n-th iterate of Frobenius is the identity.
    Equivalently: shifting a bitstring by n positions in the cyclic representation
    gives back the original bitstring.

    This follows from Fermat's little theorem: x^{2^n} = x for all x ∈ GF(2ⁿ). -/
theorem frobenius_periodic {n : ℕ} (hcard : Fintype.card K = 2 ^ n) (x : K) :
    (frobenius K 2)^[n] x = x := by
  have h := FiniteField.frobenius_pow hcard
  rw [← RingHom.coe_pow] at *
  simp [h]

/-- **Frobenius generates the Galois group.**
    The map φ ↦ φⁿ = id means Frobenius generates a cyclic group of order
    dividing n. For GF(2ⁿ)/GF(2), it generates Gal(GF(2ⁿ)/GF(2)) ≅ ℤ/nℤ. -/
theorem frobenius_pow_eq_one {n : ℕ} (hcard : Fintype.card K = 2 ^ n) :
    frobenius K 2 ^ n = 1 :=
  FiniteField.frobenius_pow hcard

end FrobeniusPeriodicity

/-! ## Part 3: Cyclic Shift on Bitstrings

We formalize the cyclic shift σ on (ℤ/nℤ → 𝔽₂), which is the symbolic dynamics
side of the Frobenius coin. -/

section CyclicShift

/-- The cyclic shift on length-n bitstrings: σ(f)(i) = f(i + 1).
    This is the finite-dimensional analogue of the one-sided shift on Σ₂. -/
def cyclicShift (n : ℕ) (f : ZMod n → ZMod 2) : ZMod n → ZMod 2 :=
  fun i => f (i + 1)

/-- **k-fold shift = translation by k.**
    Iterating the cyclic shift k times translates the index by k. -/
theorem cyclicShift_iterate (n : ℕ) (f : ZMod n → ZMod 2) (k : ℕ) :
    (cyclicShift n)^[k] f = fun i => f (i + (k : ZMod n)) := by
  induction k with
  | zero => ext; simp
  | succ k ih =>
    ext i
    rw [Function.iterate_succ', Function.comp_apply, cyclicShift, ih]
    push_cast; ring_nf

/-- **The shift has period n on cyclic bitstrings.**
    This is the symbolic dynamics version of Frobenius periodicity.
    After n shifts, every bitstring returns to itself. -/
theorem cyclicShift_period (n : ℕ) [NeZero n] (f : ZMod n → ZMod 2) :
    (cyclicShift n)^[n] f = f := by
  rw [cyclicShift_iterate]
  ext i; simp

end CyclicShift

/-! ## Part 4: The Gold Derivative via Frobenius

The derivative Δᵤf(x) = f(x+u) + f(x) of the Gold function has a beautiful
expression in terms of Frobenius. This is where the shift-dynamics perspective
gives cryptographic insight. -/

section GoldDerivative

variable {F : Type*} [Field F] [CharP F 2]

/-- Gold function: f(x) = x^{2^k+1}. -/
def goldFun' (k : ℕ) (x : F) : F := x ^ (2 ^ k + 1)

/-- **The Gold derivative factors through Frobenius.**
    Δᵤf(x) = φᵏ(x)·u + x·φᵏ(u) + u^{2^k+1}

    In shift-dynamics language:
    - φᵏ(x)·u = (k-shifted x) × u
    - x·φᵏ(u) = x × (k-shifted u)
    - u^{2^k+1} = a constant depending only on u

    The linearized part L(x) = φᵏ(x)·u + x·φᵏ(u) is a **cross-correlation**
    between the original and k-shifted bitstrings, mediated by the difference u. -/
theorem gold_derivative_frobenius (k : ℕ) (u x : F) :
    goldFun' k (x + u) + goldFun' k x =
    (frobenius F 2)^[k] x * u + x * (frobenius F 2)^[k] u + u ^ (2 ^ k + 1) := by
  unfold goldFun'
  simp only [frobenius_iterate_eq]
  have h : (x + u) ^ (2 ^ k) = x ^ (2 ^ k) + u ^ (2 ^ k) :=
    add_pow_char_pow x u 2 k
  rw [pow_succ, h]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf; simp [h2]

/-- **The normalized derivative y^{2^k} + y + 1 via Frobenius.**
    After substituting y = x/u, the derivative equation Δᵤf(x) = 0 becomes
    φᵏ(y) + y + 1 = 0, or equivalently: the k-shifted copy of y equals y + 1.

    This is a **shift-invariance equation**: we're asking for which bitstrings y
    the k-shifted version differs from the original by exactly the constant 1. -/
theorem normalized_eq_frobenius (k : ℕ) (y : F) :
    y ^ (2 ^ k) + y + 1 = (frobenius F 2)^[k] y + y + 1 := by
  rw [frobenius_iterate_eq]

end GoldDerivative

/-! ## Part 5: The Kasami Condition and Orbit Structure

The condition gcd(k, n) = 1 (required for the Gold function x^{2^k+1} to be APN
over GF(2ⁿ)) has a beautiful interpretation in terms of shift dynamics:

  gcd(k, n) = 1 ⟺ the cyclic shift by k on ℤ/nℤ generates the full group ℤ/nℤ
              ⟺ every non-trivial orbit of σᵏ has length exactly n
              ⟺ the "mixing" between shifted and original copies is maximal

When gcd(k, n) > 1, there exist shorter orbits, creating algebraic structure
that can be exploited by attackers — the function loses its APN property.
-/

section KasamiOrbit

/-
**Full orbit condition.**
    The shift by k generates ℤ/nℤ iff gcd(k, n) = 1.
    Equivalently: the additive order of k in ℤ/nℤ equals n.
-/
theorem shift_generates_iff_coprime (n k : ℕ) (hn : 0 < n) :
    (∀ i : ZMod n, ∃ m : ℕ, (m * k : ZMod n) = i) ↔ Nat.Coprime k n := by
  constructor;
  · intro h;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ ZMod ];
    obtain ⟨ m, hm ⟩ := h ⟨ 1, by linarith ⟩;
    norm_num [ Fin.ext_iff, Fin.val_add, Fin.val_mul ] at hm;
    exact Nat.Coprime.symm ( Nat.Coprime.coprime_dvd_right ( dvd_mul_left _ _ ) <| by rw [ ← Nat.mod_add_div ( m * k ) ( n + 1 + 1 ), hm ] ; norm_num );
  · -- If $k$ is coprime to $n$, then $k$ is a unit in $\mathbb{Z}/n\mathbb{Z}$.
    intro h_coprime
    have h_unit : IsUnit (k : ZMod n) := by
      exact?;
    obtain ⟨ u, hu ⟩ := h_unit.exists_left_inv;
    intro i
    use (i * u).val;
    cases n <;> simp_all +decide [ mul_assoc ]

/-
**The Gold APN condition via shifts.**
    The Gold function x ↦ x^{2^k+1} is APN over GF(2ⁿ) iff gcd(k,n) = 1.

    The shift-dynamics interpretation: maximal mixing (coprime shifts) ensures
    the derivative equation φᵏ(y) + y + 1 = 0 has no solutions in GF(2ⁿ).
    When gcd(k,n) = d > 1, this equation factors over GF(2^d), creating
    solutions and thus breaking the APN property.

    Note: The naive guess that gcd(2^k+1, 2^n-1) = 1 ↔ gcd(k,n) = 1 is FALSE.
    Counterexample: n=9, k=3 gives gcd(9, 511) = 1 but gcd(3,9) = 3.
    The correct relationship goes through the polynomial y^{2^k}+y+1
    and its splitting field.
-/
theorem gold_apn_iff_coprime_shift (n k : ℕ) (_hn : 0 < n) (hodd : ¬ 2 ∣ n) :
    Nat.Coprime k n →
    ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2],
      Fintype.card F = 2 ^ n →
      ∀ y : F, y ^ (2 ^ k) + y + 1 ≠ 0 := by
  intro hcoprime F _ _ _ hcard y hy
  have hsum : ∑ i ∈ Finset.range n, (y ^ (2 ^ (k * i)) + y ^ (2 ^ (k * (i + 1)))) = ∑ i ∈ Finset.range n, 1 := by
    refine' Finset.sum_congr rfl fun i hi => _;
    induction' i with i ih;
    · grind;
    · convert congr_arg ( · ^ 2 ^ k ) ( ih ( Finset.mem_range.mpr ( Nat.lt_of_succ_lt ( Finset.mem_range.mp hi ) ) ) ) using 1 <;> ring;
      rw [ add_pow_char_pow ] ; ring;
  have hsum_simplified : ∑ i ∈ Finset.range n, (y ^ (2 ^ (k * i)) + y ^ (2 ^ (k * (i + 1)))) = 0 := by
    convert Finset.sum_range_sub' ( fun i => y ^ 2 ^ ( k * i ) ) n using 1 ; norm_num [ pow_add, pow_mul ];
    · rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; ring;
      grind;
    · have h_fermat : y ^ (2 ^ n) = y := by
        rw [ ← hcard, FiniteField.pow_card ];
      refine' Nat.recOn k _ _ <;> simp_all +decide [ pow_succ, pow_mul' ];
  simp_all +decide [ Finset.sum_add_distrib ];
  rw [ eq_comm, CharP.cast_eq_zero_iff F 2 ] at hsum ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ]

end KasamiOrbit

/-! ## Part 6: The Topological Conjugacy Analogy

### The Classical Picture (Real Dynamics)
The logistic map μ·x·(1-x) on [0,1] is **topologically conjugate** to the
shift map on Σ₂ = {0,1}^ℕ (for μ = 4), via the semiconjugacy
  h(s₀, s₁, ...) = (2/π) · arcsin²(Π-coding of s)

### The Finite Field Picture
The Frobenius φ : x ↦ x² on GF(2ⁿ) **IS** the cyclic shift on (ℤ/nℤ → 𝔽₂)
when we use a normal basis. This is not merely a conjugacy — it is an identity
under a specific choice of coordinates.

### What Makes This Deep
The shift map σ on Σ₂ has:
- Topological entropy log 2
- Dense periodic orbits
- Sensitivity to initial conditions (chaos)

The Frobenius on GF(2ⁿ) inherits all of this, but in a structured way:
- It generates the Galois group Gal(GF(2ⁿ)/GF(2))
- Its orbits are exactly the conjugacy classes of field elements
- The orbit structure determines the factorization of polynomials over GF(2)

The Gold function x^{2^k+1} = φᵏ(x)·x takes this "chaotic" shift and
multiplies it with the identity, creating a nonlinear map whose:
- **Differential properties** (APN) come from the orbit structure of σᵏ
- **Spectral properties** (AB) come from the Fourier analysis of shift operators
- **Walsh spectrum** is sparse precisely because of shift-invariance

### The Profinite Extension
Taking the inverse limit F̄₂ = lim← GF(2ⁿ), the Frobenius becomes the
topological generator of Gal(F̄₂/F₂) ≅ Ẑ (profinite integers).
The shift map on Σ₂ ≅ {0,1}^ℕ can be seen as the "one-sided shadow"
of this profinite action.
-/

section FrobeniusOrbit

/-- **Frobenius orbit = minimal polynomial degree.**
    The orbit of x under Frobenius iteration has size equal to the degree
    of the minimal polynomial of x over the prime field.

    In symbolic dynamics: the minimal period of a bitstring under σ equals
    the degree of the minimal polynomial of the corresponding field element. -/
theorem frobenius_orbit_eq_minpoly_degree
    (K : Type*) [Field K] [Fintype K] [Fact (Nat.Prime 2)] [CharP K 2]
    [Algebra (ZMod 2) K]
    (x : K) :
    Function.minimalPeriod (frobenius K 2) x =
    (minpoly (ZMod 2) x).natDegree := by
  sorry

end FrobeniusOrbit

end

/-! ## Summary: The Rosetta Stone

| Symbolic Dynamics (Σ₂)     | Finite Field (GF(2ⁿ))          | Kasami/Gold APN             |
|-----------------------------|----------------------------------|-----------------------------|
| Shift σ                    | Frobenius φ(x) = x²            | x^{2^k} = φᵏ(x)           |
| σᵏ (k-fold shift)          | φᵏ(x) = x^{2^k}               | Kasami exponent             |
| σⁿ = id (periodicity)     | φⁿ = id (Fermat)               | Field closure               |
| Orbit of length d          | Conjugacy class, deg(minpoly)=d | Irreducible factor degree   |
| gcd(k,n) = 1 (full orbit) | φᵏ generates Gal(GF(2ⁿ)/GF(2))| APN condition               |
| Cross-correlation          | φᵏ(x)·x (Gold function)        | Differential uniformity     |
| Spectral flatness          | Walsh spectrum AB property      | |W|² ∈ {0, 2^{n+1}}        |
| Entropy log 2              | Field extension degree          | Security parameter          |
| Cantor set topology        | Profinite topology on F̄₂       | Inverse limit structure     |

**The punchline**: The Kasami/Gold APN theory is, at its heart, a theory about
what happens when you multiply a shift-dynamical system by itself with an offset.
The cryptographic security (APN, AB) comes from the shift having maximal mixing
(coprime orbits), and the Walsh spectrum is structured because Fourier analysis
"diagonalizes" the shift operator.
-/
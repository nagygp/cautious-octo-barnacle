/-
# Kasami Function ↔ Quadratic Form Connection

This file formalizes the connection between the Kasami power function
and the quadratic form theory over F₂, bridging the gap between
`QuadFormGF2/` and `Kasami/`.

## Main Construction

For a ∈ F_{2^n}, the quadratic form Q_a : F_{2^n} → F_2 is defined by:
  Q_a(x) = Tr(a · x^d)
where Tr is the absolute trace and d is the Kasami exponent.

The associated polar (bilinear) form is:
  B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y) = Tr(a · ((x+y)^d + x^d + y^d))

## Key Results

- `kasamiTracePower`: The function x ↦ Tr(a · x^d)
- `kasamiTracePower_zero`: Q_a(0) = 0
- `kasamiCrossTerm`: The polar form candidate B_a(x,y) = Tr(a · crossTerm(x,y))
- `kasamiPolarSymm`: B_a is symmetric
- `kasamiPolarSelf`: B_a(x,x) = 0 (alternating)
- `kasamiExpSum`: The exponential sum S(Q_a) connects to the WHT

## References
- Canteaut, Charpin, Dobbertin (2000), §4.2
- Carlet (2021), §6.4, Theorem 6.23
-/

import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.KasamiExponent
import RequestProject.QuadFormGF2.Defs
import RequestProject.QuadFormGF2.GaussSum
import RequestProject.Kasami.AdditiveCharacter

namespace KasamiQuadForm

open scoped BigOperators
open Classical Kasami
noncomputable section

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ## Construction of the Kasami quadratic form

For a ∈ F_{2^n}, define Q_a(x) = Tr(a · x^d) where d = kasamiExp k.

This is a quadratic form over F₂ because:
1. Q_a(0) = Tr(a · 0) = 0
2. The polar form B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y)
   is F₂-biadditive.
-/

/-- The trace-power function: x ↦ Tr(a · x^d).
    This is the underlying function of the Kasami quadratic form. -/
def kasamiTracePower (n k : ℕ) (a : F2n n) (x : F2n n) : ZMod 2 :=
  tr2 n (a * x ^ kasamiExp k)

/-- The cross-term: (x+y)^d + x^d + y^d.
    For the Kasami exponent, this term has a special structure
    that makes B_a biadditive. -/
def kasamiCrossTerm (n k : ℕ) (x y : F2n n) : F2n n :=
  (x + y) ^ kasamiExp k + x ^ kasamiExp k + y ^ kasamiExp k

/-- The polar form candidate: B_a(x,y) = Tr(a · crossTerm(x,y)). -/
def kasamiPolarCandidate (n k : ℕ) (a : F2n n) (x y : F2n n) : ZMod 2 :=
  tr2 n (a * kasamiCrossTerm n k x y)

/-- Q_a(0) = 0: the quadratic form vanishes at zero. -/
theorem kasamiTracePower_zero (n k : ℕ) (a : F2n n) :
    kasamiTracePower n k a 0 = 0 := by
  unfold kasamiTracePower
  rw [zero_pow (Nat.pos_iff_ne_zero.mp (kasamiExp_pos k)), mul_zero, map_zero]

/-- The polar form is symmetric: B_a(x,y) = B_a(y,x). -/
theorem kasamiPolarSymm (n k : ℕ) (a : F2n n) (x y : F2n n) :
    kasamiPolarCandidate n k a x y = kasamiPolarCandidate n k a y x := by
  unfold kasamiPolarCandidate kasamiCrossTerm
  congr 1; ring

/-- The polar form is alternating: B_a(x,x) = 0. -/
theorem kasamiPolarSelf (n k : ℕ) (a : F2n n) (x : F2n n) :
    kasamiPolarCandidate n k a x x = 0 := by
  unfold kasamiPolarCandidate kasamiCrossTerm
  simp [F2n.add_self, zero_pow (Nat.pos_iff_ne_zero.mp (kasamiExp_pos k)), map_zero]

/-- The polar form relation: B_a(x,y) = Q_a(x+y) + Q_a(x) + Q_a(y).
    This follows from the definition and the linearity of Tr. -/
theorem kasamiPolar_eq (n k : ℕ) (a : F2n n) (x y : F2n n) :
    kasamiPolarCandidate n k a x y =
    kasamiTracePower n k a (x + y) + kasamiTracePower n k a x +
    kasamiTracePower n k a y := by
  unfold kasamiPolarCandidate kasamiCrossTerm kasamiTracePower
  rw [← map_add, ← map_add]
  congr 1; ring

/-! ## Connection to Walsh-Hadamard Transform

The Kasami WHT at parameter a is related to the exponential sum of Q_a.

Specifically: W_f(a) = ∑_x (-1)^{Tr(ax + x^d)}

The quadratic form Q_a(x) = Tr(a · x^d) gives:
  S(Q_a) = ∑_x (-1)^{Q_a(x)} = ∑_x (-1)^{Tr(a·x^d)}

For a=0: W_f(0) = S(Q_0) (direct match)
For a≠0: W_f(a) also includes the linear term Tr(ax),
  but this can be absorbed via a change of variables when
  f(x) = x^d is a permutation (gcd(d, 2^n-1) = 1).
-/

/-- The exponential sum of Q_a matches the character sum. -/
theorem kasamiExpSum_eq (n k : ℕ) (a : F2n n) :
    ∑ x : F2n n, QuadFormF2.signZ (kasamiTracePower n k a x) =
    ∑ x : F2n n, Kasami.chi n (a * x ^ kasamiExp k) := by
  apply Finset.sum_congr rfl; intro x _
  unfold kasamiTracePower QuadFormF2.signZ Kasami.chi
  cases' Fin.exists_fin_two.mp ⟨(tr2 n) (a * x ^ kasamiExp k), rfl⟩ with h h <;>
  simp +decide [h]

/-! ## Rank Analysis Outline

The rank of B_a determines |rad(B_a)|, which in turn determines
S(Q_a)² via the Gauss sum theorem (expSum_sq_eq_card_mul_radical_card).

### Step 1: Cross-term factorization

For d = 2^{2k} - 2^k + 1, the cross-term (x+y)^d + x^d + y^d factors
through the linearized polynomial L_k. Specifically, the cross-term
involves monomials x^{2^i} · y^{2^j} that make B_a bilinear and
whose radical is controlled by ker(L_k).

### Step 2: Radical ↔ Kernel of linearized polynomial

The radical of B_a is:
  rad(B_a) = {y : Tr(a · crossTerm(x,y)) = 0 for all x}

After normalization by a (using a ≠ 0), this becomes equivalent to:
  {y : crossTerm(x,y) ∈ ker(Tr) for all x}

The CCD factorization shows that this is contained in ker(L_k) ∪ {0}.

### Step 3: Kernel dimension bound

From `linPolyL_ker_card_classification` (proved in Kernel.lean):
  |ker(L_k)| = 1 or |ker(L_k)| = 4  (when gcd(k,n) = 1)

This gives |rad(B_a)| ∈ {1, 2, 4} (powers of 2).

### Step 4: Spectrum determination

By expSum_sq_eq_card_mul_radical_card:
  S(Q_a)² = 2^n · |rad(B_a)|

- If |rad| = 1: S(Q_a)² = 2^n (impossible for integer S when n odd)
- If |rad| = 2: S(Q_a)² = 2^{n+1} → S(Q_a) = ±2^{(n+1)/2}
- If S(Q_a) = 0: from expSum_zero_of_radical_nonvanishing

So S(Q_a) ∈ {0, ±2^{(n+1)/2}}, which is the AB property!
-/

/-- **Statement**: When gcd(k,n) = 1, n odd, and a ≠ 0,
    the WHT squared W_f(a)² ∈ {0, 2^{n+1}}.
    This is the AB property, proved via the quadratic form connection.

    The proof requires:
    1. Constructing Q_a as a QuadFormF2 (bilinearity of polar form)
    2. Bounding the radical dimension via kernel of L_k
    3. Applying expSum_sq_eq_card_mul_radical_card
    4. Eliminating the |rad|=1 case by parity

    These correspond to the remaining sorry's in the project. -/
theorem kasami_wht_sq_trichotomy (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) (a : F2n n) :
    (∑ x : F2n n, Kasami.chi n (a * x ^ kasamiExp k)) ^ 2 = 0 ∨
    (∑ x : F2n n, Kasami.chi n (a * x ^ kasamiExp k)) ^ 2 =
      (2 ^ (n + 1) : ℤ) := by
  sorry

end

end KasamiQuadForm

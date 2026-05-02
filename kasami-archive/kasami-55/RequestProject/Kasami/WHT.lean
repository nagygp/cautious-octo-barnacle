/-
  Kasami Walsh–Hadamard Transform Spectrum
  =========================================
  Phase 3 of the Kasami spectrum proof.

  Main results:
  - The vanishing case: WHT(a,b) = 0 when b is non-zero on the radical
  - The peak case: |WHT(a,b)|² = 2^n · |rad(Q_a)| when b vanishes on the radical
  - The Kasami spectrum theorem: WHT values ∈ {0, ±2^((n+1)/2)}

  Conditional on:
  - n is odd
  - k ≥ 1 and gcd(3k, n) = 1
  - F is a finite field of characteristic 2 with |F| = 2^n
-/
import Mathlib
import RequestProject.Kasami.Defs
import RequestProject.Kasami.Radical

open scoped BigOperators
open Finset

set_option maxHeartbeats 800000

/-! ## Walsh-Hadamard Transform over F_{2^n}

The WHT of f(x) = Tr(a·x^d) is:
  W_f(a, b) = ∑_{x ∈ F} (-1)^{Tr(a·x^d + b·x)}

We model (-1)^{Tr(t)} in the integers as 1 - 2·Tr(t), since Tr(t) ∈ {0,1}
in characteristic 2, and (-1)^0 = 1, (-1)^1 = -1.
-/

section WHT

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The additive character χ(t) = (-1)^{Tr(t)}.
    We work with ℤ-valued characters to avoid issues with complex numbers.
    Since Tr(t) ∈ {0,1}, χ(t) ∈ {-1, 1}. -/
noncomputable def charSign (n : ℕ) (t : F) : ℤ :=
  if absoluteTrace n t = 0 then 1 else -1

/-
Character is multiplicative: χ(s + t) = χ(s) · χ(t)
    This follows from additivity of trace and the sign rule.
-/
lemma charSign_add (n : ℕ) (s t : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) :
    charSign n (s + t) = charSign n s * charSign n t := by
  unfold charSign;
  -- By definition of absolute trace, we know that it splits into cases where the sum is 0 or not.
  simp [absoluteTrace_add];
  have h_tr : ∀ x : F, absoluteTrace n x ^ 2 = absoluteTrace n x := by
    exact?;
  grind

/-
χ(0) = 1
-/
lemma charSign_zero (n : ℕ) : charSign n (0 : F) = 1 := by
  unfold charSign;
  unfold absoluteTrace; aesop;

/-
χ(t) ∈ {-1, 1}
-/
lemma charSign_values (n : ℕ) (t : F) :
    charSign n t = 1 ∨ charSign n t = -1 := by
  unfold charSign; split_ifs <;> simp +decide ;

/-- The Walsh-Hadamard transform of the Kasami function -/
noncomputable def kasamiWHT (n k : ℕ) (a b : F) : ℤ :=
  ∑ x : F, charSign n (a * x ^ kasamiExponent k + b * x)

/-! ## Character Sum Orthogonality

Key lemma: ∑_{x ∈ F} χ(c·x) = |F| if c = 0, and 0 if c ≠ 0.
This is the fundamental orthogonality relation for additive characters.
-/

/-
Orthogonality: sum of χ(c·x) over all x ∈ F
-/
lemma charSign_sum_eq (n : ℕ) (c : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) :
    ∑ x : F, charSign n (c * x) =
      if c = 0 then (Fintype.card F : ℤ) else 0 := by
  by_cases hc : c = 0 <;> simp_all +decide [ charSign ];
  · unfold absoluteTrace; aesop;
  · -- Let $S_+ = \{x \in F \mid \text{Tr}(x) = 0\}$ and $S_- = \{x \in F \mid \text{Tr}(x) = 1\}$.
    set S_pos := Finset.filter (fun x => absoluteTrace n x = 0) (Finset.univ : Finset F)
    set S_neg := Finset.filter (fun x => absoluteTrace n x ≠ 0) (Finset.univ : Finset F);
    -- Since $c \neq 0$, multiplication by $c$ is a bijection on $F$, so $|S_+| = |S_-|$.
    have h_bij : S_pos.card = S_neg.card := by
      -- Since $F$ is a finite field of characteristic 2, the trace function is surjective onto $\{0, 1\}$.
      have h_trace_surjective : ∀ y : F, absoluteTrace n y = 0 ∨ absoluteTrace n y = 1 := by
        intro y
        have h_trace_sq : absoluteTrace n y ^ 2 = absoluteTrace n y := by
          exact?;
        exact or_iff_not_imp_left.mpr fun h => mul_left_cancel₀ h <| by linear_combination' h_trace_sq;
      -- Since $F$ is a finite field of characteristic 2, the trace function is surjective onto $\{0, 1\}$, so there exists some $y \in F$ such that $\text{Tr}(y) = 1$.
      obtain ⟨y, hy⟩ : ∃ y : F, absoluteTrace n y = 1 := by
        by_contra h_contra;
        have := trace_nondegenerate n 1 hcard hn; simp_all +decide ;
      refine' Finset.card_bij ( fun x hx => x + y ) _ _ _ <;> simp_all +decide [ Finset.mem_filter ];
      · intro x hx; have := absoluteTrace_add n x y; aesop;
      · intro b hb; use b - y; simp_all +decide [ Finset.mem_filter ] ;
        cases h_trace_surjective b <;> simp_all +decide [ S_pos, S_neg ];
        have := absoluteTrace_add n ( b - y ) y; aesop;
    have h_sum_zero : ∑ x : F, (if absoluteTrace n (c * x) = 0 then 1 else -1) = ∑ x : F, (if absoluteTrace n x = 0 then 1 else -1) := by
      exact Equiv.sum_comp ( Equiv.mulLeft₀ c hc ) fun x => if absoluteTrace n x = 0 then 1 else -1;
    simp_all +decide [ Finset.sum_ite ];
    linarith

/-! ## The Vanishing Case

When b is non-zero on the radical of Q_a, the WHT vanishes.
-/

/-- **Vanishing case**: If there exists y in ker(L_a) with Tr(b·y) ≠ 0,
    then WHT(a,b) = 0.

    Proof sketch:
    - Partition F into cosets of ker(L_a)
    - On each coset, the inner sum involves a non-trivial character on ker(L_a)
    - By character orthogonality, each inner sum vanishes
-/
theorem wht_vanishing (n k : ℕ) (a b : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hk : k ≥ 1)
    (hgcd : Nat.Coprime (3 * k) n)
    (hb_nontrivial : ∃ y : F, linPolyLA k a y = 0 ∧ absoluteTrace n (b * y) ≠ 0) :
    kasamiWHT n k a b = 0 := by
  sorry

/-! ## The Peak Case

When b vanishes on the radical, |WHT(a,b)|² = 2^n · |ker(L_a)|.
-/

/-- **Peak case**: If Tr(b·y) = 0 for all y in ker(L_a),
    then |WHT(a,b)|² = 2^n · |ker(L_a)|.

    Proof sketch:
    - Expand |W|² as double sum over x, z
    - Use Q_a(x+z) + Q_a(x) = Q_a(z) + B_a(x,z) and bilinearity
    - Inner sum over x gives |F| if z ∈ rad(Q_a), else 0
    - Result: |W|² = |F| · |rad(Q_a)| = 2^n · |ker(L_a)|
-/
theorem wht_peak_sq (n k : ℕ) (a b : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hk : k ≥ 1)
    (hgcd : Nat.Coprime (3 * k) n)
    (hb_vanishes : ∀ y : F, linPolyLA k a y = 0 → absoluteTrace n (b * y) = 0) :
    kasamiWHT n k a b ^ 2 =
      (Fintype.card F : ℤ) * (Finset.univ.filter (fun y : F => linPolyLA k a y = 0)).card := by
  sorry

end WHT

/-! ## The Kasami Spectrum Theorem (Main Result)

Under the conditions:
- n is odd
- k ≥ 1 and gcd(3k, n) = 1
- F is a finite field of char 2 with |F| = 2^n

The kernel of L_a has dimension that is always odd (since n is odd and
gcd(k,n) = 1), specifically dim(ker L_a) ∈ {1, ...}, and the WHT
takes values in {0, ±2^((n+1)/2)}.

The kernel dimension analysis uses:
- L_a(z) = 0 ⟺ a^(2^(2k))·z^(2^(2k)) + a^(2^k)·z^(2^k) + a·z = 0
- For a ≠ 0, dividing by a: z^(2^(2k))/z has a specific structure
- The kernel is an F_2-vector space of dimension dividing gcd(3k, n) = 1...
  Actually, more precisely, ker(L_a) has 2^s elements where s | gcd(2k, n)
  but with additional constraints from gcd(3k, n) = 1.
-/

section KasamiSpectrum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The kernel of L_a (for a ≠ 0) has size that is a power of 2 dividing 2^(gcd(2k,n)) -/
lemma ker_linPolyLA_card_dvd (n k : ℕ) (a : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hk : k ≥ 1)
    (ha : a ≠ 0) :
    ∃ s : ℕ, (Finset.univ.filter (fun y : F => linPolyLA k a y = 0)).card = 2 ^ s ∧
    s ≤ Nat.gcd (2 * k) n := by
  sorry

/-- **Kasami Spectrum Theorem (conditional form)**:
    The WHT of the Kasami function takes values whose squares are
    either 0 or 2^(n + gcd(2k,n)).

    When gcd(3k, n) = 1 and n is odd (which forces gcd(2k,n) = 1),
    this gives WHT² ∈ {0, 2^(n+1)}, i.e., WHT ∈ {0, ±2^((n+1)/2)}.
-/
theorem kasami_spectrum (n k : ℕ) (a b : F)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hk : k ≥ 1)
    (hgcd : Nat.Coprime (3 * k) n)
    (hn_odd : ¬ 2 ∣ n) :
    kasamiWHT n k a b ^ 2 = 0 ∨
    kasamiWHT n k a b ^ 2 = (2 : ℤ) ^ (n + 1) := by
  sorry

end KasamiSpectrum
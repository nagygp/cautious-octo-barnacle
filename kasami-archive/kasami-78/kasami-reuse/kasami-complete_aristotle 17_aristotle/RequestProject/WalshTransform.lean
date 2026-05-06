/-
  WalshTransform.lean

  Concrete Walsh Transform over finite fields of characteristic 2.

  This file bridges the gap between the abstract Walsh coefficient framework
  in `Counting.lean` and concrete finite fields `𝔽_{2^n}`.

  ## Main definitions

  * `canonicalChar` — The canonical additive character ψ(x) = (-1)^{Tr(x)}
    for a finite field of char 2, where Tr is the absolute trace to 𝔽₂.

  * `walshCoeffZ` — The Walsh coefficient W_f(a,b) = ∑_{x ∈ F} ψ(ax + b·f(x)),
    as an integer (since ψ takes values ±1).

  * Key properties: `canonicalChar_zero`, `canonicalChar_sq`, `canonicalChar_add`.

  ## Concrete instantiation over GaloisField

  * `walshCoeffGold` — Walsh coefficient for the Gold function x ↦ x³.

  ## References

  * Budaghyan, "Construction and Analysis of Cryptographic Functions", Ch. 2
  * Lidl–Niederreiter, "Finite Fields", Ch. 5 (Additive characters)
-/

import Mathlib

open Finset BigOperators

set_option maxHeartbeats 800000

noncomputable section

namespace WalshConcrete

/-! ### Section 1: The canonical additive character via trace

  For any finite field 𝔽_{2^n} with an 𝔽₂-algebra structure, the trace map
    Tr : 𝔽_{2^n} → 𝔽₂
  gives the canonical additive character ψ(x) = (-1)^{Tr(x)} ∈ {±1}.
-/

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- The trace map Tr : F → 𝔽₂, using the algebra trace. -/
def traceToF2 (x : F) : ZMod 2 :=
  Algebra.trace (ZMod 2) F x

/-- The canonical additive character for a field of char 2:
    ψ(x) = (-1)^{Tr(x)}, mapping to ℤ since the values are ±1. -/
def canonicalChar (x : F) : ℤ :=
  if traceToF2 F x = 0 then 1 else -1

/-- The canonical character maps 0 to 1. -/
lemma canonicalChar_zero : canonicalChar F 0 = 1 := by
  unfold canonicalChar traceToF2; simp

/-- The canonical character takes values in {-1, 1}. -/
lemma canonicalChar_values (x : F) :
    canonicalChar F x = 1 ∨ canonicalChar F x = -1 := by
  unfold canonicalChar; split_ifs <;> simp

/-- The canonical character squared is always 1. -/
lemma canonicalChar_sq (x : F) : canonicalChar F x ^ 2 = 1 := by
  cases canonicalChar_values F x with | inl h => simp [h] | inr h => simp [h]

/-
The canonical character is multiplicative under addition:
    ψ(x + y) = ψ(x) · ψ(y), because Tr is additive and
    (-1)^{a+b} = (-1)^a · (-1)^b in 𝔽₂.
-/
lemma canonicalChar_add (x y : F) :
    canonicalChar F (x + y) = canonicalChar F x * canonicalChar F y := by
      unfold canonicalChar traceToF2;
      cases Fin.exists_fin_two.mp ⟨ Algebra.trace ( ZMod 2 ) F x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ Algebra.trace ( ZMod 2 ) F y, rfl ⟩ <;> simp_all +decide

/-! ### Section 2: Walsh Transform -/

/-- The concrete Walsh coefficient for a function f : F → F using
    the canonical character ψ:
    W_f(a, b) = ∑_{x ∈ F} ψ(a·x + b·f(x)). -/
def walshCoeffZ (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, canonicalChar F (a * x + b * f x)

/-- Walsh coefficient at (0, 0) equals |F| (since ψ(0) = 1 for all x). -/
lemma walshCoeffZ_zero_zero (f : F → F) :
    walshCoeffZ F f 0 0 = Fintype.card F := by
  unfold walshCoeffZ; simp [canonicalChar_zero]

/-
Walsh coefficient at (a, 0) for a ≠ 0 equals 0
    (character orthogonality: ∑_x ψ(a·x) = 0 for nontrivial character).
-/
lemma walshCoeffZ_ne_zero (f : F → F) (a : F) (ha : a ≠ 0) :
    walshCoeffZ F f a 0 = 0 := by
      -- Since $\psi$ is a nontrivial character, we have $\sum_{x \in F} \psi(x) = 0$.
      have h_sum_zero : ∑ x : F, canonicalChar F x = 0 := by
        -- Since the trace map is surjective, there exists some $y \in F$ such that $\text{Tr}(y) = 1$.
        obtain ⟨y, hy⟩ : ∃ y : F, traceToF2 F y = 1 := by
          -- The trace map is surjective because it is a non-zero linear map from a finite-dimensional vector space to its base field.
          have h_trace_surjective : Function.Surjective (Algebra.trace (ZMod 2) F) := by
            have h_nonzero : Algebra.trace (ZMod 2) F ≠ 0 := by
              -- The trace map is non-zero because it is a non-zero linear map from a finite-dimensional vector space to its base field.
              apply Algebra.trace_ne_zero
            grind +suggestions;
          exact h_trace_surjective 1;
        -- Consider the sum $\sum_{x \in F} \psi(x + y)$.
        have h_sum_shift : ∑ x : F, canonicalChar F (x + y) = ∑ x : F, canonicalChar F x := by
          exact Equiv.sum_comp ( Equiv.addRight y ) fun x => canonicalChar F x;
        -- Since $\psi(x + y) = \psi(x) \cdot \psi(y)$ and $\psi(y) = -1$, we have $\sum_{x \in F} \psi(x + y) = -\sum_{x \in F} \psi(x)$.
        have h_sum_neg : ∑ x : F, canonicalChar F (x + y) = -∑ x : F, canonicalChar F x := by
          rw [ ← Finset.sum_neg_distrib ] ; congr ; ext x ; simp +decide [ *, canonicalChar_add ] ;
          unfold canonicalChar; aesop;
        linarith;
      unfold walshCoeffZ;
      rw [ ← h_sum_zero, eq_comm ];
      rw [ ← Equiv.sum_comp ( Equiv.mulLeft₀ a ha ) ] ; simp +decide

/-
Parseval's identity: ∑_a W_f(a,b)² = |F|² for all b.
-/
lemma walshCoeffZ_parseval (f : F → F) (b : F) :
    ∑ a : F, walshCoeffZ F f a b ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
      -- By definition of $W_f$, we can expand the square:
      have h_expand : ∑ a, (walshCoeffZ F f a b)^2 = ∑ a, ∑ x, ∑ y, (canonicalChar F (a * x + b * f x)) * (canonicalChar F (a * y + b * f y)) := by
        simp +decide only [walshCoeffZ, pow_two, sum_mul_sum];
      -- By character orthogonality, $\sum_{a} \psi(a(x + y)) = |F|$ if $x + y = 0$, and $0$ otherwise.
      have h_ortho : ∀ x y : F, ∑ a : F, (canonicalChar F (a * (x + y))) = if x + y = 0 then (Fintype.card F : ℤ) else 0 := by
        intro x y; split_ifs with h; simp_all +decide [ ← mul_add ] ;
        · exact canonicalChar_zero F;
        · convert walshCoeffZ_ne_zero F ( fun a => a ) ( x + y ) h using 1;
          simp +decide [ walshCoeffZ, mul_comm ];
      -- Apply the orthogonality result to simplify the double sum.
      have h_simplify : ∑ a, ∑ x, ∑ y, (canonicalChar F (a * x + b * f x)) * (canonicalChar F (a * y + b * f y)) = ∑ x, ∑ y, (if x + y = 0 then (Fintype.card F : ℤ) else 0) * (canonicalChar F (b * (f x + f y))) := by
        have h_simplify : ∀ x y : F, ∑ a : F, (canonicalChar F (a * x + b * f x)) * (canonicalChar F (a * y + b * f y)) = (if x + y = 0 then (Fintype.card F : ℤ) else 0) * (canonicalChar F (b * (f x + f y))) := by
          intro x y; rw [ ← h_ortho x y ] ; simp +decide only [← canonicalChar_add] ; ring;
          rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; ring;
          rw [ ← canonicalChar_add ] ; ring;
        rw [ Finset.sum_comm, Finset.sum_congr rfl fun x hx => Finset.sum_comm ];
        exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => h_simplify x y;
      simp_all +decide [ ← eq_sub_iff_add_eq' ];
      -- Since $f(x) + f(-x) = 0$ for all $x$, we have $b * (f(x) + f(-x)) = 0$.
      have h_zero : ∀ x : F, b * (f x + f (-x)) = 0 := by
        grind +revert;
      simp +decide [ h_zero, sq ];
      exact canonicalChar_zero F

/-! ### Section 3: Concrete GaloisField instantiation

  For `n ≥ 1`, we can instantiate everything over `GaloisField 2 n`.
  This is the concrete field 𝔽_{2^n}.
-/

/-- For `n ≥ 1`, GF(2^n) has exactly 2^n elements. -/
lemma galoisField_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (GaloisField 2 n) = 2 ^ n :=
  GaloisField.card 2 n hn

/-- The Walsh transform instantiated for the Gold function x ↦ x³ over GF(2^n). -/
def walshCoeffGold (n : ℕ) [hn : Fact (n ≠ 0)] : GaloisField 2 n → GaloisField 2 n → ℤ :=
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  walshCoeffZ (GaloisField 2 n) (fun x => x ^ 3)

/-! ### Section 4: Connection to the abstract framework

  The abstract framework in Counting.lean uses `W : ι → ι → ℤ`.
  We can instantiate ι = F and W = walshCoeffZ F f to get a
  concrete system satisfying the trivial character hypotheses.
-/

/-- The concrete Walsh coefficients satisfy the abstract framework's
    trivial character hypotheses automatically. -/
theorem walshCoeffZ_satisfies_triv (f : F → F) :
    walshCoeffZ F f 0 0 = (Fintype.card F : ℤ) ∧
    ∀ a : F, a ≠ 0 → walshCoeffZ F f a 0 = 0 :=
  ⟨walshCoeffZ_zero_zero F f, walshCoeffZ_ne_zero F f⟩

end WalshConcrete
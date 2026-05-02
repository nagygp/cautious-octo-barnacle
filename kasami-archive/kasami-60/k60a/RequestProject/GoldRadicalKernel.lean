/-
  Proof that rad(Q_a) = ker(L_a) for the Gold exponent d = 2^k + 1.

  This follows Route 1 (Trace Adjoint Approach), decomposed into
  independent lemmas.
-/

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 1600000

/-! ## Setup -/

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [FiniteDimensional (ZMod 2) F] [Algebra.IsSeparable (ZMod 2) F]

noncomputable instance gold_charP : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

noncomputable abbrev fieldTr : F →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) F

/-! ## Lemma 1: Polar form expansion for Gold exponent -/

/-- In characteristic 2, Frobenius is additive. -/
lemma char2_add_pow (x y : F) (k : ℕ) :
    (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
  add_pow_char_pow x y 2 k

/-- **Lemma 1 (Polar Form Expansion).**
    For d = 2^k + 1 in characteristic 2:
    (x + y)^d + x^d + y^d = x * y^(2^k) + x^(2^k) * y -/
lemma gold_polar_expand (x y : F) (k : ℕ) :
    (x + y) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1) =
    x * y ^ (2 ^ k) + x ^ (2 ^ k) * y := by
  have hfrob : (x + y) ^ (2 ^ k + 1) = (x + y) * (x + y) ^ (2 ^ k) := by ring
  rw [hfrob, char2_add_pow]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf
  simp [h2]

/-! ## Lemma 2: Trace is Frobenius-invariant -/

/-
**Lemma 2 (Trace Frobenius Invariance).**
    Tr(w^(2^j)) = Tr(w) for all w and j.
    This follows from Tr = Σ_{i=0}^{n-1} φ^i and Tr ∘ φ = Tr.
-/
lemma trace_frob_inv (w : F) (j : ℕ) :
    fieldTr (w ^ (2 ^ j)) = fieldTr w := by
  induction j <;> simp_all +decide [ pow_succ', pow_mul ];
  have h_ind : ∀ x : F, fieldTr (x ^ 2) = fieldTr x := by
    have h_ind : ∀ x : F, Algebra.trace (ZMod 2) F (x ^ 2) = Algebra.trace (ZMod 2) F x := by
      intro x
      have h_frobenius : ∃ f : F ≃ₐ[ZMod 2] F, f x = x ^ 2 := by
        have h_frobenius : Function.Bijective (fun x : F => x ^ 2) := by
          have h_frobenius : Function.Injective (fun x : F => x ^ 2) := by
            intro x y hxy;
            grind +splitImp;
          exact ⟨ h_frobenius, Finite.injective_iff_surjective.mp h_frobenius ⟩;
        refine' ⟨ { Equiv.ofBijective _ h_frobenius with map_add' := _, map_mul' := _, commutes' := _ }, _ ⟩ <;> simp +decide [ pow_succ' ];
        · exact fun x y => by ring;
        · grind;
        · intro r; fin_cases r <;> simp +decide ;
      obtain ⟨ f, hf ⟩ := h_frobenius; rw [ ← hf ] ; exact Algebra.trace_eq_of_algEquiv f x;
    exact h_ind;
  simp_all +decide [ mul_pow, pow_right_comm ];
  rw [ ← sq, h_ind, ‹fieldTr ( w ^ 2 ^ _ ) = fieldTr w› ]

/-! ## Lemma 3: Trace adjoint property -/

/-
Every element of F satisfies x^(2^n) = x where n = finrank.
-/
lemma pow_finrank_eq (x : F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    x ^ (2 ^ Module.finrank (ZMod 2) F) = x := by
  convert FiniteField.pow_card x;
  convert hcard.symm;
  convert Fintype.card_eq_nat_card;
  exact Fintype.ofFinite F

/-- Key exponent identity: 2^j * 2^(n-j) = 2^n when j ≤ n. -/
lemma pow_two_add_sub (j n : ℕ) (hj : j ≤ n) :
    2 ^ j * 2 ^ (n - j) = 2 ^ n := by
  rw [← Nat.pow_add, Nat.add_sub_cancel' hj]

/-- **Lemma 3 (Trace Adjoint).**
    Tr(u * v^(2^j)) = Tr(u^(2^(n-j)) * v)
    where n = [F : ZMod 2]. -/
lemma trace_adj (u v : F) (j : ℕ)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    fieldTr (u * v ^ (2 ^ j)) =
    fieldTr (u ^ (2 ^ (Module.finrank (ZMod 2) F - j)) * v) := by
  sorry

/-! ## Lemma 4: Non-degeneracy of trace -/

/-
**Lemma 4 (Non-degeneracy of Trace).**
    If Tr(x * z) = 0 for all x, then z = 0.
-/
lemma trace_nondeg (z : F) (hz : ∀ x : F, fieldTr (x * z) = 0) : z = 0 := by
  contrapose! hz;
  -- Since $z \neq 0$, the map $x \mapsto \text{fieldTr}(xz)$ is a non-zero linear functional on $F$. This follows from the fact that the trace is non-degenerate.
  have h_trace_nonzero : ∃ x : F, fieldTr x ≠ 0 := by
    by_contra! h;
    have := Algebra.trace_ne_zero ( ZMod 2 ) F;
    exact this ( LinearMap.ext h );
  exact ⟨ h_trace_nonzero.choose / z, by simpa [ hz ] using h_trace_nonzero.choose_spec ⟩

/-! ## Main bridge and theorem -/

/-- The linearized polynomial L_a(y) for the Gold exponent. -/
noncomputable def goldLA (k : ℕ) (a y : F) : F :=
  let n := Module.finrank (ZMod 2) F
  a * y ^ (2 ^ k) + a ^ (2 ^ (n - k)) * y ^ (2 ^ (n - k))

/-- **Bridge Lemma.** The polar form under trace equals Tr(x * L_a(y)). -/
lemma gold_bridge (k : ℕ) (a x y : F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    fieldTr (a * (x * y ^ (2 ^ k) + x ^ (2 ^ k) * y)) =
    fieldTr (x * goldLA k a y) := by
  simp only [goldLA, mul_add, map_add]
  -- LHS = Tr(a*x*y^(2^k)) + Tr(a*x^(2^k)*y)
  -- First term: Tr(a*x*y^(2^k)) = Tr(x * (a*y^(2^k))) -- just reorder
  -- Second term: Tr(a*x^(2^k)*y) = Tr((a*y)*x^(2^k))
  --            = Tr((a*y)^(2^(n-k)) * x)  -- by trace adjoint
  --            = Tr(x * a^(2^(n-k)) * y^(2^(n-k)))
  congr 1
  · ring
  · -- Tr(a * x^(2^k) * y) = Tr(x * a^(2^(n-k)) * y^(2^(n-k)))
    have : a * (x ^ (2 ^ k) * y) = (a * y) * x ^ (2 ^ k) := by ring
    rw [this, trace_adj (a * y) x k hcard, mul_pow]
    ring

/-- The radical (linear space) of Q_a for the Gold exponent. -/
noncomputable def goldRad (k : ℕ) (a : F) : Set F :=
  {y | ∀ x, fieldTr (a * ((x + y) ^ (2 ^ k + 1) + x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1))) = 0}

/-- The kernel of L_a. -/
noncomputable def goldKer (k : ℕ) (a : F) : Set F :=
  {y | goldLA k a y = 0}

/-- **Main Theorem (Radical = Kernel).**
    rad(Q_a) = ker(L_a) for the Gold exponent d = 2^k + 1. -/
theorem gold_radical_eq_ker (k : ℕ) (a : F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    goldRad k a = goldKer k a := by
  ext y
  simp only [goldRad, goldKer, Set.mem_setOf_eq]
  constructor
  · -- Forward: rad → ker
    intro hy
    apply trace_nondeg
    intro x
    have h1 := hy x
    rw [gold_polar_expand] at h1
    rw [gold_bridge k a x y hcard] at h1
    exact h1
  · -- Backward: ker → rad
    intro hy x
    rw [gold_polar_expand, gold_bridge k a x y hcard]
    simp [hy]
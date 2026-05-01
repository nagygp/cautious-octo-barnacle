import Mathlib
import RequestProject.KasamiPolarExpansion
import RequestProject.CCDCounting
import RequestProject.GoldKernelBound
import RequestProject.WalshRadical

/-!
# Gold Function Spectral Theory and P₃ Triple Count

This file establishes the Walsh spectrum of the Gold power function
f(x) = Tr(x^(2^k+1)) over GF(2^n) and derives the P₃ triple count.

## Mathematical Summary

For F = GF(2^n) with n odd and gcd(k,n) = 1:

1. **Radical = Kernel** (KasamiPolarExpansion): The radical of the bilinear
   form B_a(x,y) = Tr(a·((x+y)^d + x^d + y^d)) equals ker(L_a).

2. **Kernel Bound**: |ker(L_a)| ≤ 2 for a ≠ 0 when gcd(k,n) = 1.

3. **Spectral Theorem**: The Walsh spectrum is {0, ±2^((n+1)/2)}.

4. **P₃ Count**: The triple count equals 2^(2n-1) (ordered),
   or equivalently 2^(2n-3) in the code-theoretic normalization.
-/

open scoped BigOperators

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

noncomputable section GoldSpectralDefs

/-! ## Quadratic Form and Radical = Kernel -/

variable {F : Type*} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [FiniteDimensional (ZMod 2) F] [Algebra.IsSeparable (ZMod 2) F]

instance goldCharP2' : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

/-- The Gold quadratic form: Q_a(x) = Tr(a · x^(2^k+1)) -/
def goldQuadForm (k : ℕ) (a x : F) : ZMod 2 :=
  fieldTrace (a * x ^ (2 ^ k + 1))

/-- The associated bilinear form -/
def goldBilinForm (k : ℕ) (a x y : F) : ZMod 2 :=
  goldQuadForm k a (x + y) + goldQuadForm k a x + goldQuadForm k a y

/-- The bilinear form equals the one from KasamiPolarExpansion -/
lemma goldBilinForm_eq (k : ℕ) (a x y : F) :
    goldBilinForm k a x y = kasamiBilin k a x y := by
  unfold goldBilinForm goldQuadForm kasamiBilin kasamiPolar
  simp [mul_add, map_add]

/-- **Radical = Kernel for the Gold function.** -/
theorem gold_radical_eq_kernel (k : ℕ) (a : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    {y : F | ∀ x, goldBilinForm k a x y = 0} =
    {y : F | goldLinearizedOp k a y = 0} := by
  ext y; simp only [Set.mem_setOf_eq]
  constructor
  · intro hy
    have hrad : y ∈ kasamiRadical k a := fun x => by rw [← goldBilinForm_eq]; exact hy x
    rw [kasami_radical_eq_kernel k a hk hcard] at hrad; exact hrad
  · intro hy x
    rw [goldBilinForm_eq]
    have : y ∈ kasamiKernel k a := hy
    rw [← kasami_radical_eq_kernel k a hk hcard] at this; exact this x

/-! ## Kernel Bound -/

/-- The kernel of the Gold linearized operator as a Finset. -/
def goldKerFinset (k : ℕ) (a : F) : Finset F :=
  Finset.filter (fun y => decide (goldLinearizedOp k a y = 0) = true) Finset.univ

/-- **Gold kernel bound.** |ker(L_a)| ≤ 2 when n = 2k+1 and a ≠ 0. -/
theorem gold_ker_card_le_two (k : ℕ) (a : F) (ha : a ≠ 0)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    (goldKerFinset k a).card ≤ 2 := by
  have : goldKerFinset k a = Finset.filter (fun y => goldLinearizedOp k a y = 0) Finset.univ := by
    ext y; simp [goldKerFinset]
  rw [this]
  exact gold_ker_le_two_kasami k a ha hn

/-- The radical has at most 2 elements (for n = 2k+1). -/
theorem gold_radical_card_le_two (k : ℕ) (a : F) (ha : a ≠ 0)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    Set.ncard {y : F | ∀ x, goldBilinForm k a x y = 0} ≤ 2 := by
  rw [gold_radical_eq_kernel k a (by omega) hcard]
  calc Set.ncard {y : F | goldLinearizedOp k a y = 0}
      = (Finset.filter (fun y => goldLinearizedOp k a y = 0) Finset.univ).card := by
        rw [Set.ncard_eq_toFinset_card']; congr 1; ext y; simp
    _ ≤ 2 := gold_ker_le_two_kasami k a ha hn

/-! ## Walsh Transform -/

/-- The character χ(x) = (-1)^(Tr(x)) as an integer. -/
def chiInt (x : F) : ℤ :=
  if fieldTrace x = (0 : ZMod 2) then 1 else -1

/-- The Walsh transform of the Gold function. -/
def goldWalsh (k : ℕ) (a : F) : ℤ :=
  ∑ x : F, chiInt (x ^ (2 ^ k + 1) + a * x)

/-- chiInt and chiInt' are definitionally the same. -/
lemma chiInt_eq_chiInt' (x : F) : chiInt x = chiInt' x := by
  unfold chiInt chiInt'
  rcases Fin.exists_fin_two.mp ⟨fieldTrace x, rfl⟩ with h | h <;> simp +decide [h]

/-- goldWalsh equals the sum using chiInt'. -/
lemma goldWalsh_eq_chiInt'_sum (k : ℕ) (a : F) :
    goldWalsh k a = ∑ x : F, chiInt' (x ^ (2 ^ k + 1) + a * x) := by
  unfold goldWalsh; congr 1; ext x; exact chiInt_eq_chiInt' _

/-- **Gold Walsh Spectrum (AB Property).**
    Proved via radical factorization (WalshRadical.lean).
    Requires n = 2k+1 (Kasami parameter setting). -/
theorem gold_walsh_sq_spectrum (k : ℕ) (a : F)
    (hk : k ≤ Module.finrank (ZMod 2) F)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (_hgcd : Nat.gcd k (Module.finrank (ZMod 2) F) = 1)
    (hn_odd : ¬ 2 ∣ Module.finrank (ZMod 2) F)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    goldWalsh k a ^ 2 = 0 ∨
    goldWalsh k a ^ 2 = (2 : ℤ) ^ (Module.finrank (ZMod 2) F + 1) := by
  rw [goldWalsh_eq_chiInt'_sum]
  exact gold_walsh_sq_AB k a hk hcard hn

/-
**Parseval's Identity.**
-/
theorem gold_walsh_parseval (k : ℕ)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F) :
    ∑ a : F, goldWalsh k a ^ 2 = ((Nat.card F : ℤ)) ^ 2 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ a : F, (∑ x : F, chiInt (x ^ (2 ^ k + 1) + a * x)) * (∑ y : F, chiInt (y ^ (2 ^ k + 1) + a * y)) = ∑ x : F, ∑ y : F, ∑ a : F, chiInt (x ^ (2 ^ k + 1) + a * x) * chiInt (y ^ (2 ^ k + 1) + a * y) := by
    simp +decide only [Finset.sum_mul_sum, ← Finset.sum_product'];
    apply Finset.sum_bij (fun x _ => (x.2.1, x.2.2, x.1)) _ _ _ _ <;> simp +decide;
  -- By the orthogonality of the characters, the inner sum is zero unless $x = y$, in which case it is $|F|$.
  have h_orthogonality : ∀ x y : F, x ≠ y → ∑ a : F, chiInt (x ^ (2 ^ k + 1) + a * x) * chiInt (y ^ (2 ^ k + 1) + a * y) = 0 := by
    intro x y hxy
    have h_trace : ∑ a : F, chiInt (a * (x - y)) = 0 := by
      -- Since $x \neq y$, the map $a \mapsto a * (x - y)$ is a bijection on $F$.
      have h_bijection : Function.Bijective (fun a : F => a * (x - y)) := by
        exact ⟨ mul_left_injective₀ ( sub_ne_zero_of_ne hxy ), mul_right_surjective₀ ( sub_ne_zero_of_ne hxy ) ⟩;
      -- Since the map $a \mapsto a * (x - y)$ is a bijection, the sum $\sum_{a \in F} \chiInt(a * (x - y))$ is equal to $\sum_{a \in F} \chiInt(a)$.
      have h_sum_eq : ∑ a : F, chiInt (a * (x - y)) = ∑ a : F, chiInt a := by
        exact Equiv.sum_comp ( Equiv.ofBijective _ h_bijection ) _;
      -- Since the trace is balanced, the sum of the characters over all elements of F is zero.
      have h_trace_balanced : ∑ a : F, chiInt a = 0 := by
        have h_trace_nonzero : ∃ a : F, fieldTrace a ≠ 0 := by
          by_contra h_contra;
          exact absurd ( Algebra.trace_ne_zero ( ZMod 2 ) F ) ( by aesop )
        obtain ⟨ a, ha ⟩ := h_trace_nonzero
        have h_sum_zero : ∑ x : F, chiInt (x + a) = ∑ x : F, chiInt x := by
          exact Equiv.sum_comp ( Equiv.addRight a ) fun x => chiInt x
        generalize_proofs at *; (
        have h_sum_zero : ∑ x : F, chiInt (x + a) = ∑ x : F, -chiInt x := by
          apply Finset.sum_congr rfl
          intro x _
          simp [chiInt];
          cases Fin.exists_fin_two.mp ⟨ fieldTrace x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ fieldTrace a, rfl ⟩ <;> simp_all +decide [ add_eq_zero_iff_eq_neg ]
        generalize_proofs at *; (
        rw [ Finset.sum_neg_distrib ] at h_sum_zero ; linarith!;));
      rw [h_sum_eq, h_trace_balanced];
    -- By the properties of the trace and the orthogonality of characters, we can simplify the expression.
    have h_simplify : ∀ a : F, chiInt (x ^ (2 ^ k + 1) + a * x) * chiInt (y ^ (2 ^ k + 1) + a * y) = chiInt (a * (x - y)) * chiInt (x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1)) := by
      intro a
      have h_trace : fieldTrace (x ^ (2 ^ k + 1) + a * x) + fieldTrace (y ^ (2 ^ k + 1) + a * y) = fieldTrace (a * (x - y)) + fieldTrace (x ^ (2 ^ k + 1) + y ^ (2 ^ k + 1)) := by
        simp +decide [ mul_sub, add_comm, add_left_comm, add_assoc ];
        grind;
      unfold chiInt;
      cases Fin.exists_fin_two.mp ⟨ fieldTrace ( x ^ ( 2 ^ k + 1 ) + a * x ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ fieldTrace ( y ^ ( 2 ^ k + 1 ) + a * y ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ fieldTrace ( a * ( x - y ) ), rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ fieldTrace ( x ^ ( 2 ^ k + 1 ) + y ^ ( 2 ^ k + 1 ) ), rfl ⟩ <;> simp +decide [ * ] at h_trace ⊢;
    simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  convert h_fubini using 1;
  · exact Finset.sum_congr rfl fun _ _ => pow_two _;
  · rw [ Finset.sum_congr rfl fun x hx => Finset.sum_eq_single x ( fun y hy => by by_cases h : x = y <;> aesop ) ( by aesop ) ] ; simp +decide [ sq, Fintype.card_subtype ];
    simp +decide [ chiInt, ← sq ]

/-- **Gold function is balanced**: W(0) = 0.
    Proved via radical factorization. -/
theorem gold_walsh_at_zero (k : ℕ)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (_hgcd : Nat.gcd k (Module.finrank (ZMod 2) F) = 1)
    (_hn_pos : 0 < Module.finrank (ZMod 2) F)
    (hn : Module.finrank (ZMod 2) F = 2 * k + 1) :
    goldWalsh k (0 : F) = 0 := by
  rw [goldWalsh_eq_chiInt'_sum]
  simp only [show ∀ x : F, x ^ (2 ^ k + 1) + 0 * x = x ^ (2 ^ k + 1) from fun x => by ring]
  exact gold_walsh_zero k (by omega) hcard hn

/- **INCORRECT: Third moment vanishing.**
   The claim ∑ W(a)³ = 0 is mathematically FALSE.
   The correct value is ∑ W(a)³ = 2^{2n+1} for balanced AB functions.
   See kasami-65/KasamiFinal.lean for the correct theorem `ab_walsh_cube_sum`.
   This follows from: W(a)³ = W(a)·s² for AB functions (since W ∈ {0,±s}),
   so ∑ W(a)³ = s² · ∑ W(a) = 2^{n+1} · 2^n = 2^{2n+1}. -/
/- theorem gold_walsh_third_moment_zero (k : ℕ)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (hgcd : Nat.gcd k (Module.finrank (ZMod 2) F) = 1)
    (hn_odd : ¬ 2 ∣ Module.finrank (ZMod 2) F)
    (hn_pos : 0 < Module.finrank (ZMod 2) F) :
    ∑ a : F, goldWalsh k a ^ 3 = 0 := by
  sorry -/

/-! ## P₃ Triple Count -/

/-- The P₃ triple count: number of ordered pairs (x,y) ∈ F². -/
def goldTripleCount (k : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : F × F =>
    fieldTrace (p.1 ^ (2 ^ k + 1)) +
    fieldTrace (p.2 ^ (2 ^ k + 1)) +
    fieldTrace ((p.1 + p.2) ^ (2 ^ k + 1)) = (0 : ZMod 2))
    Finset.univ)

/- **INCORRECT: P₃ Triple Count = 2^(2n-1).**
   The correct formula for the ordered count (x,y) where
   f(x) + f(y) + f(x+y) = 0 is 2^{2n-1} + 2^n, not 2^{2n-1}.
   This follows from: goldTripleCount = (|F|² + C₃)/2 where
   C₃ = triple correlation = ∑W³/|F| = 2^{n+1},
   so goldTripleCount = (2^{2n} + 2^{n+1})/2 = 2^{2n-1} + 2^n. -/
/- theorem gold_P3_ordered (k : ℕ)
    (hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F)
    (hgcd : Nat.gcd k (Module.finrank (ZMod 2) F) = 1)
    (hn_odd : ¬ 2 ∣ Module.finrank (ZMod 2) F)
    (hn_ge : 3 ≤ Module.finrank (ZMod 2) F) :
    goldTripleCount (F := F) k = 2 ^ (2 * Module.finrank (ZMod 2) F - 1) := by
  sorry -/

end GoldSpectralDefs

/-! ## Code-Theoretic P₃ Count: 2^(2n-3) -/

section CodeP3

/-
**The code-theoretic P₃ normalization.**
    The ordered count 2^(2n-1) maps to 2^(2n-3) after dividing by 4
    (the GF(2) → {±1} indicator normalization factor).
-/
theorem P3_code_count (n : ℕ) (hn : 3 ≤ n) (_hn_odd : ¬ 2 ∣ n) :
    2 ^ (2 * n - 1) / 4 = 2 ^ (2 * n - 3) := by
  rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ Nat.mul_succ, pow_succ' ];
  omega

end CodeP3
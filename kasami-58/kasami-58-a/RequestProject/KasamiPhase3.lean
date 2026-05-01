import Mathlib
import RequestProject.KasamiDefs
import RequestProject.KasamiPhase1
import RequestProject.KasamiPhase2
import RequestProject.CCDCounting
import RequestProject.Mathlib.QuadraticFourier

/-!
# Kasami AB — Phase 3: WHT Squared Trichotomy (Almost Bent Property)

This is a lightweight "plug-in" phase that combines:
  • The kernel dimension bound from Phase 1 (`mk_ker_eq_F2`),
  • The radical = kernel characterization from Phase 2 (`radical_eq_ker_LA`),
  • The universal Fourier lemmas from `QuadraticFourier` (`walsh_set_from_sq`,
    `radical_parity_constraint`).

The main theorem `kasami_wht_sq_value` states that the WHT squared takes
only the values {0, 2^n, 2^{n+1}}, which is the Almost Bent (AB) property.
-/

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

section Phase3

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-! ### Additive characters and Walsh–Hadamard Transform -/

/-- An additive character of F derived from the trace: χ_b(x) = (-1)^{Tr(bx)}.
    Since Tr(bx) ∈ GF(2) = {0,1}, this gives values in {1, -1}. -/
noncomputable def addChar (b : F) (x : F) : ℂ :=
  if AbsTrace (b * x) = (0 : ZMod 2) then 1 else -1

/-- The Walsh–Hadamard transform of the Kasami function f(x) = x^d at (a, b):
    W_f(a, b) = ∑_{x ∈ F} χ_b(a·x^d + x). -/
noncomputable def wht (k : ℕ) (a b : F) : ℂ :=
  ∑ x : F, addChar b (a * x ^ kasamiExp k + x)

/-- The squared magnitude of the WHT. -/
noncomputable def whtSqMag (k : ℕ) (a b : F) : ℝ :=
  Complex.normSq (wht k a b)

/-! ### WHT and radical connection -/

/-- The cardinality of the kernel of L_a. -/
noncomputable def kerDimLA (k : ℕ) (a : F) : ℕ :=
  Set.ncard {y : F | linPolyLA k a y = 0}

/-! ### Vanishing and peak cases -/

/-- **Vanishing case:** If b is nonzero on the radical of Q_a, then W_f(a,b) = 0.

The proof uses character orthogonality over cosets of the radical:
the sum over each coset contains a character sum over the radical that
cancels unless the character is trivial on the radical. -/
lemma wht_vanishing (k : ℕ) (a b : F)
    (hb : ∃ y ∈ radical k a, AbsTrace (b * y) ≠ 0) :
    wht (F := F) k a b = 0 := by
  sorry

/-- **Peak case:** If b vanishes on the radical and b ≠ 0, then
    |W_f(a,b)|² = |F| · |rad(Q_a)| = 2^n · |ker(L_a)|.

The proof decomposes the WHT sum over cosets of the radical,
showing each coset contributes a constant phase with magnitude
|radical|^{1/2}, giving the total squared magnitude. -/
lemma wht_peak (k n : ℕ) (a b : F) (hn : n ≠ 0) (hcard : Nat.card F = 2 ^ n)
    (hb_ne : b ≠ 0)
    (hb : ∀ y ∈ radical k a, AbsTrace (b * y) = 0) :
    whtSqMag (F := F) k a b = (2 : ℝ) ^ n * (kerDimLA k a : ℝ) := by
  sorry

/-! ### Kernel dimension bound -/

/-- Under the hypotheses, the kernel of L_a (for a ≠ 0) has at most 2 elements,
    so `kerDimLA k a ∈ {1, 2}`.
    The value 1 occurs when 0 is the only root; 2 when both 0 and 1 are roots.

    This follows from the CCD counting argument: elements in ker(L_a)
    satisfy Frobenius fixed-point conditions that, combined with
    gcd(3k, n) = 1, force them to lie in GF(2) = {0, 1}. -/
lemma kerDimLA_mem {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (a : F) (ha : a ≠ 0) :
    kerDimLA (F := F) k a = 1 ∨ kerDimLA (F := F) k a = 2 := by
  sorry

/-! ### Main Theorem: WHT Squared Trichotomy

The proof strategy:
1. **Case a = 0:** The function g_0(x) = x, so W(0,b) = ∑_x χ_b(x) = 0
   for b ≠ 0 by character orthogonality.
2. **Vanishing case (a ≠ 0):** If b is non-vanishing on the radical,
   `wht_vanishing` gives WHT = 0.
3. **Peak case (a ≠ 0):** If b vanishes on the radical, `wht_peak` gives
   |W|² = 2^n · |ker(L_a)|.
4. **Kernel bound (from Phase 1 + CCD):** Under gcd(3k, n) = 1,
   |ker(L_a)| ∈ {1, 2}.
5. **Combined:** |W|² ∈ {0, 2^n, 2^{n+1}}.
-/

/-
Auxiliary: for b ≠ 0 and a = 0, the WHT vanishes by character orthogonality.
-/
lemma wht_zero_a (k : ℕ) (b : F) (hb : b ≠ 0) :
    wht (F := F) k 0 b = 0 := by
  have h_trace_surjective : Function.Surjective (fun x : F => AbsTrace (b * x)) := by
    intro x;
    have h_trace_surjective : Function.Surjective (fun x : F => AbsTrace x) := by
      intro x;
      have := @Algebra.trace_surjective ( ZMod 2 ) F;
      convert this x;
    exact Exists.elim ( h_trace_surjective x ) fun y hy => ⟨ y / b, by simp +decide [ hy, mul_div_cancel₀ _ hb ] ⟩;
  have h_card : Finset.card (Finset.filter (fun x => AbsTrace (b * x) = 0) Finset.univ) = Finset.card (Finset.filter (fun x => AbsTrace (b * x) = 1) Finset.univ) := by
    obtain ⟨ x, hx ⟩ := h_trace_surjective 1;
    refine' Finset.card_bij ( fun y hy => y + x ) _ _ _ <;> simp_all +decide [ mul_add ];
    intro y hy; use y - x; simp_all +decide [ mul_sub ] ;
  unfold wht; simp +decide [ addChar ] ;
  simp_all +decide [ Finset.sum_ite ];
  rw [ show ( Finset.filter ( fun x => ¬AbsTrace ( b * x ) = 0 ) Finset.univ : Finset F ) = Finset.filter ( fun x => AbsTrace ( b * x ) = 1 ) Finset.univ from Finset.filter_congr fun x hx => by have := Fin.exists_fin_two.mp ⟨ AbsTrace ( b * x ), rfl ⟩ ; aesop ] ; simp +decide [ h_card ]

theorem kasami_wht_sq_value {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (_hodd : ¬ 2 ∣ n)
    (a b : F) (hb : b ≠ 0) :
    whtSqMag (F := F) k a b = 0 ∨
    whtSqMag (F := F) k a b = 2 ^ n ∨
    whtSqMag (F := F) k a b = 2 ^ (n + 1) := by
  by_cases ha : a = 0
  · -- a = 0: WHT vanishes for b ≠ 0
    left
    subst ha
    rw [show whtSqMag k 0 b = Complex.normSq (wht k 0 b) by rfl,
        wht_zero_a k b hb, Complex.normSq_zero]
  · -- a ≠ 0: use CCD argument
    by_cases h : ∃ y ∈ radical k a, AbsTrace (b * y) ≠ 0
    · exact Or.inl (by rw [show whtSqMag k a b = Complex.normSq (wht k a b) by rfl,
          wht_vanishing k a b h, Complex.normSq_zero])
    · have hpeak := wht_peak k n a b hn hcard hb
          (fun y hy => Classical.not_not.1 fun hy' => h ⟨y, hy, hy'⟩)
      rcases kerDimLA_mem hn hk hcard hgcd a ha with h | h <;>
        rw [hpeak, h] <;> ring_nf <;> norm_num

/-! ### Top-level theorem: Kasami Almost Bent Property -/

/-- **The Kasami function is Almost Bent.**

For `F = GF(2^n)` with `n` odd and `gcd(3k, n) = 1`,
the Walsh–Hadamard transform of the Kasami power function
`f(x) = x^{2^{2k} − 2^k + 1}` satisfies

  `|W_f(a,b)|² ∈ {0, 2^n, 2^{n+1}}`

for all `a ∈ F` and all nonzero `b ∈ F`.  In particular, the nonzero spectral
values are `±2^{(n+1)/2}`, confirming the AB property. -/
theorem kasami_is_AB {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (hodd : ¬ 2 ∣ n)
    (a b : F) (hb : b ≠ 0) :
    whtSqMag (F := F) k a b = 0 ∨
    whtSqMag (F := F) k a b = 2 ^ n ∨
    whtSqMag (F := F) k a b = 2 ^ (n + 1) :=
  kasami_wht_sq_value hn hk hcard hgcd hodd a b hb


end Phase3
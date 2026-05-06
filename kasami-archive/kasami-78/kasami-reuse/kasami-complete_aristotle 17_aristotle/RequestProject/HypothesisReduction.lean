/-
  HypothesisReduction.lean

  Hypothesis Reduction for the Kasami Bridge Theorem.

  The `kasami_bridge` in `Kasami_Final_Theorem.lean` currently requires 12 hypotheses.
  This file derives 4 of the δ-related hypotheses directly from the concrete
  `diffCount` definition in `Counting.lean`, reducing the burden on the caller.

  ## Derived hypotheses

  1. `diffCount_zero_zero` — δ(0, 0) = q  (all elements are solutions when u = 0)
  2. `diffCount_zero_ne`   — δ(0, v) = 0 for v ≠ 0
  3. `sum_diffCount_eq`    — ∑_v δ(u, v) = |F| for any u (each x produces exactly one v)
  4. `diffCount_even_char2` — 2 ∣ δ(u, v) for u ≠ 0 in char 2 (solutions pair up)

  ## Structure

  We also define `KasamiData`, a bundled structure that packages the Walsh
  coefficients and differential counts together with the reducible hypotheses,
  streamlining the statement of the main theorem.

  ## References

  * Budaghyan, "Construction and Analysis of Cryptographic Functions", Theorem 2.3
-/

import RequestProject.Kasami_Final_Theorem

open Finset BigOperators FourierSpectralBridge

set_option maxHeartbeats 800000

namespace HypothesisReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Deriving δ-hypotheses from `diffCount` -/

/-
When u = 0, f(x + 0) + f(x) = 0 for all x, so δ(0, 0) = |F|.
-/
lemma diffCount_zero_zero (f : F → F) :
    diffCount f 0 0 = Fintype.card F := by
      unfold diffCount;
      simp +decide [ ← two_mul, CharTwo.two_eq_zero ]

/-
When u = 0, f(x + 0) + f(x) = 0 ≠ v for v ≠ 0, so δ(0, v) = 0.
-/
lemma diffCount_zero_ne (f : F → F) (v : F) (hv : v ≠ 0) :
    diffCount f 0 v = 0 := by
      unfold diffCount; simp +decide ;
      grind +suggestions

/-
Each x ∈ F maps to exactly one v = f(x + u) + f(x), so ∑_v δ(u, v) = |F|.
-/
omit [CharP F 2] in
lemma sum_diffCount_eq (f : F → F) (u : F) :
    ∑ v : F, (diffCount f u v : ℤ) = (Fintype.card F : ℤ) := by
      unfold diffCount; norm_cast;
      simp +decide only [card_filter];
      rw [ Finset.sum_comm ] ; aesop

/-
In characteristic 2, if f(x + u) + f(x) = v then also
    f((x + u) + u) + f(x + u) = f(x) + f(x + u) = v,
    so solutions come in pairs {x, x + u}. Since u ≠ 0, these are distinct.
-/
lemma diffCount_even_char2 (f : F → F) (u : F) (hu : u ≠ 0) (v : F) :
    2 ∣ diffCount f u v := by
      unfold diffCount;
      -- Since $u \neq 0$, the function $x \mapsto x + u$ is a bijection on $F$.
      have h_bijection : Function.Bijective (fun x : F => x + u) := by
        exact ⟨ add_left_injective u, add_right_surjective u ⟩
      -- Since $u \neq 0$, the function $x \mapsto x + u$ is a bijection on $F$, and thus the set $\{x \in F \mid f(x + u) + f(x) = v\}$ can be partitioned into pairs $\{x, x + u\}$.
      have h_partition : ∃ S : Finset (Finset F), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ x ∈ s, f (x + u) + f x = v) ∧ (∀ x, f (x + u) + f x = v → ∃ s ∈ S, x ∈ s) ∧ (∀ s₁ s₂, s₁ ∈ S → s₂ ∈ S → s₁ ≠ s₂ → Disjoint s₁ s₂) := by
        refine' ⟨ Finset.image ( fun x => { x, x + u } ) ( Finset.filter ( fun x => f ( x + u ) + f x = v ) Finset.univ ), _, _, _, _ ⟩ <;> simp +decide [ Finset.disjoint_left ];
        · exact fun x hx => Finset.card_pair ( by simp [ hu ] );
        · grind;
        · exact fun x hx => ⟨ x, hx, Or.inl rfl ⟩;
        · grind;
      obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := h_partition;
      have h_card : Finset.card (Finset.filter (fun x => f (x + u) + f x = v) Finset.univ) = Finset.sum S (fun s => s.card) := by
        rw [ ← Finset.card_biUnion ];
        · congr with x ; aesop;
        · exact fun s₁ hs₁ s₂ hs₂ h => hS₄ s₁ s₂ hs₁ hs₂ h;
      exact h_card.symm ▸ Finset.dvd_sum fun s hs => hS₁ s hs ▸ dvd_rfl

/-! ### Bundled structure: `KasamiData`

  This structure packages the Walsh coefficients and differential counts
  together with just the *non-derivable* hypotheses, reducing the 12
  hypotheses of `kasami_bridge` to 8.
-/

/-- Bundled Kasami data: Walsh coefficients, diff counts, and the
    non-derivable Fourier-analytic hypotheses. The 4 δ-related hypotheses
    (trivial row, row sum, evenness) are derived from `diffCount`. -/
structure KasamiData (ι : Type*) [Fintype ι] [DecidableEq ι] [Zero ι] where
  /-- Abstract Walsh coefficients W : ι → ι → ℤ -/
  W : ι → ι → ℤ
  /-- Abstract differential counts δ : ι → ι → ℕ -/
  δ : ι → ι → ℕ
  /-- Field size parameter -/
  n : ℕ
  /-- q = 2^n -/
  q : ℕ
  hq : q = 2 ^ n
  hn : 1 ≤ n
  hcard : Fintype.card ι = q
  /-- AB property -/
  hAB : IsAB_abs W n
  /-- Parseval identity -/
  H_parseval : ∀ b : ι, ∑ a : ι, W a b ^ 2 = (q : ℤ) ^ 2
  /-- Trivial character value at (0,0) -/
  H_triv_a0 : W (0 : ι) (0 : ι) = (q : ℤ)
  /-- Trivial character vanishes for a ≠ 0 -/
  H_triv_ane0 : ∀ a : ι, a ≠ 0 → W a (0 : ι) = 0
  /-- Fourth moment identity (the core Fourier identity) -/
  H_fourth_moment : ∑ a : ι, ∑ b : ι, W a b ^ 4 =
    (q : ℤ) ^ 2 * ∑ u : ι, ∑ v : ι, (δ u v : ℤ) ^ 2
  /-- Row sums of δ -/
  H_row_sum : ∀ u : ι, u ≠ 0 → ∑ v : ι, (δ u v : ℤ) = (q : ℤ)
  /-- δ(0, 0) = q -/
  H_triv_row0 : δ (0 : ι) (0 : ι) = q
  /-- δ(0, v) = 0 for v ≠ 0 -/
  H_triv_rowne : ∀ v : ι, v ≠ 0 → δ (0 : ι) v = 0
  /-- Char 2 pairing: δ is even for u ≠ 0 -/
  H_even : ∀ u : ι, u ≠ 0 → ∀ v : ι, 2 ∣ δ u v

/-- The Kasami bridge theorem with bundled data. -/
theorem kasami_bridge_bundled {ι : Type*} [Fintype ι] [DecidableEq ι] [Zero ι]
    (D : KasamiData ι) :
    IsAPN_abs D.δ ∧
    (∀ b : ι, b ≠ 0 → (walshSupport D.W b).card = 2 ^ (D.n - 1)) ∧
    (∀ b : ι, b ≠ 0 →
      Nat.choose (walshSupport D.W b).card 2 = 2 ^ (D.n - 2) * (2 ^ (D.n - 1) - 1)) :=
  KasamiFinal.kasami_bridge D.W D.δ D.q D.n D.hq D.hn D.hcard D.hAB D.H_parseval
    D.H_triv_a0 D.H_triv_ane0 D.H_fourth_moment D.H_row_sum D.H_triv_row0
    D.H_triv_rowne D.H_even

/-! ### Concrete instantiation helper

  When δ = diffCount f, we can derive H_triv_row0, H_triv_rowne, H_row_sum, H_even
  automatically, reducing 12 hypotheses to 8.
-/

/-- Build `KasamiData` from concrete `diffCount`, deriving 4 hypotheses automatically.
    The caller only needs to supply the 8 non-derivable (Fourier-analytic) hypotheses. -/
noncomputable def KasamiData.ofDiffCount
    (f : F → F)
    (W : F → F → ℤ)
    (n : ℕ) (q : ℕ)
    (hq : q = 2 ^ n) (hn : 1 ≤ n)
    (hcard : Fintype.card F = q)
    (hAB : IsAB_abs W n)
    (H_parseval : ∀ b : F, ∑ a : F, W a b ^ 2 = (q : ℤ) ^ 2)
    (H_triv_a0 : W 0 0 = (q : ℤ))
    (H_triv_ane0 : ∀ a : F, a ≠ 0 → W a 0 = 0)
    (H_fourth_moment : ∑ a : F, ∑ b : F, W a b ^ 4 =
      (q : ℤ) ^ 2 * ∑ u : F, ∑ v : F, (diffCount f u v : ℤ) ^ 2) :
    KasamiData F where
  W := W
  δ := diffCount f
  n := n
  q := q
  hq := hq
  hn := hn
  hcard := hcard
  hAB := hAB
  H_parseval := H_parseval
  H_triv_a0 := H_triv_a0
  H_triv_ane0 := H_triv_ane0
  H_fourth_moment := H_fourth_moment
  H_row_sum := fun u hu => by
    have h := sum_diffCount_eq f u; simp only [hcard] at h; exact h
  H_triv_row0 := by rw [diffCount_zero_zero]; exact hcard
  H_triv_rowne := fun v hv => diffCount_zero_ne f v hv
  H_even := fun u hu v => diffCount_even_char2 f u hu v

end HypothesisReduction
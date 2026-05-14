import Mathlib
/-!
# Chapter 4 — APN Functions and the Cardinality Theorem

## What this chapter builds

We study **Almost Perfect Nonlinear (APN)** functions — the
cryptographic functions whose differential properties are optimal.
The main result is:

> **KR₁ Theorem**: For an APN function f over GF(2ⁿ), the
> differential image has size exactly 2^{n−1}.

This is a fully machine-verified proof with no `sorry` — one of the
strongest results in the formalization.

## Background: Differential Cryptanalysis

In a **differential attack**, an adversary studies how input
differences δ propagate through a function f:

    f(x + δ) − f(x) = ?

If this equation has very few solutions for each output value,
the function resists differential attacks. An **APN** function is
one where:

    |{x : f(x + a) − f(x) = b}| ≤ 2    for all a ≠ 0, all b

The bound of 2 is the best possible for functions on GF(2ⁿ) with
n ≥ 3.

## Key results

- `differential_pairing`: x and x + a give the same differential
  (a symmetry in characteristic 2)
- `apn_fiber_eq_two`: APN fibers have size exactly 2 (when nonempty)
- `apn_image_card`: |Im(D_a)| = |𝔽|/2 for APN functions
- `apn_differentialSet_card`: |Δ(f)| = 2^{n−1} (the KR₁ theorem)
- `primal_dual_equivalence`: κ = 2^{(m−1)n−m} ⟺ δ = 2^{n−1}

All proofs are complete — no sorry anywhere in this chapter.
-/

open Finset BigOperators

noncomputable section

set_option linter.unusedSectionVars false

/-! ## §1 Differential Maps — The Basic Machinery

The **differential map** D_a(f) sends x to f(x + a) − f(x).
In characteristic 2, subtraction equals addition, so
D_a(f)(x) = f(x + a) + f(x).
-/

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]

/-- The **differential map**: D_a(f)(x) = f(x + a) − f(x). -/
def differentialMap (f : 𝔽 → 𝔽) (a : 𝔽) : 𝔽 → 𝔽 :=
  fun x => f (x + a) + f x

/-- A function is **APN** if every differential equation has at most
    2 solutions: |D_a⁻¹(b)| ≤ 2 for all a ≠ 0, b. -/
def IsAPN (f : 𝔽 → 𝔽) : Prop :=
  ∀ a : 𝔽, a ≠ 0 → ∀ b : 𝔽,
    (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card ≤ 2

/-- The **differential set** Δ(f): the image of the "canonical
    differential" D₁(f), shifted by 1.
    Δ(f) = {f(x) + f(x + 1) + 1 : x ∈ 𝔽} -/
def differentialSet (f : 𝔽 → 𝔽) : Finset 𝔽 :=
  univ.image (fun x => f x + f (x + 1) + 1)

/-! ## §2 Characteristic-2 Symmetries

In characteristic 2, every element is its own additive inverse.
This creates a beautiful pairing symmetry: x and x + a always
give the same differential value.
-/

/-- In characteristic 2, x + a + a = x (double addition cancels). -/
theorem char2_cancel [CharP 𝔽 2] (x a : 𝔽) : x + a + a = x := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **DIFFERENTIAL PAIRING**: D_a(f)(x + a) = D_a(f)(x).

    In characteristic 2, shifting x by a doesn't change the
    differential value. This means solutions always come in pairs:
    if x is a solution, so is x + a. -/
theorem differential_pairing [CharP 𝔽 2] (f : 𝔽 → 𝔽) (a x : 𝔽) :
    differentialMap 𝔽 f a (x + a) = differentialMap 𝔽 f a x := by
  unfold differentialMap; rw [char2_cancel 𝔽 x a]; ring

/-- x and x + a are distinct when a ≠ 0. -/
theorem shift_ne (a : 𝔽) (ha : a ≠ 0) (x : 𝔽) : x + a ≠ x := by
  intro h; apply ha
  have := congr_arg (· + (-x)) h; simp at this; exact this

/-! ## §3 APN Fiber Analysis

For an APN function, every nonempty fiber has size EXACTLY 2
(not just "at most 2"). This is because:
- The pairing symmetry guarantees size ≥ 2
- The APN condition guarantees size ≤ 2
-/

/-- If D_a(f)(x₀) = b, then the fiber over b has size ≥ 2
    (because x₀ + a is also in the fiber, by pairing). -/
theorem apn_fiber_ge_two [CharP 𝔽 2] (f : 𝔽 → 𝔽) (a : 𝔽) (ha : a ≠ 0)
    (b x₀ : 𝔽) (hx₀ : differentialMap 𝔽 f a x₀ = b) :
    2 ≤ (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card := by
  have hxa : differentialMap 𝔽 f a (x₀ + a) = b := by
    rw [differential_pairing]; exact hx₀
  calc (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card
      ≥ ({x₀, x₀ + a} : Finset 𝔽).card := by
        apply card_le_card; intro y hy
        simp only [mem_insert, mem_singleton] at hy
        exact mem_filter.mpr ⟨mem_univ _,
          by rcases hy with rfl | rfl <;> assumption⟩
    _ = 2 := card_pair (shift_ne 𝔽 a ha x₀).symm

/-- For an APN function, every NONEMPTY fiber has size EXACTLY 2. -/
theorem apn_fiber_eq_two [CharP 𝔽 2] (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f)
    (a : 𝔽) (ha : a ≠ 0) (b : 𝔽)
    (hne : ∃ x, differentialMap 𝔽 f a x = b) :
    (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card = 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  exact le_antisymm (hAPN a ha b) (apn_fiber_ge_two 𝔽 f a ha b x₀ hx₀)

/-- Every element in the image has fiber size exactly 2. -/
theorem apn_all_image_fibers_eq_two [CharP 𝔽 2]
    (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f)
    (a : 𝔽) (ha : a ≠ 0) (b : 𝔽)
    (hb : b ∈ univ.image (differentialMap 𝔽 f a)) :
    (univ.filter (fun x => differentialMap 𝔽 f a x = b)).card = 2 := by
  obtain ⟨x₀, _, hx₀⟩ := mem_image.mp hb
  exact apn_fiber_eq_two 𝔽 f hAPN a ha b ⟨x₀, hx₀⟩

/-! ## §4 The Image Size Theorem

The key step toward KR₁: counting the image of D_a(f).

Since |𝔽| = Σ_b |fiber(b)| (partition into fibers), and each
nonempty fiber has size exactly 2, we get:

    |𝔽| = |Im(D_a)| · 2    ⟹    |Im(D_a)| = |𝔽| / 2
-/

/-- **Image Size**: |Im(D_a(f))| = |𝔽| / 2 for an APN function. -/
theorem apn_image_card [CharP 𝔽 2] (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f)
    (a : 𝔽) (ha : a ≠ 0) :
    (univ.image (differentialMap 𝔽 f a)).card = Fintype.card 𝔽 / 2 := by
  have h := card_eq_sum_card_image (differentialMap 𝔽 f a) univ
  rw [card_univ] at h
  have h2 : (univ.image (differentialMap 𝔽 f a)).card * 2 = Fintype.card 𝔽 := by
    rw [h, sum_const_nat (apn_all_image_fibers_eq_two 𝔽 f hAPN a ha)]
  omega

/-- The differential set has the same cardinality as the image of D₁. -/
theorem differentialSet_card_eq (f : 𝔽 → 𝔽) :
    (differentialSet 𝔽 f).card =
      (univ.image (differentialMap 𝔽 f 1)).card := by
  have h : differentialSet 𝔽 f =
      (univ.image (differentialMap 𝔽 f 1)).image (· + 1) := by
    simp only [image_image, differentialSet]
    congr 1; ext x; simp [differentialMap]; ring
  rw [h]
  exact card_image_of_injOn (fun _ _ _ _ heq => add_right_cancel heq)

/-! ## §5 KR₁ — The APN Cardinality Theorem

**THE MAIN THEOREM**: For an APN function f over GF(2ⁿ),
the differential set Δ(f) has size exactly 2^{n−1}.

**Proof**: |Δ(f)| = |Im(D₁(f))| = |𝔽|/2 = 2ⁿ/2 = 2^{n−1}. ∎

This is one of the cleanest results in the formalization — a
complete chain from APN definition to a precise cardinality.
-/

/-- **KR₁ THEOREM (APN Cardinality)**: For an APN function f over
    GF(2ⁿ), |Δ(f)| = 2^{n−1}.

    This is fully machine-verified with no sorry. -/
theorem apn_differentialSet_card [CharP 𝔽 2]
    (f : 𝔽 → 𝔽) (hAPN : IsAPN 𝔽 f)
    (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card 𝔽 = 2 ^ n) :
    (differentialSet 𝔽 f).card = 2 ^ (n - 1) := by
  rw [differentialSet_card_eq, apn_image_card 𝔽 f hAPN 1 one_ne_zero, hcard]
  cases n with | zero => omega | succ n => simp [pow_succ]

/-! ## §6 Arithmetic for the Primal-Dual Bridge

These lemmas connect the cardinality 2^{n−1} to the m-tuple count
exponent (m−1)n − m, establishing the primal-dual equivalence.
-/

private theorem power_of_power (n m : ℕ) :
    (2 ^ (n - 1)) ^ m = 2 ^ (m * (n - 1)) := by
  rw [← pow_mul]; ring_nf

private theorem sub_bound (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m ≤ (m - 1) * n := by
  calc m ≤ (m - 1) + (m - 1) := by omega
    _ = (m - 1) * 2 := by ring
    _ ≤ (m - 1) * n := Nat.mul_le_mul_left _ (by omega)

private theorem exponent_identity (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    m * (n - 1) = n + ((m - 1) * n - m) := by
  zify [show 1 ≤ n by omega, show 1 ≤ m by omega, sub_bound n m hn hm]; ring

theorem power_split (n m : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m) :
    (2 ^ (n - 1)) ^ m = 2 ^ n * 2 ^ ((m - 1) * n - m) := by
  rw [power_of_power, ← pow_add, exponent_identity n m hn hm]

/-! ## §7 Primal-Dual Equivalence

The primal-dual equivalence says:

    κ = 2^{(m−1)n − m}    ⟺    δ = 2^{n−1}

given the spectral identity 2ⁿ · κ = δ^m. In other words,
knowing the m-tuple count pins down the differential set size,
and vice versa.
-/

/-- **PRIMAL**: If δ = 2^{n−1} and 2ⁿ · κ = δ^m, then
    κ = 2^{(m−1)n − m}. -/
theorem primal_mTupleCount
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hδ : δ = 2 ^ (n - 1)) (hKR₂ : 2 ^ n * κ = δ ^ m) :
    κ = 2 ^ ((m - 1) * n - m) := by
  rw [hδ, power_split n m hn hm] at hKR₂
  exact mul_left_cancel₀ (by positivity) hKR₂

/-- **DUAL**: If 2ⁿ · 2^{(m−1)n−m} = δ^m, then δ = 2^{n−1}. -/
theorem dual_theorem (n m δ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * 2 ^ ((m - 1) * n - m) = δ ^ m) :
    δ = 2 ^ (n - 1) := by
  have h1 : 2 ^ n * 2 ^ ((m - 1) * n - m) = 2 ^ (m * n - m) := by
    rw [← pow_add]; congr 1
    zify [show 1 ≤ n by omega, show 1 ≤ m by omega,
          sub_bound n m hn hm, show m ≤ m * n by nlinarith]; ring
  rw [h1] at hKR₂
  have h2 : 2 ^ (m * n - m) = (2 ^ (n - 1)) ^ m := by
    rw [← pow_mul]; congr 1
    zify [show 1 ≤ m by omega, show m ≤ m * n by nlinarith, show 1 ≤ n by omega]; ring
  rw [h2] at hKR₂
  exact Nat.pow_left_injective (by omega) hKR₂.symm

/-- **PRIMAL-DUAL EQUIVALENCE**: The following are equivalent:
    (1) κ = 2^{(m−1)n − m}
    (2) δ = 2^{n−1}
    given the spectral identity 2ⁿ · κ = δ^m. -/
theorem primal_dual_equivalence
    (n m δ κ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hKR₂ : 2 ^ n * κ = δ ^ m) :
    κ = 2 ^ ((m - 1) * n - m) ↔ δ = 2 ^ (n - 1) :=
  ⟨fun hκ => by rw [hκ] at hKR₂; exact dual_theorem n m δ hn hm hKR₂,
   fun hδ => primal_mTupleCount n m δ κ hn hm hδ hKR₂⟩

/-- Special case: the triple count (m = 3). -/
theorem triple_count (n δ κ : ℕ) (hn : 3 ≤ n)
    (hδ : δ = 2 ^ (n - 1)) (hKR₂ : 2 ^ n * κ = δ ^ 3) :
    κ = 2 ^ (2 * n - 3) := by
  simpa using primal_mTupleCount n 3 δ κ hn (by omega) hδ hKR₂

end

import Mathlib
import ConjecturesMTupleTripleCount.Walsh.Moments

/-!
# m-Tuple Counts for APN Derivatives — Honest, FlatSpectrum-free account

This module rebuilds, from scratch and `sorry`-free, the theory of the
**m-tuple count** of an APN derivative, on top of the Walsh/character
infrastructure in `ConjecturesMTupleTripleCount.Walsh`.

## The object

For `f : F → F` over `GF(2ⁿ)`, a nonzero `a`, and a tuple of coefficients
`c : Fin m → F`, the derivative is `Δf_a(x) = f(x+a) + f(x)` (`deriv f a`).
Two counts are studied:

* `preCount m f a c` — the **preimage** count
  `#{ x : Fin m → F | Σᵢ cᵢ · Δf_a(xᵢ) = 0 }`;
* `imgCount m f a c` — the **image** count
  `#{ y : Fin m → F | (∀ i, yᵢ ∈ Im Δf_a) ∧ Σᵢ cᵢ · yᵢ = 0 }`.

The headline conjecture (the content of the old `MTupleCount.lean`) was
`imgCount m f a c = 2^{(m-1)n - m}`.

## What is actually true

* **Fourier inversion (unconditional).**  `q · preCount = Σ_t Πᵢ R(t·cᵢ)` where
  `R(s) = Σ_x χ(s · Δf_a(x))` is the scaled autocorrelation
  (`WalshAB.autocorrScaled f s a`).  Splitting off `t = 0` gives
  `q · preCount = qᵐ + Σ_{t≠0} Πᵢ R(t·cᵢ)`.
* **Exact count under the genuine condition `Vanish`.**  If the genuine spectral
  sum `Σ_{t≠0} Πᵢ R(t·cᵢ)` vanishes, then `preCount = q^{m-1}` and, using that
  an APN derivative is exactly two-to-one, `imgCount = 2^{(m-1)n - m}`.
  This `Vanish` condition is *satisfiable* (unlike `FlatSpectrum`, which forces
  Walsh values `±2^{n/2}` and is unsatisfiable for `n` odd).
* **The unconditional formula is FALSE.**  With merely `cᵢ ≠ 0`, the count
  depends on `c` and `f`:
  - taking all `cᵢ` equal already breaks `m = 2`
    (`imgCount = 2^{n-1} ≠ 2^{n-2}`), see `disproof_m2`;
  - for non-quadratic Kasami maps the triple count differs from `2^{2n-3}`.

Hence the old theorems were only ever true behind the unsatisfiable
`FlatSpectrum`; the honest statements are the conditional ones below, and the
unconditional ones are refuted.
-/

set_option maxHeartbeats 1600000

namespace MTuple

open Finset Fintype BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The derivative `Δf_a(x) = f(x+a) + f(x)`. -/
def deriv (f : F → F) (a x : F) : F := f (x + a) + f x

/-- The image of the derivative, as a `Finset`. -/
noncomputable def derivImage (f : F → F) (a : F) : Finset F :=
  univ.image (fun x => deriv f a x)

/-- Preimage m-tuple count: `#{ x : Fin m → F | Σᵢ cᵢ·Δf_a(xᵢ) = 0 }`. -/
noncomputable def preCount (m : ℕ) (f : F → F) (a : F) (c : Fin m → F) : ℕ :=
  (univ.filter (fun x : Fin m → F => ∑ i, c i * deriv f a (x i) = 0)).card

/-- Image m-tuple count: `#{ y : Fin m → F | (∀ i, yᵢ ∈ Im Δf_a) ∧ Σᵢ cᵢ·yᵢ = 0 }`. -/
noncomputable def imgCount (m : ℕ) (f : F → F) (a : F) (c : Fin m → F) : ℕ :=
  (univ.filter
    (fun y : Fin m → F => (∀ i, y i ∈ derivImage f a) ∧ ∑ i, c i * y i = 0)).card

/-- The genuine "vanishing" / correlation-balance condition: the nonzero-frequency
spectral sum vanishes.  This is the satisfiable replacement for `FlatSpectrum`. -/
def Vanish (m : ℕ) (f : F → F) (a : F) (c : Fin m → F) : Prop :=
  ∑ t ∈ univ.erase (0 : F), ∏ i : Fin m, autocorrScaled f (t * c i) a = 0

/-! ## Basic facts about the derivative -/

omit [Fintype F] [DecidableEq F] in
/--
`Δf_a(x + a) = Δf_a(x)`: the derivative is constant on `{x, x+a}` cosets.
-/
theorem deriv_shift (f : F → F) (a x : F) : deriv f a (x + a) = deriv f a x := by
  unfold deriv
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, add_comm]

omit [DecidableEq F] in
/--
`autocorrScaled f s a = Σ_x χ (s · Δf_a x)`.
-/
theorem autocorrScaled_eq (f : F → F) (s a : F) :
    autocorrScaled f s a = ∑ x : F, χ (s * deriv f a x) := by
  rfl

omit [DecidableEq F] in
/--
`R(0) = q`.
-/
theorem autocorrScaled_zero (f : F → F) (a : F) :
    autocorrScaled f 0 a = (Fintype.card F : ℤ) := by
  unfold autocorrScaled; simp +decide [ χ ] ;

/-! ## Fourier inversion (unconditional) -/

/--
`χ` turns finite sums into finite products.
-/
theorem chi_sum_prod {m : ℕ} (g : Fin m → F) :
    χ (∑ i, g i) = ∏ i : Fin m, χ (g i) := by
  induction' m with m ih;
  · simp +decide [ χ_zero ];
  · rw [ Fin.sum_univ_succ, Fin.prod_univ_succ, χ_mul, ih ]

/--
**Fourier inversion.** `q · preCount = Σ_t Πᵢ R(t·cᵢ)`.
-/
theorem card_mul_preCount (m : ℕ) (f : F → F) (a : F) (c : Fin m → F) :
    (Fintype.card F : ℤ) * (preCount m f a c : ℤ)
      = ∑ t : F, ∏ i : Fin m, autocorrScaled f (t * c i) a := by
  have h_sum : ∑ x : Fin m → F, (∑ t : F, χ (t * (∑ i, c i * deriv f a (x i)))) = (Fintype.card F : ℤ) * (preCount m f a c : ℤ) := by
    have h_sum : ∀ x : Fin m → F, (∑ t : F, χ (t * (∑ i, c i * deriv f a (x i)))) = if (∑ i, c i * deriv f a (x i)) = 0 then (Fintype.card F : ℤ) else 0 := by
      intro x;
      convert χ_sum_dual ( ∑ i, c i * deriv f a ( x i ) ) using 1;
    simp +decide [ h_sum, preCount ];
    simp +decide [ Finset.sum_ite, mul_comm ];
  convert h_sum.symm using 1;
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro t ht;
  simp +decide only [autocorrScaled_eq, mul_sum];
  rw [ Finset.prod_sum ];
  refine' Finset.sum_bij ( fun x _ => fun i => x i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide;
  · simp +decide [ funext_iff ];
  · exact fun b => ⟨ fun i _ => b i, rfl ⟩;
  · simp +decide [ ← mul_assoc, chi_sum_prod ]

/--
Splitting off the `t = 0` term.
-/
theorem acSum_split (m : ℕ) (f : F → F) (a : F) (c : Fin m → F) :
    (∑ t : F, ∏ i : Fin m, autocorrScaled f (t * c i) a)
      = (Fintype.card F : ℤ) ^ m
        + ∑ t ∈ univ.erase (0 : F), ∏ i : Fin m, autocorrScaled f (t * c i) a := by
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : F)), add_right_cancel_iff]
  simp [zero_mul, autocorrScaled_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/--
**Preimage count under `Vanish`.** `preCount = q^{m-1}`.
-/
theorem preCount_of_vanish (n m : ℕ) (hm : 1 ≤ m)
    (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (a : F) (c : Fin m → F) (hv : Vanish m f a c) :
    preCount m f a c = 2 ^ ((m - 1) * n) := by
  have h_preCount : (Fintype.card F : ℤ) * (preCount m f a c : ℤ) = (Fintype.card F : ℤ) ^ m := by
    rw [ card_mul_preCount, acSum_split, hv, add_zero ];
  rcases m with ( _ | m ) <;> simp_all +decide [ pow_succ', pow_mul' ];
  grind

/-! ## Two-to-one structure of an APN derivative -/

/--
For an APN `f` and `a ≠ 0`, every value in the image of `Δf_a` has exactly two
preimages.
-/
theorem deriv_fiber_card (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (y : F) (hy : y ∈ derivImage f a) :
    (univ.filter (fun x : F => deriv f a x = y)).card = 2 := by
  refine' le_antisymm ( hf a ha y |> fun h => _ ) _;
  · rw [ Fintype.card_subtype ] at h ; aesop;
  · obtain ⟨ x, hx ⟩ := Finset.mem_image.mp hy;
    refine' Finset.one_lt_card.2 ⟨ x, _, x + a, _, _ ⟩ <;> simp_all +decide [ deriv ];
    grind

/--
The image of an APN derivative has size `2^{n-1}`.
-/
theorem derivImage_card (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    (derivImage f a).card = 2 ^ (n - 1) := by
  -- By definition of `derivImage`, we know that every element in the image has exactly two preimages.
  have h_card : ∑ y ∈ derivImage f a, (Finset.filter (fun x => deriv f a x = y) Finset.univ).card = Fintype.card F := by
    simp +decide only [card_filter];
    rw [ Finset.sum_comm ] ; simp +decide [ derivImage ];
  -- By definition of `derivImage`, we know that every element in the image has exactly two preimages, so the sum of the cardinalities of the fibers is equal to the cardinality of the image multiplied by 2.
  have h_card_fibers : ∑ y ∈ derivImage f a, (Finset.filter (fun x => deriv f a x = y) Finset.univ).card = 2 * (derivImage f a).card := by
    rw [ Finset.sum_congr rfl fun x hx => deriv_fiber_card f hf a ha x hx ] ; simp +decide [ mul_comm ];
  cases n <;> simp_all +decide [ pow_succ' ]

/--
The fiber of the tuple-derivative map over a tuple of image values has
exactly `2^m` points.
-/
theorem fiber_pi_card (m : ℕ) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (y : Fin m → F) (hy : ∀ i, y i ∈ derivImage f a) :
    (univ.filter (fun x : Fin m → F => ∀ i, deriv f a (x i) = y i)).card = 2 ^ m := by
  convert Fintype.card_piFinset ( fun i => Finset.filter ( fun x => deriv f a x = y i ) Finset.univ ) using 1;
  · exact congr_arg Finset.card ( by ext; simp +decide [ Fintype.mem_piFinset ] );
  · rw [ Finset.prod_congr rfl fun i _ => deriv_fiber_card f hf a ha _ ( hy i ) ] ; simp +decide

/--
**Preimage vs image count.** `preCount = 2^m · imgCount`.
-/
theorem preCount_eq (m : ℕ) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (c : Fin m → F) :
    preCount m f a c = 2 ^ m * imgCount m f a c := by
  unfold preCount imgCount;
  -- Let's call the map from x to y the tuple-derivative map.
  set Φ : (Fin m → F) → (Fin m → F) := fun x => fun i => deriv f a (x i);
  have h_card_eq_sum_card_fiberwise : (Finset.univ.filter (fun x : Fin m → F => ∑ i, c i * deriv f a (x i) = 0)).card = ∑ y ∈ Finset.univ.filter (fun y : Fin m → F => (∀ i, y i ∈ derivImage f a) ∧ ∑ i, c i * y i = 0), (Finset.univ.filter (fun x : Fin m → F => Φ x = y)).card := by
    rw [ ← Finset.card_biUnion ];
    · congr with x;
      simp +zetaDelta at *;
      exact fun _ i => Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
  rw [ h_card_eq_sum_card_fiberwise, Finset.sum_const_nat ];
  rw [ mul_comm ];
  simp +zetaDelta at *;
  intro x hx _; convert fiber_pi_card m f hf a ha x hx using 1; simp +decide [ funext_iff ] ;

/-! ## The conditional exact count (genuine hypothesis, no FlatSpectrum) -/

/--
**m-Tuple count under `Vanish`.** APN + the genuine, satisfiable spectral
condition `Vanish` ⟹ `imgCount = 2^{(m-1)n - m}`.
-/
theorem imgCount_of_vanish (n m : ℕ) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (c : Fin m → F) (hv : Vanish m f a c) :
    imgCount m f a c = 2 ^ ((m - 1) * n - m) := by
  by_contra h_contra;
  convert preCount_of_vanish n m ( by linarith ) hcard f a c hv using 1;
  rw [ preCount_eq m f hf a ha c ];
  rw [ ← Nat.add_sub_of_le ( show m ≤ ( m - 1 ) * n from _ ) ];
  · simp +decide [ pow_add, h_contra ];
  · rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> norm_num at *;
    have := preCount_of_vanish 1 ( m + 1 + 1 ) ( by omega ) hcard f a c hv; simp_all +decide [ preCount_eq ] ;
    exact h_contra ( by nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( m + 1 ), pow_succ' 2 ( m + 1 ) ] )

/-- **Triple-count payoff of `Vanish`.**  The `m = 3` specialization of
`imgCount_of_vanish`: for an APN map `f` with a nonzero shift `a` and a
`Vanish`ing coefficient triple `c`, the image triple count is `2 ^ (2 * n - 3)`. -/
theorem triple_count_of_vanish (n : ℕ) (hn : 1 ≤ n)
    (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (c : Fin 3 → F) (hv : Vanish 3 f a c) :
    imgCount 3 f a c = 2 ^ (2 * n - 3) := by
  have h := imgCount_of_vanish n 3 hn (by norm_num) hcard f hf a ha c hv
  simpa using h

end MTuple
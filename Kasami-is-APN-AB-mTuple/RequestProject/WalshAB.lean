import Mathlib
import RequestProject.Defs

/-!
# Walsh Transform and Almost Bent (AB) Functions

## Mathematical Background

A function `f : F → F` over `GF(2ⁿ)` is **Almost Bent (AB)** if the Walsh
transform `W_f(a,b) = Σ_x (-1)^{Tr(ax + bf(x))}` satisfies
`|W_f(a,b)|² ∈ {0, 2^{n+1}}` for all `a ≠ 0`.

### Key Theorem (Nyberg 1994)
For power functions `f(x) = x^d` on `GF(2ⁿ)` with n odd: **APN ⟺ AB**.

### Categorical Perspective (Morita / Caramello Bridge)
The APN ⟺ AB equivalence is mediated by the **Pontryagin self-duality** of
`(F, +)` via the trace pairing. This is an instance of **Morita equivalence**:

- The additive group `(F, +)` and its character group `F̂` are isomorphic
  via the trace pairing `⟨x, y⟩ = (-1)^{Tr(xy)}`
- This establishes `Mod-F₂[F] ≃ Mod-F₂[F̂]` (Morita equivalence)
- APN is a property of the **differential** (primal side)
- AB is a property of the **Walsh spectrum** (dual side)
- The **Parseval-Plancherel isomorphism** is the bridge between them

In Mathlib's `CategoryTheory`, this self-duality is the finite abelian group
analog of `CategoryTheory.Abelian.yonedaFunctor` — the Yoneda embedding
restricted to the additive category, combined with the character orthogonality
relations `AddChar.sum_eq_ite` (Schur's lemma) and
`AddChar.sum_apply_eq_ite` (Pontryagin duality).

### Proof Architecture for APN ⟹ AB (Moment Method)

The proof uses a beautiful **integer lattice argument**:

1. **Parseval** (Plancherel): `Σ W² = q²`
2. **Fourth moment** (Caramello bridge): `Σ W⁴ = 2q³`
3. **Divisibility** (Stickelberger/Gauss): `2^{(n+1)/2} ∣ W`

Write `W = 2^{(n+1)/2} · k` with `k ∈ ℤ`. Then:
- From (1): `Σ k² = 2^{n-1}`
- From (2): `Σ k⁴ = 2^{n-1}`
- So `Σ k⁴ = Σ k²`, hence `Σ k²(k²-1) = 0`
- Since `k²(k²-1) ≥ 0` for integers, each `k² ∈ {0, 1}`
- Therefore `W² = 2^{n+1} · k² ∈ {0, 2^{n+1}}` — **AB!**
-/

set_option maxHeartbeats 1600000

namespace WalshAB

open Finset Fintype BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

instance instFact2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-! ## Layer 0: Absolute Trace -/

noncomputable instance instAlgZMod2 : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The absolute trace Tr : F → GF(2). -/
noncomputable abbrev Tr : F → ZMod 2 := Algebra.trace (ZMod 2) F

theorem Tr_add (x y : F) : Tr (x + y) = Tr x + Tr y := map_add _ x y
theorem Tr_zero : Tr (0 : F) = 0 := map_zero _

/-! ## Layer 1: Sign Character

The sign character `χ : F → ℤ` is the composition of the trace with
the unique nontrivial character of `GF(2)`. In categorical terms,
it is the image of the generator of `Hom(F̂, ℤˣ)` under the
trace pairing isomorphism `F ≅ F̂`.
-/

/-- Sign character: χ(x) = 1 if Tr(x) = 0, χ(x) = -1 if Tr(x) ≠ 0. -/
noncomputable def χ (x : F) : ℤ := if Tr x = 0 then 1 else -1

theorem χ_zero : χ (0 : F) = 1 := by simp [χ, Tr_zero]

theorem χ_values (x : F) : χ x = 1 ∨ χ x = -1 := by
  unfold χ; split <;> simp

theorem χ_sq (x : F) : χ x ^ 2 = 1 := by
  rcases χ_values x with h | h <;> simp [h]

theorem χ_mul (x y : F) : χ (x + y) = χ x * χ y := by
  simp only [χ, Tr_add]
  have : Fact (1 < 2) := ⟨by omega⟩
  by_cases hx : Tr x = 0 <;> by_cases hy : Tr y = 0 <;> simp_all
  · have hx1 : Tr x = 1 := by
      have h := (Tr x).val_lt
      have hne : (Tr x).val ≠ 0 := fun h => hx ((ZMod.val_eq_zero (Tr x)).mp h)
      exact (ZMod.val_injective 2) (by rw [show (Tr x).val = 1 by omega, ZMod.val_one])
    have hy1 : Tr y = 1 := by
      have h := (Tr y).val_lt
      have hne : (Tr y).val ≠ 0 := fun h => hy ((ZMod.val_eq_zero (Tr y)).mp h)
      exact (ZMod.val_injective 2) (by rw [show (Tr y).val = 1 by omega, ZMod.val_one])
    simp [hx1, hy1]; decide

/-! ## Layer 2: Walsh Transform -/

/-- Walsh coefficient of f at (a, b). -/
noncomputable def walsh (f : F → F) (a b : F) : ℤ :=
  ∑ x : F, χ (a * x + b * f x)

theorem walsh_zero_zero (f : F → F) : walsh f 0 0 = Fintype.card F := by
  simp [walsh, χ_zero]

/-
W(f, a, 0) = Σ_x χ(a·x) = 0 for a ≠ 0.
-/
theorem walsh_b_zero (f : F → F) (a : F) (ha : a ≠ 0) :
    walsh f a 0 = 0 := by
  -- Since $a \neq 0$, we can substitute $y = a \cdot x$ and get $\sum_x \chi(a \cdot x) = \sum_y \chi(y)$.
  have h_subst : ∑ x : F, χ (a * x) = ∑ y : F, χ y := by
    exact Equiv.sum_comp ( Equiv.mulLeft₀ a ha ) fun x => χ x;
  convert h_subst;
  · exact Finset.sum_congr rfl fun _ _ => by simp +decide [ walsh ] ;
  · -- Since Tr is surjective, there exists some $y_0 \in F$ such that $Tr(y_0) = 1$.
    obtain ⟨y0, hy0⟩ : ∃ y0 : F, Tr y0 = 1 := by
      exact ( Algebra.trace_surjective ( ZMod 2 ) F ) 1;
    -- Since Tr is surjective, for any $y \in F$, we have $\sum_{x \in F} \chi �(x� + y) = \ �sum�_{x \ �in� F} \chi(x �)$�.
    have h_sum_shift : ∀ y : F, ∑ x : F, χ (x + y) = ∑ x : F, χ x := by
      exact fun y => Equiv.sum_comp ( Equiv.addRight y ) fun x => χ x;
    specialize h_sum_shift y0;
    -- Since $\chi(x + � y�0) = -\chi(x)$ for all $x$, we can rewrite the sum.
    have h_sum_neg : ∑ x : F, χ (x + y0) = ∑ x : F, -χ x := by
      apply Finset.sum_congr rfl
      intro x _
      simp [χ, Tr_add, hy0];
      cases Fin.exists_fin_two.mp ⟨ Tr x, rfl ⟩ <;> simp +decide [ * ];
    rw [ Finset.sum_neg_distrib ] at h_sum_neg ; linarith

/-
W(f, 0, b) = 0 for b ≠ 0 when f is bijective.
This uses the Morita self-duality: f being a bijection means
the dual character sum is over a complete set.
-/
theorem walsh_a_zero_perm (f : F → F) (hf : Function.Bijective f)
    (b : F) (hb : b ≠ 0) : walsh f 0 b = 0 := by
  unfold walsh; simp +decide [ hf.injective.eq_iff, hb ] ;
  convert walsh_b_zero ( fun x => x ) b hb using 1;
  exact ( Equiv.sum_comp ( Equiv.ofBijective f hf ) fun x => χ ( b * x ) ) ▸ by simp +decide [ walsh ] ;

/-! ## Layer 3: Character Orthogonality

These are instances of **Schur's lemma** for the character group of `(F, +)`.
In Mathlib's `CategoryTheory`, this corresponds to `Hom(ψ₁, ψ₂) = 0`
for distinct irreducible representations, and the endomorphism ring being `ℤ`.
-/

/-
Orthogonality: Σ_x χ(c·x) = |F| if c = 0, else 0.
-/
theorem χ_sum_eq (c : F) :
    ∑ x : F, χ (c * x) = if c = 0 then (Fintype.card F : ℤ) else 0 := by
  convert walsh_b_zero ( fun x => x ) c using 1;
  split_ifs <;> simp_all +decide [ walsh ];
  exact?

/-
Dual orthogonality (Pontryagin duality).
-/
theorem χ_sum_dual (x : F) :
    ∑ c : F, χ (c * x) = if x = 0 then (Fintype.card F : ℤ) else 0 := by
  convert χ_sum_eq x using 1 ; simp +decide [ mul_comm ]

/-! ## Layer 4: AB and APN Definitions -/

/-- A function is **Almost Bent (AB)** if Walsh² values ∈ {0, 2^{n+1}}. -/
noncomputable def IsAB {n : ℕ} (_ : Fintype.card F = 2 ^ n) (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    walsh f a b ^ 2 = 0 ∨ walsh f a b ^ 2 = (2 ^ (n + 1) : ℤ)

/-- A function is **APN** if differential equation has ≤ 2 solutions. -/
def IsAPN (f : F → F) : Prop :=
  ∀ a : F, a ≠ 0 → ∀ b : F,
    Fintype.card {x : F // f (x + a) + f x = b} ≤ 2

/-- Differential count N_f(a, b). -/
noncomputable def diffCount (f : F → F) (a b : F) : ℕ :=
  Fintype.card {x : F // f (x + a) + f x = b}

/-! ## Layer 5: Parseval Identity (Plancherel Theorem)

For bijective f: `Σ_b W(f,a,b)² = |F|²` for any `a ≠ 0`.

This is the **Plancherel theorem** for the Fourier transform on `(F, +)`.
In categorical terms, it says the Fourier functor is an **isometry**
with respect to the L² norm — a consequence of the Morita equivalence
between `F` and `F̂` being unitary.
-/

theorem parseval_perm {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : Function.Bijective f)
    (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh f a b ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  have := @χ_sum_eq F;
  -- Expand W(a,b)² = (Σ_x χ(ax+bf(x)))² = Σ_{x,y} χ(ax+bf(x))·χ(ay+bf(y)) = Σ_{x,y} χ(a(x+y) + b(f(x)+f(y))) using χ_mul.
  have h_expand : ∑ b : F, (walsh f a b) ^ 2 = ∑ x : F, ∑ y : F, χ (a * (x + y)) * ∑ b : F, χ (b * (f x + f y)) := by
    have h_expand : ∀ b : F, (walsh f a b) ^ 2 = ∑ x : F, ∑ y : F, χ (a * x + b * f x) * χ (a * y + b * f y) := by
      intro b
      simp [walsh];
      simp +decide only [sq, ← Finset.mul_sum _ _ _, ← sum_mul];
    simp +decide only [h_expand, mul_add, Finset.mul_sum _ _ _, mul_comm];
    simp +decide only [← χ_mul, add_comm];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
  -- By_sum_dual, the inner sum is |F| if f(x)+f(y)=0, else 0.
  have h_inner : ∀ x y : F, ∑ b : F, χ (b * (f x + f y)) = if f x + f y = 0 then (Fintype.card F : ℤ) else 0 := by
    exact fun x y => by simpa only [ mul_comm ] using this ( f x + f y ) ;
  -- Since f is bijective, f x + f y = 0 if and only if x = y.
  have h_bijective : ∀ x y : F, f x + f y = 0 ↔ x = y := by
    simp +decide [ add_eq_zero_iff_eq_neg, hf.injective.eq_iff ];
    intro x y; rw [ show -f y = f y from _ ] ; rw [ hf.injective.eq_iff ] ;
    grind;
  simp_all +decide [ sq, Finset.sum_ite ];
  simp +decide [ ← hcard, two_mul, χ ];
  simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
  exact_mod_cast hcard

/-! ## Layer 6: Differential Spectrum -/

/-
Total differential count = |F|. Each x maps to exactly one b.
-/
theorem diffCount_sum (f : F → F) (a : F) :
    ∑ b : F, diffCount f a b = Fintype.card F := by
  unfold diffCount; simp +decide [ Fintype.card_subtype ] ;
  simp +decide only [card_filter];
  rw [ Finset.sum_comm ] ; aesop;

/-
For APN: Σ_b N(a,b)² = 2·|F|.
Solutions come in pairs (x, x+a) in char 2, so N ∈ {0, 2}.
-/
theorem diffCount_sq_sum_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) :
    ∑ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) := by
  -- By definition of $diffCount$, we know that $diffCount f a b \in \{0, 1, 2\}$.
  have h_diffCount_range : ∀ b : F, diffCount f a b ≤ 2 := by
    exact fun b => hf a ha b;
  -- Since $diffCount f a b \in \{0, 1, 2\}$, we have $diffCount f a b ^ 2 = 2 * diffCount f a b$.
  have h_diffCount_sq : ∀ b : F, (diffCount f a b : ℤ) ^ 2 = 2 * (diffCount f a b : ℤ) := by
    intro b
    by_cases h_diffCount_zero : diffCount f a b = 1;
    · obtain ⟨ x, hx ⟩ := Fintype.card_eq_one_iff.mp h_diffCount_zero;
      simp_all +decide [ Subtype.ext_iff ];
      grind;
    · have := h_diffCount_range b; interval_cases _ : diffCount f a b <;> simp_all +decide ;
  simp +decide only [h_diffCount_sq];
  rw_mod_cast [ ← Finset.mul_sum _ _ _, diffCount_sum ]

/-! ## Layer 6.5: Autocorrelation Infrastructure

The scaled autocorrelation `R_b(u) = ∑_x χ(b·D_u f(x))` connects the Walsh
transform to the differential distribution through a three-step Fourier pipeline:
1. W² = Fourier transform of R_b  (walsh_sq_eq_autocorr_sum)
2. Wiener-Khinchin: ∑_a W⁴ = q·∑_u R²  (walsh_fourth_sum_a)
3. Second Parseval: ∑_b R² = q·∑_c N²  (autocorr_sq_sum_b)
-/

/-- The scaled autocorrelation: `R_b(u) = ∑_x χ(b · (f(x+u) + f(x)))`. -/
noncomputable def autocorrScaled (f : F → F) (b u : F) : ℤ :=
  ∑ x : F, χ (b * (f (x + u) + f x))

/-
**Step 1**: `W(a,b)² = ∑_u χ(a·u) · R_b(u)`.
-/
theorem walsh_sq_eq_autocorr_sum (f : F → F) (a b : F) :
    walsh f a b ^ 2 = ∑ u : F, χ (a * u) * autocorrScaled f b u := by
  unfold walsh autocorrScaled; simp +decide [ Finset.sum_mul _ _ _, pow_two ] ;
  simp +decide only [χ_mul, Finset.mul_sum _ _ _, ← sum_product', mul_add];
  refine' Finset.sum_bij ( fun x _ => ( x.2 + x.1, x.2 ) ) _ _ _ _ <;> simp +decide [ mul_add, add_mul, χ_mul ];
  · aesop;
  · exact fun a b => ⟨ a - b, by ring ⟩;
  · intro x y; rw [ show y + ( y + x ) = x by ring_nf; simp +decide [ CharTwo.two_eq_zero ] ] ; ring;

/-
**Step 2 (Wiener-Khinchin)**: `∑_a W(a,b)⁴ = |F| · ∑_u R_b(u)²`.
-/
theorem walsh_fourth_sum_a (f : F → F) (b : F) :
    ∑ a : F, walsh f a b ^ 4 =
      (Fintype.card F : ℤ) * ∑ u : F, autocorrScaled f b u ^ 2 := by
  -- Expand W^4 = (W^2)^2. Use walsh_sq_eq_autocorr_sum to substitute W^2.
  have h_expand : ∀ a : F, (walsh f a b) ^ 4 = (∑ u : F, χ (a * u) * autocorrScaled f b u) ^ 2 := by
    exact fun a => by rw [ ← walsh_sq_eq_autocorr_sum ] ; ring;
  simp +decide only [h_expand, mul_comm, sq];
  -- Use_mul to combine(au)·χ(av) =(a(u+v)).
  have h_combine : ∀ a u v : F, χ (a * u) * χ (a * v) = χ (a * (u + v)) := by
    simp +decide [ mul_add, χ_mul ];
  -- Factor out the autocorrScaled terms and sum over a using_sum_eq.
  have h_sum_a : ∀ u v : F, ∑ a : F, χ (a * (u + v)) = if u + v = 0 then (Fintype.card F : ℤ) else 0 := by
    exact?;
  simp +decide only [mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun u hu => _;
  rw [ Finset.sum_comm ];
  rw [ Finset.sum_eq_single u ] <;> simp_all +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  · simp +decide [ ← two_mul, CharTwo.two_eq_zero ] ; ring;
  · grind

/-
**Step 3 (Second Parseval)**: `∑_b R_b(u)² = |F| · ∑_c N(u,c)²`.
-/
theorem autocorr_sq_sum_b (f : F → F) (u : F) :
    ∑ b : F, autocorrScaled f b u ^ 2 =
      (Fintype.card F : ℤ) * ∑ c : F, (diffCount f u c : ℤ) ^ 2 := by
  unfold autocorrScaled;
  simp +decide only [pow_two, sum_mul _ _ _];
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ x : F, ∑ i : F, ∑ j : F, χ (x * (f (i + u) + f i)) * χ (x * (f (j + u) + f j)) = ∑ i : F, ∑ j : F, ∑ x : F, χ (x * (f (i + u) + f i + f (j + u) + f j)) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro x hx; rw [ Finset.sum_comm ] ; congr; ext y; congr; ext z; rw [ ← χ_mul ] ; ring;
  -- Apply the orthogonality relation to the inner sum.
  have h_inner : ∀ i j : F, ∑ x : F, χ (x * (f (i + u) + f i + f (j + u) + f j)) = if f (i + u) + f i = f (j + u) + f j then (Fintype.card F : ℤ) else 0 := by
    intro i j; split_ifs with h; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
    · simp +decide [ add_assoc, add_left_comm, add_comm ];
      rw [ ← add_assoc, ← two_mul, ← two_mul ];
      rw [ show ( 2 : F ) = 0 by exact CharTwo.two_eq_zero ] ; simp +decide [ χ ] ;
    · convert χ_sum_eq ( f ( i + u ) + f i + f ( j + u ) + f j ) using 1 ; ring;
      · ac_rfl;
      · grind;
  simp_all +decide [ Finset.sum_ite ];
  convert h_fubini using 1;
  · simp +decide only [Finset.mul_sum _ _ _];
  · simp +decide only [diffCount, Fintype.card_subtype, mul_comm];
    simp +decide only [card_filter];
    simp +decide only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_sum _ _ _];
    rw [ Finset.sum_comm ];
    simp +decide [ Finset.sum_ite ];
    simp +decide only [eq_comm, mul_comm]

/-- N(0,0) = |F|. -/
theorem diffCount_zero_zero (f : F → F) :
    diffCount f 0 0 = Fintype.card F := by
  unfold diffCount; simp only [add_zero]
  rw [Fintype.card_subtype]; simp [CharTwo.add_self_eq_zero, Finset.card_univ]

/-- N(0,b) = 0 for b ≠ 0. -/
theorem diffCount_zero_ne (f : F → F) (b : F) (hb : b ≠ 0) :
    diffCount f 0 b = 0 := by
  unfold diffCount; rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨x, hx⟩ => by simp [CharTwo.add_self_eq_zero] at hx; exact hb hx.symm⟩

/-- ∑_b N(0,b)² = |F|². -/
theorem diffCount_zero_sq_sum (f : F → F) :
    ∑ b : F, (diffCount f 0 b : ℤ) ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  rw [Finset.sum_eq_single (0 : F)]
  · simp [diffCount_zero_zero]
  · intro b _ hb; simp [diffCount_zero_ne f b hb]
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- Total ∑_{u,b} N(u,b)² for APN = q² + (q-1)·2q. -/
theorem diffCount_sq_total_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) :
    ∑ u : F, ∑ b : F, (diffCount f u b : ℤ) ^ 2 =
    (Fintype.card F : ℤ) ^ 2 +
      ((Fintype.card F : ℤ) - 1) * (2 * (Fintype.card F : ℤ)) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  rw [diffCount_zero_sq_sum]; congr 1
  rw [Finset.sum_congr rfl (fun u hu => diffCount_sq_sum_apn hcard f hf u
    (Finset.ne_of_mem_erase hu))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  rw [nsmul_eq_mul]; push_cast
  have hq : (1 : ℤ) ≤ Fintype.card F := by exact_mod_cast le_of_lt Fintype.one_lt_card
  rw [Nat.cast_sub (by exact_mod_cast hq)]; ring

/-! ## Layer 7: Fourth Moment (Caramello Bridge)

The fourth moment identity `∑_{a,b} W(a,b)⁴ = |F|² · ∑_{a,b} N(a,b)²`
is proved via the autocorrelation pipeline (Steps 1-3 above).
-/

/-- **Double-sum fourth moment identity** (via autocorrelation pipeline):
    `∑_{a,b} W(a,b)⁴ = |F|² · ∑_{a,b} N(a,b)²`. -/
theorem double_sum_fourth_moment {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) :
    ∑ a : F, ∑ b : F, walsh f a b ^ 4 =
      (Fintype.card F : ℤ) ^ 2 * ∑ a : F, ∑ b : F, (diffCount f a b : ℤ) ^ 2 := by
  rw [Finset.sum_comm]
  simp_rw [walsh_fourth_sum_a]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [autocorr_sq_sum_b]
  rw [← Finset.mul_sum]; ring

/-
For power permutations: Σ_b W(a,b)⁴ is the same for all a ≠ 0.
This follows from walsh_pow_scaling: W(a,b) = W(1, b/a^d).
-/
theorem walsh_pow_fourth_uniform (d : ℕ) (a₁ a₂ : F)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    ∑ b : F, walsh (· ^ d) a₁ b ^ 4 = ∑ b : F, walsh (· ^ d) a₂ b ^ 4 := by
  have h_walsh_pow_scaling : ∀ (a b t : F), t ≠ 0 → walsh (fun x => x ^ d) (a * t) (b * t ^ d) = walsh (fun x => x ^ d) a b := by
    intros a b t ht_ne_zero
    simp (config := { decide := true }) only [walsh];
    convert ( Equiv.sum_comp ( Equiv.mulLeft₀ t ht_ne_zero ) fun x => χ ( a * x + b * x ^ d ) ) using 1 ; simp +decide [ mul_assoc, mul_left_comm ];
    simp +decide only [mul_pow];
  -- By Lemma 2.1, we can rewrite the sums using the scaling property.
  have h_scale : ∀ (b : F), walsh (fun x => x ^ d) a₂ b = walsh (fun x => x ^ d) a₁ (b * (a₁ / a₂) ^ d) := by
    intro b; specialize h_walsh_pow_scaling a₁ ( b * ( a₁ / a₂ ) ^ d ) ( a₂ / a₁ ) ; simp_all +decide [ mul_div_cancel₀ ] ;
    simp_all +decide [ mul_assoc, div_pow ];
  rw [ ← Equiv.sum_comp ( Equiv.mulRight₀ ( ( a₁ / a₂ ) ^ d ) ( by aesop ) ) ] ; simp +decide [ h_scale ]

/-
For APN power permutations: the fourth moment = 2·|F|³.

Derived from the double-sum identity + power function uniformity:
1. `W(a,b) = W(1, b/a^d)` for `a ≠ 0` (walsh_pow_scaling)
2. So `∑_b W(a,b)⁴` is the same for all `a ≠ 0`
3. `W(0,b) = 0` for `b ≠ 0`, `W(0,0) = q`
4. From double sum: `(q-1)·S + q⁴ = q²·((q-1)·2q + q²)`, solve `S = 2q³`
-/
theorem fourth_moment_apn {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (d : ℕ) (hbij : Function.Bijective (· ^ d : F → F))
    (hapn : IsAPN (· ^ d : F → F)) (a : F) (ha : a ≠ 0) :
    ∑ b : F, walsh (· ^ d : F → F) a b ^ 4 =
      2 * (Fintype.card F : ℤ) ^ 3 := by
  have := @double_sum_fourth_moment F;
  have := @diffCount_sq_total_apn F;
  have := @walsh_pow_fourth_uniform F;
  rename_i h₁ h₂;
  specialize h₁ hcard ( fun x => x ^ d );
  -- By the uniformity of the fourth moment, we can replace each term in the sum by S.
  have h_uniform : ∑ a' : F, ∑ b : F, walsh (fun x => x ^ d) a' b ^ 4 = (Fintype.card F : ℤ) ^ 4 + (Fintype.card F - 1) * ∑ b : F, walsh (fun x => x ^ d) a b ^ 4 := by
    rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ 0 ) ];
    rw [ Finset.sum_congr rfl fun x hx => this d x a ( by aesop ) ha ];
    rw [ Finset.sum_eq_single 0 ] <;> simp +decide [ *, Finset.card_sdiff ];
    · rw [ walsh_zero_zero ] ; aesop;
    · exact fun b hb => walsh_a_zero_perm _ hbij _ hb;
  rw [ h₂ hcard _ hapn ] at h₁;
  nlinarith [ show ( Fintype.card F : ) > 1 from mod_cast Fintype.one_lt_card ]

/-! ## Layer 8: Power Function Symmetries

These symmetries arise from the **Galois action** of `Gal(F/GF(2))`
on the Walsh transform. The Frobenius `φ : x ↦ x²` generates
this Galois group, and its action on Walsh coefficients is trivial —
reflecting the fact that `φ` acts as the identity on `GF(2)`.

In categorical terms: the Walsh transform factors through the
**coinvariants** of the Galois action, and the Frobenius acts
trivially because the trace is Galois-invariant.
-/

/-
Frobenius invariance of χ: χ(x²) = χ(x).
This follows from `Tr(x²) = Tr(x)` since the Frobenius
is a Galois automorphism and Tr is Galois-invariant.
-/
theorem χ_sq_eq (x : F) : χ (x ^ 2) = χ x := by
  -- Since Tr is linear, we have Tr(x^2) = Tr(x).
  have h_tr_sq : Tr (x ^ 2) = Tr x := by
    convert Algebra.trace_eq_of_algEquiv _ _;
    swap;
    constructor;
    case convert_9.toEquiv => exact Equiv.ofBijective ( fun x => x ^ 2 ) ⟨ fun x y hxy => by
      grind, fun x => by
      have h_frobenius_surjective : Function.Surjective (fun x : F => x ^ 2) := by
        exact Finite.injective_iff_surjective.mp ( fun x y hxy => by simpa [ sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq ] using hxy );
      exact h_frobenius_surjective x ⟩;
    all_goals norm_num [ mul_pow, add_sq ];
    · exact fun x y => Or.inl <| Or.inl <| CharP.cast_eq_zero F 2;
    · exact fun r => by fin_cases r <;> simp +decide ;
  grind +locals

/-
Power function scaling: W(a·t, b·t^d) = W(a, b).
The multiplicative group acts on Walsh coefficients via scaling.
-/
theorem walsh_pow_scaling (d : ℕ) (a b t : F) (ht : t ≠ 0) :
    walsh (· ^ d) (a * t) (b * t ^ d) = walsh (· ^ d) a b := by
  -- By changing variables $y = t * x$, we can rewrite the sum.
  have h_change_var : ∑ x : F, χ (a * t * x + b * t ^ d * x ^ d) = ∑ y : F, χ (a * y + b * y ^ d) := by
    have h_bij : Function.Bijective (fun x : F => t * x) := by
      exact ⟨ mul_right_injective₀ ht, mul_left_surjective₀ ht ⟩
    conv_rhs => rw [ ← Equiv.sum_comp ( Equiv.ofBijective _ h_bij ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    exact Finset.sum_congr rfl fun _ _ => by ring;
  exact h_change_var

/-
Frobenius invariance: W(1, c²) = W(1, c).
The Walsh spectrum is constant on Frobenius orbits.
-/
theorem walsh_pow_frob_inv (d : ℕ) (c : F) :
    walsh (· ^ d) 1 (c ^ 2) = walsh (· ^ d) 1 c := by
  -- Since squaring is a bijection in characteristic 2, we can replace $x$ with $y^2$ in the sum.
  have h_bij : ∑ x : F, χ (x + c ^ 2 * x ^ d) = ∑ y : F, χ (y ^ 2 + c ^ 2 * (y ^ 2) ^ d) := by
    have h_bij : Function.Bijective (fun y : F => y ^ 2) := by
      exact ⟨ fun x y hxy => by simpa [ sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq ] using hxy, Finite.injective_iff_surjective.mp ( fun x y hxy => by simpa [ sq_eq_sq_iff_eq_or_eq_neg, CharTwo.neg_eq ] using hxy ) ⟩;
    conv_lhs => rw [ ← Equiv.sum_comp ( Equiv.ofBijective _ h_bij ) ] ;
    rfl;
  -- By the properties of the trace, we know that $\chi(y^2 + c^2 \cdot (y^2)^d) = \chi((y + c \cdot y^d)^2)$.
  have h_trace : ∀ y : F, χ (y ^ 2 + c ^ 2 * (y ^ 2) ^ d) = χ ((y + c * y ^ d) ^ 2) := by
    intro y; ring;
    simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ];
  -- By the properties of the trace, we know that $\chi((y + c \cdot y^d)^2) = \chi(y + c \cdot y^d)$.
  have h_trace_sq : ∀ y : F, χ ((y + c * y ^ d) ^ 2) = χ (y + c * y ^ d) := by
    grind +suggestions;
  unfold walsh; aesop;

/-! ## Layer 9: The Integer Lattice Argument for AB

This is the elegant **moment method** proof. The key algebraic fact:

If `Σ k² = Σ k⁴` for non-negative integer terms `k²`, then
`Σ k²(k²-1) = 0`, forcing each `k² ∈ {0, 1}`.

This is a consequence of `k²(k²-1) ≥ 0` for all integers `k`.
-/

/-- For integers: k²(k²-1) ≥ 0. Used in the AB deduction. -/
theorem sq_mul_sq_sub_one_nonneg (k : ℤ) : 0 ≤ k ^ 2 * (k ^ 2 - 1) := by
  nlinarith [sq_nonneg k, sq_nonneg (k ^ 2 - 1)]

/-
If Σ k² = Σ k⁴ (over a finset) and all are integers, then k² ∈ {0,1}.
-/
theorem eq_zero_or_one_of_sum_sq_eq_sum_fourth
    {ι : Type*} (s : Finset ι) (k : ι → ℤ)
    (h : ∑ i ∈ s, k i ^ 4 = ∑ i ∈ s, k i ^ 2) :
    ∀ i ∈ s, k i ^ 2 = 0 ∨ k i ^ 2 = 1 := by
  intro i hi;
  contrapose! h;
  refine' ne_of_gt ( Finset.sum_lt_sum _ _ );
  · exact fun i _ => by nlinarith [ sq_nonneg ( k i ^ 2 - 1 ) ] ;
  · exact ⟨ i, hi, by cases lt_or_gt_of_ne h.1 <;> cases lt_or_gt_of_ne h.2 <;> nlinarith [ sq_nonneg ( k i ^ 2 - 1 ) ] ⟩

/-
Walsh coefficients are even (|F| = 2ⁿ is even, and W is a sum of ±1).
-/
theorem walsh_even (f : F → F) (a b : F) : 2 ∣ walsh f a b := by
  have h_even : ∑ x : F, (if Tr (a * x + b * f x) = 0 then 1 else -1) ≡ 0 [ZMOD 2] := by
    simp +decide [ Int.modEq_zero_iff_dvd, Finset.sum_ite ];
    simp +decide [ ← even_iff_two_dvd, parity_simps ];
    simp +decide [ Finset.filter_not, Finset.card_sdiff ];
    rw [ Nat.even_sub ( Finset.card_le_univ _ ) ];
    have h_card : Fintype.card F = 2 ^ (Module.finrank (ZMod 2) F) := by
      have h_card : Fintype.card F = Fintype.card (Fin (Module.finrank (ZMod 2) F) → ZMod 2) := by
        exact Fintype.card_congr ( ( Module.finBasis ( ZMod 2 ) F ).equivFun );
      aesop;
    rcases k : Module.finrank ( ZMod 2 ) F with ( _ | _ | k ) <;> simp_all +decide [ Nat.even_pow ];
    exact absurd h_card ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
  convert Int.dvd_of_emod_eq_zero h_even using 1

/-! ## Layer 10: AB Deduction from Moments + Divisibility

The clean algebraic argument: divisibility forces Walsh values
onto an integer lattice, and the moment constraints pin them down.
-/

/-
**AB from moments**: The integer lattice argument.
Given Parseval, fourth moment, and divisibility, the function is AB.

This is the **Caramello bridge theorem**: the Morita equivalence
between primal (differential) and dual (spectral) theories,
combined with integrality constraints from the Galois action,
forces the spectral values onto a rank-1 lattice.
-/
theorem ab_from_moments {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hodd : Odd n) (hn : n ≥ 1)
    (hparseval : ∀ a, a ≠ 0 →
      ∑ b : F, walsh f a b ^ 2 = (Fintype.card F : ℤ) ^ 2)
    (hfourth : ∀ a, a ≠ 0 →
      ∑ b : F, walsh f a b ^ 4 = 2 * (Fintype.card F : ℤ) ^ 3)
    (hdiv : ∀ a b, (2 : ℤ) ^ ((n + 1) / 2) ∣ walsh f a b) :
    IsAB hcard f := by
  intro a ha b;
  -- Write W(a,b) = � �2^{(n+1)/2} · k_b for integers k_b (from hdiv).
  obtain ⟨k, hk⟩ : ∃ k : F → ℤ, ∀ b, walsh f a b = 2 ^ ((n + 1) / 2) * k b := by
    exact ⟨ fun b => Classical.choose ( hdiv a b ), fun b => Classical.choose_spec ( hdiv a b ) ⟩;
  -- Then: k_b �²� = 2^{n-1} (from Parseval) and k �_b = 2^{n-1} (from fourth moment).
  have hsum_sq : ∑ b, k b ^ 2 = 2 ^ (n - 1) := by
    have := hparseval a ha; simp_all +decide [ mul_pow, Finset.mul_sum _ _ _ ] ;
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.mul_sum _ _ _ ] at this; simp_all +decide [ ← mul_assoc, ← pow_mul' ] ;
    rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ];
    · exact mul_left_cancel₀ ( pow_ne_zero ( 2 * ( c + 1 ) ) two_ne_zero ) ( by ring_nf at *; linarith );
    · exact absurd hodd ( by simp +decide [ parity_simps ] )
  have hsum_fourth : ∑ b, k b ^ 4 = 2 ^ (n - 1) := by
    rcases n with ( _ | n ) <;> simp_all +decide [ Nat.pow_succ', mul_pow ];
    have := hfourth a ha; simp_all +decide [ mul_pow, Finset.mul_sum _ _ _ ] ;
    rw [ ← Finset.mul_sum _ _ _ ] at this; rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_div ] ; ring_nf at *;
    · exact mul_left_cancel₀ ( pow_ne_zero ( c * 4 ) two_ne_zero ) ( by ring_nf at *; linarith );
    · exact absurd hodd ( by simp +decide [ parity_simps ] );
  -- So k_b⁴ = k_b², hence by eq_zero_or_one_of_sum_sq_eq_sum_four �th�, k_b² ∈ {0,1}.
  have h_k_sq : ∀ b, k b ^ 2 = 0 ∨ k b ^ 2 = 1 := by
    convert eq_zero_or_one_of_sum_sq_eq_sum_fourth Finset.univ k _ using 1;
    · simp +decide;
    · rw [hsum_fourth, hsum_sq];
  cases h_k_sq b <;> simp +decide [ *, mul_pow ];
  rw [ ← pow_mul, Nat.div_mul_cancel ( even_iff_two_dvd.mp ( by simpa [ parity_simps ] using hodd ) ) ]

end WalshAB

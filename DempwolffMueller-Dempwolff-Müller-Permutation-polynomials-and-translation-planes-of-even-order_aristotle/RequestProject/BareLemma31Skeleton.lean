import Mathlib
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg

/-!
# Foundational Layer FL-A: Bare-Function Lemma 3.1

**This is the single most impactful foundational layer.** It collapses
4 sorries: `adjoint_swap_bij`, `adjoint_swap_bijective`,
`LxXk'_bijective_v2`, `LxXk'_bijective`.

## Motivation

`lemma_3_1` in `Lemma31.lean` is proved using `F →ₗ[K] F` (Mathlib LinearMap).
But the actual sorries work with bare `F → F` functions and `frobSum` (which maps
`F → F`, not `F → K`). Rather than wrapping everything in LinearMap (hard, boilerplate),
we reprove the core argument directly for bare additive functions.

## Strategy

Mirror the 8-layer proof of `lemma_3_1` but with:
- Bare additive functions `L : F → F` instead of `F →ₗ[K] F`
- `frobSum p n : F → F` as the trace form instead of `T : F →ₗ[K] K`
- Plain multiplicativity `∀ a b, M(ab) = M(a)·M(b)` instead of monoid hom

## DAG Structure

```
  FL-A.1..A.8 (independent easy lemmas)
      │
      ├──► FL-A.9..A.13 (meh: core equivalences)
      │
      └──► FL-A.14..A.16 (assembly)
               │
               └──► adjoint_swap_bij
```

## Sorries collapsed

- `adjoint_swap_bij` (AdjointBij.lean)
- `adjoint_swap_bijective` (Thm32Kprime.lean)
- `LxXk'_bijective_v2` (Thm32Kprime.lean)
- `LxXk'_bijective` (Thm32.lean)
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════════════
-- FL-A.2 [easy]: DeltaBare definition
-- ═══════════════════════════════════════════════════

/-- The Δ operator for bare functions: Δ_{L,M,y}(x) = L(x·y) · M(y). -/
def DeltaBare' (L : F → F) (M : F → F) (y : F) (x : F) : F :=
  L (x * y) * M y

/-
═══════════════════════════════════════════════════
FL-A.3 [easy]: Additive + trivial kernel ⟹ injective
═══════════════════════════════════════════════════

An additive function with trivial kernel is injective.
-/
lemma additive_injective_of_ker_trivial
    (f : F → F) (hf_add : ∀ a b, f (a + b) = f a + f b)
    (hker : ∀ x, f x = 0 → x = 0) :
    Function.Injective f := by
      intro a b hab;
      exact sub_eq_zero.mp ( hker ( a - b ) ( by simpa [ hab, sub_eq_add_neg ] using hf_add ( a - b ) b ) )

/-
Proof: f(a) = f(b) ⟹ f(a-b) = f(a) + f(-b) = f(a) - f(b) = 0 ⟹ a-b = 0.
Uses hf_add, sub = add neg, f(-x) = -f(x) from additivity.

═══════════════════════════════════════════════════
FL-A.4 [easy]: P(x·y) = Δ_y(x) · M(x)
═══════════════════════════════════════════════════

The product identity: L(xy)·M(xy) = Δ_y(x) · M(x) when M is multiplicative.
-/
lemma PBare_mul_eq'
    (L M : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (x y : F) :
    L (x * y) * M (x * y) = DeltaBare' L M y x * M x := by
      unfold DeltaBare';
      grind +extAll

/-
Proof: Unfold DeltaBare'. RHS = L(xy)·M(y)·M(x).
LHS = L(xy)·M(xy) = L(xy)·M(x)·M(y) = L(xy)·M(y)·M(x). ring.

═══════════════════════════════════════════════════
FL-A.5 [meh]: Δ-difference zero implies x = 0
═══════════════════════════════════════════════════

If P = L·M is injective and Δ_{y₁}(x) = Δ_{y₂}(x), then x = 0.
    (When M is multiplicative and injective.)
-/
lemma DeltaBare_sub_zero_imp_zero'
    (L M : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_inj : Function.Injective M)
    (hP_inj : Function.Injective (fun x => L x * M x))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂)
    {x : F} (h : DeltaBare' L M y₁ x = DeltaBare' L M y₂ x) :
    x = 0 := by
      unfold DeltaBare' at h;
      have := @hP_inj ( x * y₁ ) ( x * y₂ ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      exact this ( by linear_combination' h * M x )

/-
Proof: From PBare_mul_eq', P(xy₁) = Δ_{y₁}(x)·M(x) and P(xy₂) = Δ_{y₂}(x)·M(x).
If Δ_{y₁}(x) = Δ_{y₂}(x), then P(xy₁)·M(x)⁻¹ = P(xy₂)·M(x)⁻¹.
Case x = 0: done.
Case x ≠ 0: M(x) ≠ 0 (M injective, M(0) = 0), so cancel M(x):
P(xy₁) = P(xy₂), so xy₁ = xy₂ (P injective), so x(y₁-y₂) = 0.
Since y₁ ≠ y₂ and F is a field, x = 0. Contradiction.

═══════════════════════════════════════════════════
FL-A.6 [easy]: Δ-difference is additive
═══════════════════════════════════════════════════

The map x ↦ Δ_{y₁}(x) - Δ_{y₂}(x) is additive when L is additive.
-/
lemma DeltaBare_sub_additive'
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (M : F → F) (y₁ y₂ : F) (a b : F) :
    (DeltaBare' L M y₁ (a + b) - DeltaBare' L M y₂ (a + b)) =
    (DeltaBare' L M y₁ a - DeltaBare' L M y₂ a) +
    (DeltaBare' L M y₁ b - DeltaBare' L M y₂ b) := by
      unfold DeltaBare';
      rw [ add_mul, add_mul, hL_add, hL_add ] ; ring

/-
Proof: Expand DeltaBare'. L((a+b)·y₁)·M(y₁) = (L(ay₁) + L(by₁))·M(y₁)
= L(ay₁)·M(y₁) + L(by₁)·M(y₁). Same for y₂. Distribute and regroup. ring.

═══════════════════════════════════════════════════
FL-A.7 [easy]: Δ is additive
═══════════════════════════════════════════════════

Δ_{y}(a+b) = Δ_{y}(a) + Δ_{y}(b) when L is additive.
-/
lemma DeltaBare_is_additive'
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (M : F → F) (y : F) (a b : F) :
    DeltaBare' L M y (a + b) = DeltaBare' L M y a + DeltaBare' L M y b := by
      unfold DeltaBare'; simp +decide [ hL_add, add_mul ] ;

-- Proof: Expand DeltaBare'. L((a+b)y)·M(y) = (L(ay) + L(by))·M(y)
-- = L(ay)·M(y) + L(by)·M(y). Uses add_mul.

-- ═══════════════════════════════════════════════════
-- FL-A.8 [easy]: Injective on Fintype ⟹ bijective
-- ═══════════════════════════════════════════════════

/-- On a finite type, injective ⟹ bijective. -/
lemma bij_of_inj_fintype' (f : F → F) (hinj : Function.Injective f) :
    Function.Bijective f :=
  ⟨hinj, (Finite.injective_iff_surjective).mp hinj⟩

/-
═══════════════════════════════════════════════════
FL-A.9 [meh]: P injective ⟹ Δ-differences bijective
═══════════════════════════════════════════════════

P injective ⟹ all Δ-differences are bijective.
-/
lemma P_inj_imp_DeltaBare_sub_bij'
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (M : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_inj : Function.Injective M)
    (hP_inj : Function.Injective (fun x => L x * M x))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂) :
    Function.Bijective (fun x => DeltaBare' L M y₁ x - DeltaBare' L M y₂ x) := by
      grind +suggestions

/-
Proof chain:
1. The diff map is additive (FL-A.6)
2. Its kernel is trivial: if diff = 0 at x, then x = 0 (FL-A.5)
3. Additive + ker trivial ⟹ injective (FL-A.3)
4. Injective on Fintype ⟹ bijective (FL-A.8)

═══════════════════════════════════════════════════
FL-A.10 [meh]: Δ-differences bijective ⟹ P injective
═══════════════════════════════════════════════════

All Δ-differences bijective ⟹ P is injective.
-/
lemma DeltaBare_sub_bij_imp_P_inj'
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL0 : L 0 = 0)
    (M : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_inj : Function.Injective M)
    (hDelta : ∀ y₁ y₂ : F, y₁ ≠ y₂ →
      Function.Bijective (fun x => DeltaBare' L M y₁ x - DeltaBare' L M y₂ x)) :
    Function.Injective (fun x => L x * M x) := by
      -- Assume that L(a) * M(a) = L(b) * M(b) with a ≠ b. By PBare_mul_eq', we have DeltaBare'(L,M,a,1) * M(1) = DeltaBare'(L,M,b,1) * M(1).
      intro a b hab
      by_contra h_contra
      have h_eq : DeltaBare' L M a 1 * M 1 = DeltaBare' L M b 1 * M 1 := by
        unfold DeltaBare' at *; aesop;
      have := hDelta a b h_contra; have := this.1; simp_all +decide [ sub_eq_iff_eq_add ] ;
      have := @this 1 0 ; simp_all +decide [ sub_eq_iff_eq_add ] ;
      simp_all +decide [ DeltaBare' ]

/-
Proof: Suppose L(a)·M(a) = L(b)·M(b) with a ≠ b.
By PBare_mul_eq': Δ_a(1) · M(1) = L(1·a)·M(a) = P(a).
Similarly Δ_b(1) · M(1) = P(b).
So Δ_a(1)·M(1) = Δ_b(1)·M(1), hence Δ_a(1) = Δ_b(1) (M(1) ≠ 0).
Then diff(1) = 0, but diff is bijective (hence injective), so 1 = 0. ⊥.

═══════════════════════════════════════════════════
FL-A.11 [meh]: Trace adjoint identity for bare Δ
═══════════════════════════════════════════════════

Tr(Δ_{L₁,M,y}(u) · v) = Tr(u · Δ_{L₂,M⁻¹,M(y)}(v)).
    The core trace-adjoint identity connecting L₁-Δ and L₂-Δ.
-/
lemma DeltaBare_trace_adjoint'
    {n : ℕ} (hn : Fintype.card F = p ^ n)
    (L₁ L₂ : F → F)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (M Minv : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hMinv_left : ∀ x, Minv (M x) = x)
    (u v y : F) :
    frobSum p n (DeltaBare' L₁ M y u * v) =
    frobSum p n (u * DeltaBare' L₂ Minv (M y) v) := by
      -- By definition of DeltaBare', we can rewrite the expressions.
      simp only [DeltaBare'] at *;
      have := hAdj ( u * y ) ( v * M y ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;

/-
Proof sketch:
LHS = Tr(L₁(u·y)·M(y)·v)
Apply hAdj with w = u·y, z = M(y)·v:
= Tr(u·y · L₂(M(y)·v))
RHS = Tr(u · L₂(v·M(y))·Minv(M(y)))
= Tr(u · L₂(v·M(y))·y)          [since Minv(M(y)) = y]
Both equal Tr(u · y · L₂(v·M(y))) after commuting multiplication.
Uses: mul_comm, mul_assoc.

═══════════════════════════════════════════════════
FL-A.12 [meh]: Additive bijective ↔ adjoint bijective
═══════════════════════════════════════════════════

An additive map on F is bijective iff its frobSum-adjoint is bijective.
    Uses nondegeneracy of frobSum.
-/
lemma additive_bij_iff_adj_bij'
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (A Aadj : F → F)
    (hA_add : ∀ a b, A (a + b) = A a + A b)
    (hAadj_add : ∀ a b, Aadj (a + b) = Aadj a + Aadj b)
    (hTadj : ∀ x y, frobSum p n (A x * y) = frobSum p n (x * Aadj y))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0) :
    Function.Bijective A ↔ Function.Bijective Aadj := by
      constructor <;> intro h;
      · -- By definition of adjoint, if A is bijective, then Aadj is injective.
        have hAadj_inj : Function.Injective Aadj := by
          intro x y hxy
          by_contra h_neq
          obtain ⟨z, hz⟩ : ∃ z : F, frobSum p n (z * (x - y)) ≠ 0 := by
            simpa only [ mul_comm ] using hTnd ( x - y ) ( sub_ne_zero.mpr h_neq );
          obtain ⟨ w, rfl ⟩ := h.2 z; simp_all +decide [ mul_sub ] ;
          simp_all +decide [ ← mul_sub, frobSum ];
          have := hAadj_add ( x - y ) y; simp_all +decide [ sub_eq_iff_eq_add ] ;
          exact hz ( Finset.sum_eq_zero fun i hi => by rw [ zero_pow ( pow_ne_zero _ hp.1.ne_zero ) ] );
        exact ⟨ hAadj_inj, Finite.injective_iff_surjective.mp hAadj_inj ⟩;
      · -- Assume A is not injective. Then there exists x ≠ 0 such that A(x) = 0.
        by_contra h_not_inj
        obtain ⟨x, hx_ne_zero, hx_zero⟩ : ∃ x : F, x ≠ 0 ∧ A x = 0 := by
          have h_not_inj : ¬Function.Injective A := by
            exact fun h_inj => h_not_inj ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩;
          contrapose! h_not_inj;
          intro x y hxy; have := hA_add ( x - y ) y; simp_all +decide ;
          exact sub_eq_zero.mp ( Classical.not_not.1 fun h => h_not_inj _ h this );
        -- By nondegeneracy (hTnd), x = 0.
        have hx_zero_trace : ∀ y : F, (frobSum p n (x * Aadj y)) = 0 := by
          grind +suggestions;
        exact hTnd x hx_ne_zero |> fun ⟨ y, hy ⟩ => hy <| by obtain ⟨ z, rfl ⟩ := h.2 y; exact hx_zero_trace z;

/-
Proof: On Fintype, bijective ↔ injective.
Direction A bij ⟹ Aadj inj:
Suppose Aadj(x) = 0 and x ≠ 0. By nondeg, ∃ y with Tr(x·y) ≠ 0.
But Tr(x·y) = Tr(A⁻¹(A(x))·y) = ... need A surjective.
Better: Suppose Aadj(x) = 0. Then ∀ y, Tr(A(y)·x) = Tr(y·Aadj(x)) = 0.
Since A is surjective, ∀ z, Tr(z·x) = 0. By nondeg, x = 0.
Direction Aadj bij ⟹ A inj: symmetric argument.

═══════════════════════════════════════════════════
FL-A.12a [easy]: Helper: additive map sends 0 to 0
═══════════════════════════════════════════════════
-/
lemma additive_zero (f : F → F) (hf : ∀ a b, f (a + b) = f a + f b) :
    f 0 = 0 := by
      simpa using hf 0 0

/-
Proof: f(0) = f(0+0) = f(0) + f(0), so f(0) = 0.

═══════════════════════════════════════════════════
FL-A.12b [easy]: Helper: additive map sends neg to neg
═══════════════════════════════════════════════════
-/
lemma additive_neg (f : F → F) (hf : ∀ a b, f (a + b) = f a + f b)
    (x : F) : f (-x) = -(f x) := by
      have := hf 0 x; have := hf ( -x ) x; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      exact eq_neg_of_add_eq_zero_left this.symm

/-
Proof: f(0) = f(x + (-x)) = f(x) + f(-x) = 0, so f(-x) = -f(x).

═══════════════════════════════════════════════════
FL-A.12c [easy]: Helper: additive map distributes over sub
═══════════════════════════════════════════════════
-/
lemma additive_sub (f : F → F) (hf : ∀ a b, f (a + b) = f a + f b)
    (x y : F) : f (x - y) = f x - f y := by
      have := hf 0 0; simp_all +decide [ sub_eq_add_neg ] ;
      exact?

/-
Proof: x - y = x + (-y), so f(x-y) = f(x) + f(-y) = f(x) - f(y).

═══════════════════════════════════════════════════
FL-A.13 [meh]: Δ-diff bijective ↔ adjoint Δ-diff bijective
═══════════════════════════════════════════════════

The Δ-difference for (L₁, M) is bijective iff the Δ-difference for
    (L₂, M⁻¹, M(·)) is bijective. Combines FL-A.11 and FL-A.12.
-/
lemma DeltaBare_sub_bij_iff_adj'
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F)
    (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (M Minv : F → F) (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hMinv_left : ∀ x, Minv (M x) = x)
    (y₁ y₂ : F) :
    Function.Bijective (fun x => DeltaBare' L₁ M y₁ x - DeltaBare' L₁ M y₂ x) ↔
    Function.Bijective (fun x => DeltaBare' L₂ Minv (M y₁) x - DeltaBare' L₂ Minv (M y₂) x) := by
      convert additive_bij_iff_adj_bij' p hn hn1 _ _ _ _ _ _ using 1;
      · exact?;
      · exact?;
      · intro x y; have := DeltaBare_trace_adjoint' p hn L₁ L₂ hAdj M Minv hM_mul hMinv_left x y; have := DeltaBare_trace_adjoint' p hn L₁ L₂ hAdj M Minv hM_mul hMinv_left x y; simp_all +decide [ DeltaBare' ] ;
        convert congr_arg₂ ( · - · ) ( this y₁ ) ( this y₂ ) using 1 <;> ring;
        · have h_linear : ∀ (a b : F), frobSum p n (a - b) = frobSum p n a - frobSum p n b := by
            intro a b; simp +decide [ sub_eq_add_neg, frobSum_add, frobSum_neg ] ;
          exact h_linear _ _;
        · simp +decide [ frobSum, Finset.sum_sub_distrib ] ;
          simp +decide only [sub_pow_char_pow, sum_sub_distrib];
      · exact hTnd

/-
Proof:
1. Both diff maps are additive (FL-A.6 applied twice).
2. They are trace-adjoints: by FL-A.11, for each y:
Tr(Δ_{L₁,M,y}(u)·v) = Tr(u·Δ_{L₂,Minv,M(y)}(v)).
Taking differences: Tr((Δ_{y₁} - Δ_{y₂})(u)·v) = Tr(u·(Δ*_{M(y₁)} - Δ*_{M(y₂)})(v)).
3. Apply FL-A.12: additive bij ↔ adj bij.

═══════════════════════════════════════════════════
FL-A.14 [easy]: Quantifier relabelling via bijection
═══════════════════════════════════════════════════

∀ y₁ ≠ y₂, Q(M(y₁), M(y₂)) ↔ ∀ z₁ ≠ z₂, Q(z₁, z₂) when M is bijective.
-/
lemma forall_ne_bij_bare'
    {M : F → F} (hMbij : Function.Bijective M)
    {Q : F → F → Prop} :
    (∀ y₁ y₂, y₁ ≠ y₂ → Q (M y₁) (M y₂)) ↔ (∀ z₁ z₂, z₁ ≠ z₂ → Q z₁ z₂) := by
      constructor <;> intro h;
      · exact fun z₁ z₂ hne => by obtain ⟨ y₁, rfl ⟩ := hMbij.2 z₁; obtain ⟨ y₂, rfl ⟩ := hMbij.2 z₂; exact h y₁ y₂ ( by aesop ) ;
      · exact fun y₁ y₂ hy => h _ _ ( hMbij.injective.ne hy )

/-
Proof:
(⟹): Given z₁ ≠ z₂, by surjectivity ∃ y₁ y₂ with M(yᵢ) = zᵢ.
By injectivity y₁ ≠ y₂. Apply hypothesis.
(⟸): Given y₁ ≠ y₂, M(y₁) ≠ M(y₂) by injectivity. Apply hypothesis.

═══════════════════════════════════════════════════
FL-A.15 [easy]: Reverse power round-trip
═══════════════════════════════════════════════════

(x^l)^e = x when e·l ≡ 1 mod (|F|-1) and x ≠ 0.
-/
lemma pow_inv_round_trip' (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    {x : F} (hx : x ≠ 0) :
    (x ^ l) ^ e = x := by
      convert pow_pow_eq_self _ _ using 1;
      exacts [ inferInstance, by simpa only [ mul_comm ] using hel, hx ]

/-
Proof: l·e ≡ e·l ≡ 1 mod (|F|-1) by mul_comm. Then pow_pow_eq_self.

═══════════════════════════════════════════════════
FL-A.15b [easy]: M(0) = 0 for multiplicative injective M
═══════════════════════════════════════════════════
-/
lemma mul_map_zero_bare {M : F → F}
    (hM_mul : ∀ a b, M (a * b) = M a * M b)
    (hM_inj : Function.Injective M) :
    M 0 = 0 := by
      by_contra hM0_ne_zero
      have hM0_one : M 0 = 1 := by
        simpa [ hM0_ne_zero ] using hM_mul 0 0
      generalize_proofs at *;
      have hM_const : ∀ x : F, M x = 1 := by
        intro x
        have := hM_mul 0 x
        simp [hM0_one] at this
        exact this.symm ▸ by
          rfl
      generalize_proofs at *; exact (by
      exact absurd ( @hM_inj 0 1 ) ( by simp +decide [ hM_const ] ));

/-
Proof: M(0) = M(0·0) = M(0)·M(0), so M(0)·(M(0)-1) = 0.
Either M(0) = 0 or M(0) = 1. If M(0) = 1, then M(0) = M(1·1) = M(1)·M(1),
so M(1) = 1 as well. But then M(0) = M(1) contradicts injectivity (if char > 0).
Actually: M(0) = M(0·0) = M(0)², so M(0)(M(0)-1) = 0, so M(0) = 0 or 1.
If M(0) = 1 = M(0·anything): M(0) = M(0·x) = M(0)·M(x) = M(x) for all x.
M constant ⟹ not injective (if |F| > 1). Contradiction.

═══════════════════════════════════════════════════
FL-A.16 [meh]: MAIN ASSEMBLY — adjoint swap for bare functions
═══════════════════════════════════════════════════

**Adjoint swap (bare function version).**
    If Tr is nondegenerate, L₁ and L₂ are additive trace-adjoints,
    x ↦ L₁(x)·x^e is bijective, and e·l ≡ 1 mod (|F|-1),
    then x ↦ L₂(x)·x^l is bijective.

    This is the direct bare-function proof, avoiding LinearMap wrapping.
-/
theorem adjoint_swap_bij_bare
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F) (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (e l : ℕ) (he_pos : 0 < e) (hl_pos : 0 < l)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hbij : Function.Bijective (fun x : F => L₁ x * x ^ e)) :
    Function.Bijective (fun x : F => L₂ x * x ^ l) := by
      have h_delta_bij : ∀ y₁ y₂, y₁ ≠ y₂ → Function.Bijective (fun x => DeltaBare' L₁ (fun x => x ^ e) y₁ x - DeltaBare' L₁ (fun x => x ^ e) y₂ x) := by
        apply P_inj_imp_DeltaBare_sub_bij';
        · exact hL₁_add;
        · exact fun a b => mul_pow a b e;
        · convert pow_field_bijective ( show Nat.Coprime ( Fintype.card F - 1 ) e from ?_ ) ( show 0 < e from he_pos ) |>.injective using 1;
          refine' Nat.Coprime.symm ( Nat.Coprime.coprime_dvd_left ( dvd_mul_right _ _ ) _ );
          exact l;
          rw [ Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec ] at * ; aesop;
        · exact hbij.injective;
      have h_delta_bij' : Function.Bijective (fun x => L₂ x * x ^ l) := by
        have h_delta_bij'' : ∀ y₁ y₂, y₁ ≠ y₂ → Function.Bijective (fun x => DeltaBare' L₂ (fun x => x ^ l) y₁ x - DeltaBare' L₂ (fun x => x ^ l) y₂ x) := by
          have h_delta_bij_adj : ∀ y₁ y₂, y₁ ≠ y₂ → Function.Bijective (fun x => DeltaBare' L₂ (fun x => x ^ l) (y₁ ^ e) x - DeltaBare' L₂ (fun x => x ^ l) (y₂ ^ e) x) := by
            intro y₁ y₂ hy₁₂
            apply (DeltaBare_sub_bij_iff_adj' p hn hn1 L₁ L₂ hL₁_add hL₂_add hAdj hTnd (fun x => x ^ e) (fun x => x ^ l) (by
            exact fun a b => mul_pow a b e) (by
            intro x
            by_cases hx : x = 0;
            · simp +decide [ hx, he_pos.ne', hl_pos.ne' ];
            · convert pow_pow_eq_self hel hx using 1) y₁ y₂).mp (h_delta_bij y₁ y₂ hy₁₂);
          have h_bij : Function.Bijective (fun x : F => x ^ e) := by
            apply pow_field_bijective;
            · refine' Nat.Coprime.symm ( Nat.Coprime.coprime_dvd_left ( dvd_mul_right _ _ ) _ );
              exact l;
              rw [ Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec ] at * ; aesop;
            · exact he_pos;
          intro y₁ y₂ hy; specialize h_delta_bij_adj ( h_bij.2 y₁ |> Classical.choose ) ( h_bij.2 y₂ |> Classical.choose ) ; simp_all +decide [ Function.Bijective ] ;
          grind +splitImp
        have h_inj : Function.Injective (fun x => L₂ x * x ^ l) := by
          apply DeltaBare_sub_bij_imp_P_inj';
          · exact hL₂_add;
          · simpa using hL₂_add 0 0;
          · exact fun a b => mul_pow a b l;
          · have h_coprime : Nat.Coprime l (Fintype.card F - 1) := by
              refine' Nat.Coprime.symm ( Nat.coprime_of_dvd' _ );
              intro k hk hk' hk''; have := Nat.dvd_of_mod_eq_zero ( show ( e * l ) % k = 0 from Nat.mod_eq_zero_of_dvd <| dvd_mul_of_dvd_right hk'' _ ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hk.one_lt ] ;
              have := Nat.mod_mod_of_dvd ( e * l ) ( Nat.dvd_of_mod_eq_zero hk' ) ; simp_all +decide [ Nat.mod_eq_of_lt hk.one_lt ] ;
              rcases x : p ^ n - 1 with ( _ | _ | k ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
            have := pow_field_bijective ( show Nat.Coprime ( Fintype.card F - 1 ) l from h_coprime.symm ) hl_pos; exact this.injective;
          · exact h_delta_bij'';
        exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩;
      exact h_delta_bij'

-- Proof assembly (each step is one application of a previous lemma):
--
-- Let M(x) = x^e and Minv(x) = x^l.
-- 1. M is multiplicative: mul_pow.
-- 2. M is injective: pow_field_bijective (from coprimality derived from hel).
-- 3. Minv is left inverse on nonzero: pow_pow_eq_self (from hel).
-- 4. hbij.1 gives P₁ = L₁·M injective.
--
-- 5. P₁ inj ⟹ ∀ y₁≠y₂, Δ_{L₁,M,y₁} - Δ_{L₁,M,y₂} bij.  [FL-A.9]
-- 6. ↔ ∀ y₁≠y₂, Δ_{L₂,Minv,M(y₁)} - Δ_{L₂,Minv,M(y₂)} bij.  [FL-A.13]
-- 7. Since M is bijective, relabel: ↔ ∀ z₁≠z₂, Δ_{L₂,Minv,z₁} - Δ_{L₂,Minv,z₂} bij.  [FL-A.14]
-- 8. ⟹ P₂ = L₂·Minv injective.  [FL-A.10]
-- 9. Injective on Fintype ⟹ bijective.  [FL-A.8]
--
-- Note: P₂(x) = L₂(x)·Minv(x) = L₂(x)·x^l, which is exactly the target.

end DempwolffMueller
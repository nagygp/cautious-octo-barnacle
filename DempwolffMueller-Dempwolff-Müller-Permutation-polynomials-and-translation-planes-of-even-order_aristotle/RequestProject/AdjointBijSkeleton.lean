import Mathlib
import RequestProject.TraceNorm
import RequestProject.ExpArith
import RequestProject.FrobAlg
import RequestProject.Lemma31

/-!
# Skeleton: Adjoint Bijectivity Transfer — Sub-lemma DAG

Decomposes `adjoint_swap_bij` (AdjointBij.lean:98) into tiny lemmas.

## Goal
If Tr is nondegenerate, L₁ and L₂ are additive trace-adjoints,
x ↦ L₁(x)·x^e is bijective, and e·l ≡ 1 (mod |F|−1),
then x ↦ L₂(x)·x^l is bijective.

## Strategy
Instantiate `lemma_3_1` from Lemma31.lean with M(x) = x^e, M⁻¹(x) = x^l.
The main challenge is building the K-linear map wrappers for L₁, L₂, and Tr.

## DAG

```
  AB.S1 (GF(p)-linearity of additive maps)  [meh]
    │
    ├──► AB.S2 (wrap L as GF(p)-linear map)  [hard]
    │
    ├──► AB.S3 (wrap Tr as GF(p)-linear form) [hard]
    │
    ├──► AB.S4 (power map multiplicative)     [easy]
    │
    ├──► AB.S5 (power map inverse)            [meh]
    │
    └──► AB.S6 (assembly: apply lemma_3_1)    [hard]
           │
           └──► adjoint_swap_bij
```
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- AB.S1 [meh]: Frobenius-sum maps are GF(p)-semilinear
-- ═══════════════════════════════════════════

/-- Any additive map that commutes with Frobenius (like a sum of Frobenius powers)
    is GF(p)-linear, i.e., L(c·x) = c·L(x) for c with c^p = c. -/
lemma additive_frob_is_gfp_linear
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (hL_frob : ∀ x, L (x ^ p) = (L x) ^ p)
    {c : F} (hc : c ^ p = c) (x : F) :
    L (c * x) = c * L x := by sorry
-- Difficulty: meh
-- Proof idea: Write c as a sum of Frobenius-fixed elements (or just use
-- the fact that c^p = c means c ∈ GF(p), so c commutes with Frobenius,
-- and L distributes via additivity + Frobenius commutation).

-- ═══════════════════════════════════════════
-- AB.S2 [hard]: Wrap additive F → F as ZMod p-linear map
-- ═══════════════════════════════════════════

-- An additive map that is GF(p)-linear can be wrapped as a (ZMod p)-linear map.
-- This is needed to interface with lemma_3_1 which requires LinearMap.
-- SUPERSEDED by BareLemma31Skeleton.lean which proves the bare-function version
-- noncomputable def wrapAsLinearMap
--     (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
--     (hL_smul : ∀ (c : F), c ^ p = c → ∀ x, L (c * x) = c * L x) :
--     F →ₗ[ZMod p] F := by sorry
-- Difficulty: hard
-- Proof idea: Define the linear map using L as the underlying function.
-- Need to show map_add (given) and map_smul. For map_smul, need to
-- show that for r : ZMod p, the algebra map sends r to an element c with c^p = c,
-- then use hL_smul.

-- ═══════════════════════════════════════════
-- AB.S3 [hard]: Wrap frobSum as ZMod p-linear form
-- ═══════════════════════════════════════════

-- The full trace frobSum p n : F → F wrapped as a (ZMod p)-linear form F →ₗ[ZMod p] (ZMod p).
-- Actually, lemma_3_1 uses T : F →ₗ[K] K where K = ZMod p, but frobSum maps F → F
-- and lands in GF(p) ⊂ F. We need the composed map F → GF(p).
-- NOTE: This is actually problematic because frobSum maps F → F (not F → ZMod p).
-- The correct approach may be to use F →ₗ[ZMod p] F with K = ZMod p viewed
-- inside F, but lemma_3_1 uses a trace T : F →ₗ[K] K.
-- Alternative: reformulate lemma_3_1 to use T : F → F with T landing in K ⊂ F.

-- ═══════════════════════════════════════════
-- AB.S4 [easy]: Power map is multiplicative
-- ═══════════════════════════════════════════

/-- `(a · b)^e = a^e · b^e`. -/
lemma pow_mul_comm (e : ℕ) (a b : F) : (a * b) ^ e = a ^ e * b ^ e :=
  mul_pow a b e

-- ═══════════════════════════════════════════
-- AB.S5a [easy]: Power map sends 0 to 0 (for e > 0)
-- ═══════════════════════════════════════════

lemma pow_zero_eq_zero (e : ℕ) (he : 0 < e) : (0 : F) ^ e = 0 :=
  zero_pow he.ne'

-- ═══════════════════════════════════════════
-- AB.S5b [meh]: Reverse round-trip for power maps
-- ═══════════════════════════════════════════

/-- If e·l ≡ 1 (mod |F|−1), then (x^l)^e = x for x ≠ 0. -/
lemma pow_reverse_round_trip (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    {x : F} (hx : x ≠ 0) :
    (x ^ l) ^ e = x := by sorry
-- Difficulty: meh
-- Proof: l * e ≡ e * l ≡ 1 mod (|F|-1) by commutativity, then pow_pow_eq_self.

-- ═══════════════════════════════════════════
-- AB.S5c [meh]: Power map bijective from modular inverse
-- ═══════════════════════════════════════════

/-- If e·l ≡ 1 (mod |F|−1) and |F| ≥ 2, then x ↦ x^e is bijective. -/
lemma pow_bij_from_mod_inverse (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hF : 2 ≤ Fintype.card F) :
    Function.Bijective (fun x : F => x ^ e) := by sorry
-- Difficulty: meh
-- Proof: From hel, deduce gcd(e, |F|-1) = 1. Then pow_field_bijective.
-- Need e > 0 (from the modular inverse condition when |F|-1 ≥ 1).

-- ═══════════════════════════════════════════
-- AB.S5d [meh]: Power map injective from modular inverse
-- ═══════════════════════════════════════════

/-- If e·l ≡ 1 (mod |F|−1), then x ↦ x^l is injective. -/
lemma pow_inj_from_mod_inverse (e l : ℕ)
    (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hF : 2 ≤ Fintype.card F) :
    Function.Injective (fun x : F => x ^ l) := by sorry
-- Difficulty: meh
-- Proof: Same as above but for l. l·e ≡ 1, so gcd(l, |F|-1) = 1.

-- ═══════════════════════════════════════════
-- AB.S6 [hard]: Main assembly — apply lemma_3_1
-- ═══════════════════════════════════════════

-- NOTE: The main difficulty is that lemma_3_1 works over an algebra K/F
-- with K-linear maps, while our setting uses bare additive functions.
-- There are two possible approaches:
--
-- Approach A: Build the full Algebra (ZMod p) F infrastructure and wrap
--   everything as linear maps. This is correct but very boilerplate-heavy.
--
-- Approach B: Prove a "bare function" version of lemma_3_1 that works
--   with additive functions directly, avoiding the LinearMap overhead.
--   This is cleaner but requires reproving the core argument.
--
-- We sketch Approach B below as it's more self-contained.

-- ═══════════════════════════════════════════
-- AB.S6a [hard]: Bare-function Δ operator
-- ═══════════════════════════════════════════

/-- The Δ operator without LinearMap wrapping.
    Δ_{L,M,y}(x) = L(x·y) · M(y). -/
def DeltaBare (L : F → F) (M : F → F) (y : F) (x : F) : F :=
  L (x * y) * M y

-- ═══════════════════════════════════════════
-- AB.S6b [easy]: Δ identity for bare functions
-- ═══════════════════════════════════════════

/-- P(x·y) = Δ_y(x) · M(x) when M is multiplicative. -/
lemma PBare_mul_eq (L : F → F) (M : F → F) (hM : ∀ a b, M (a * b) = M a * M b)
    (x y : F) :
    L (x * y) * M (x * y) = DeltaBare L M y x * M x := by sorry
-- Difficulty: easy
-- Proof: unfold DeltaBare, use hM, ring.

-- ═══════════════════════════════════════════
-- AB.S6c [meh]: Δ-difference triviality from P-injectivity
-- ═══════════════════════════════════════════

/-- If P = L·M is injective and M is multiplicative + injective,
    then Δ_{y₁}(x) - Δ_{y₂}(x) = 0 implies x = 0 (for y₁ ≠ y₂). -/
lemma DeltaBare_sub_ker_trivial
    (L : F → F) (M : F → F)
    (hM : ∀ a b, M (a * b) = M a * M b) (hMinj : Function.Injective M)
    (hP : Function.Injective (fun x => L x * M x))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂)
    {x : F} (hx : DeltaBare L M y₁ x - DeltaBare L M y₂ x = 0) :
    x = 0 := by sorry
-- Difficulty: meh
-- Proof: From the identity, P(x·y₁) = P(x·y₂), so x·y₁ = x·y₂, giving x = 0.

-- ═══════════════════════════════════════════
-- AB.S6d [meh]: Δ-difference injectivity ↔ P-injectivity (forward)
-- ═══════════════════════════════════════════

/-- P injective ⟹ Δ_{y₁} - Δ_{y₂} injective for y₁ ≠ y₂. -/
lemma DeltaBare_sub_inj_of_P_inj
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (M : F → F) (hM : ∀ a b, M (a * b) = M a * M b) (hMinj : Function.Injective M)
    (hP : Function.Injective (fun x => L x * M x))
    {y₁ y₂ : F} (hy : y₁ ≠ y₂) :
    Function.Injective (fun x => DeltaBare L M y₁ x - DeltaBare L M y₂ x) := by sorry
-- Difficulty: meh
-- Proof: If difference is 0 at x, then x = 0 by AB.S6c. Additivity of L
-- gives that the difference map is additive, so ker = 0 ⟹ injective.

-- ═══════════════════════════════════════════
-- AB.S6e [meh]: Δ-difference bijectivity ↔ P-injectivity (backward)
-- ═══════════════════════════════════════════

/-- All Δ-differences bijective ⟹ P injective. -/
lemma P_inj_of_DeltaBare_sub_bij
    (L : F → F) (hL_add : ∀ a b, L (a + b) = L a + L b)
    (M : F → F) (hM : ∀ a b, M (a * b) = M a * M b) (hMinj : Function.Injective M)
    (hDelta : ∀ y₁ y₂ : F, y₁ ≠ y₂ →
      Function.Bijective (fun x => DeltaBare L M y₁ x - DeltaBare L M y₂ x)) :
    Function.Injective (fun x => L x * M x) := by sorry
-- Difficulty: meh
-- Proof: If P(a) = P(b), use the identity with x = 1 to get
-- (Δ_a(1) - Δ_b(1)) · M(1) = 0. Since M(1) ≠ 0, Δ_a(1) = Δ_b(1).
-- Bijectivity (hence injectivity) of Δ_a - Δ_b gives 1 = 0, contradiction.

-- ═══════════════════════════════════════════
-- AB.S6f [hard]: Trace adjoint identity for bare Δ
-- ═══════════════════════════════════════════

/-- Tr(Δ_{L,M,y}(u) · v) = Tr(u · Δ_{L*,M⁻¹,M(y)}(v)). -/
lemma DeltaBare_trace_adjoint
    {n : ℕ} (hn : Fintype.card F = p ^ n)
    (L₁ L₂ : F → F) (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (M Minv : F → F) (hMinv : ∀ x, Minv (M x) = x)
    (u v y : F) :
    frobSum p n (DeltaBare L₁ M y u * v) =
    frobSum p n (u * DeltaBare L₂ Minv (M y) v) := by sorry
-- Difficulty: hard
-- Proof: Expand DeltaBare. Use hAdj with w = u·y, z = M(y)·v.
-- Then commute and use hMinv.

-- ═══════════════════════════════════════════
-- AB.S6g [hard]: Adjoint bijectivity for bare Δ-differences
-- ═══════════════════════════════════════════

/-- Δ_{L,M,y₁} - Δ_{L,M,y₂} bijective ↔ Δ_{L*,M⁻¹,M(y₁)} - Δ_{L*,M⁻¹,M(y₂)} bijective. -/
lemma DeltaBare_sub_bij_iff_adj
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F)
    (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (M Minv : F → F) (hMinv : ∀ x, Minv (M x) = x)
    (y₁ y₂ : F) :
    Function.Bijective (fun x => DeltaBare L₁ M y₁ x - DeltaBare L₁ M y₂ x) ↔
    Function.Bijective (fun x => DeltaBare L₂ Minv (M y₁) x - DeltaBare L₂ Minv (M y₂) x) := by sorry
-- Difficulty: hard
-- Proof: The Δ-difference maps are additive (since L is additive).
-- They are thus GF(p)-linear endomorphisms of F.
-- By AB.S6f, they are trace-adjoints of each other.
-- A linear map on a finite-dim space is bijective iff its adjoint is.

-- ═══════════════════════════════════════════
-- AB.S6h [meh]: Relabelling via M bijective
-- ═══════════════════════════════════════════

/-- Quantifying over distinct pairs is invariant under a bijection. -/
lemma forall_ne_bij_bare {M : F → F} (hMbij : Function.Bijective M)
    {Q : F → F → Prop} :
    (∀ y₁ y₂, y₁ ≠ y₂ → Q (M y₁) (M y₂)) ↔ (∀ z₁ z₂, z₁ ≠ z₂ → Q z₁ z₂) := by sorry
-- Difficulty: meh (already proved as forall_ne_bij in Lemma31.lean)

-- ═══════════════════════════════════════════
-- AB.S7 [hard]: Final assembly of adjoint_swap_bij
-- ═══════════════════════════════════════════

/-- Main theorem: adjoint bijectivity transfer via power maps.
    Chain: P inj ↔ Δ-diff bij ↔ Δ*-diff bij ↔ P* inj → P* bij. -/
theorem adjoint_swap_bij_skeleton
    {n : ℕ} (hn : Fintype.card F = p ^ n) (hn1 : 1 ≤ n)
    (L₁ L₂ : F → F) (hL₁_add : ∀ a b, L₁ (a + b) = L₁ a + L₁ b)
    (hL₂_add : ∀ a b, L₂ (a + b) = L₂ a + L₂ b)
    (hAdj : ∀ w z, frobSum p n (L₁ w * z) = frobSum p n (w * L₂ z))
    (hTnd : ∀ x : F, x ≠ 0 → ∃ y, frobSum p n (x * y) ≠ 0)
    (e l : ℕ) (hel : e * l % (Fintype.card F - 1) = 1 % (Fintype.card F - 1))
    (hbij : Function.Bijective (fun x : F => L₁ x * x ^ e)) :
    Function.Bijective (fun x : F => L₂ x * x ^ l) := by sorry
-- Difficulty: hard
-- Proof sketch:
-- 1. Set M(x) = x^e, Minv(x) = x^l.
-- 2. hbij ⟹ P₁ injective (bij ⟹ inj).
-- 3. P₁ inj ⟹ all Δ_{L₁,M} differences bijective (AB.S6d + finite ⟹ bij).
-- 4. ↔ all Δ_{L₂,Minv,M(·)} differences bijective (AB.S6g).
-- 5. ↔ all Δ_{L₂,Minv} differences bijective (AB.S6h + M bijective).
-- 6. ⟹ P₂ = L₂·Minv injective (AB.S6e).
-- 7. Injective on Fintype ⟹ bijective.

end DempwolffMueller

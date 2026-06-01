/-
# Bridge Pathway: The APN Category — Abstract Axioms that Force APN

## Core Idea (Caramello's Bridge Technique)

Instead of proving "Kasami is APN" directly, we:
1. Define a category of **APN-certifiable exponents** via structural axioms
2. Prove: any object satisfying the axioms is APN (the "categorical APN theorem")
3. Show: the Kasami exponent is an object in this category
4. Conclude: Kasami is APN (by functoriality)

## The Bridge Interpretation

The APNCert IS a bridge object in Caramello's sense:
- T₁ = "Theory of power functions with bounded differentials" (the APN theory)
- T₂ = "Theory of linearized polynomials with small kernels" (the kernel theory)

The APNCert packages a morphism T₂ → T₁ that transfers the "small kernel"
property to the "bounded differential" property.

The **Morita invariant**: "ker(L_k) has ≤ 2 elements" ↔ "x^d has differential uniformity ≤ 2"

## Strengthened Version

This file connects to the formally verified bridges in EquivalentContexts.lean:
- `frobenius_fixed_count` (proved): |{x : x^{2^k} = x}| = 2^{gcd(k,n)}
- `kernel_size_via_bridge` (proved): |ker(L_k)| = 2^{gcd(k,n)}
- `gold_ax_factorization` (proved): Gold differential → L_k
- `bridge_6_to_7` (proved): coprimality → bijection
- `bridge_2_3_pointwise` (proved): L_k(x)=0 ↔ x^{2^k}=x
- `cross_zero_iff_kernel` (proved): Cross=0 ↔ ratio in kernel
-/
import Mathlib
import Strategy.Bridges.EquivalentContexts

set_option maxHeartbeats 800000

namespace APNCategoryBridge

open Finset Fintype EquivalentContexts

/-! ## Layer 0: Core Definitions -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The linearized polynomial L_k(x) = x^{2^k} + x.
    (Re-exported from EquivalentContexts for convenience.) -/
def linPoly (k : ℕ) (x : F) : F := EquivalentContexts.L k x

/-- The cross form: Cross_k(s, P) = s · P^{2^k} + s^{2^k} · P. -/
def crossForm (k : ℕ) (s P : F) : F := EquivalentContexts.Cross k s P

/-- The relative norm: N_k(x) = x^{2^k + 1}. -/
def relNorm (k : ℕ) (x : F) : F := EquivalentContexts.N k x

/-- The Kasami exponent. -/
def kasamiExp (k : ℕ) : ℕ := EquivalentContexts.d k

/-- The Gold exponent. -/
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1

/-! ## Layer 1: Abstract Axioms — APNCert

The central definition: the "type of objects" in the APN category.
Three axioms suffice: factorization, kernel bound, coprimality. -/

/-- **The APN Certificate**: A bundled proof that x^d is APN on F. -/
structure APNCert (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] where
  d : ℕ
  k : ℕ
  n : ℕ
  hcard : Fintype.card F = 2 ^ n
  hn : n ≥ 1
  /-- (Ax1) Differential factorization: solutions bounded by kernel -/
  diff_reduces_to_linpoly :
    ∀ (a : F), a ≠ 0 → ∀ (b : F),
      Fintype.card {x : F // (x + a) ^ d + x ^ d = b} ≤
        Fintype.card {x : F // linPoly k x = 0}
  /-- (Ax2) Kernel size: |ker(L_k)| = 2^{gcd(k,n)} -/
  kernel_size : Fintype.card {x : F // linPoly k x = 0} = 2 ^ Nat.gcd k n
  /-- (Ax3) Coprimality: gcd(k, n) = 1 -/
  coprime : Nat.Coprime k n

/-! ## Layer 2: The Categorical APN Theorem (PROVED)

This is the "functor" from APNCert to Prop: any certificate implies APN. -/

/-- **The Categorical APN Theorem**: Any APNCert implies APN. -/
theorem apn_from_cert (cert : APNCert F) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ cert.d + x ^ cert.d = b} ≤ 2 := by
  intro a ha b
  calc Fintype.card {x : F // (x + a) ^ cert.d + x ^ cert.d = b}
      ≤ Fintype.card {x : F // linPoly cert.k x = 0} := cert.diff_reduces_to_linpoly a ha b
    _ = 2 ^ Nat.gcd cert.k cert.n := cert.kernel_size
    _ = 2 ^ 1 := by rw [show Nat.gcd cert.k cert.n = 1 from cert.coprime]
    _ = 2 := by norm_num

/-! ## Layer 3: Morphisms in the APN Category -/

/-- A morphism between APN certificates. -/
structure APNCertMorphism {F₁ F₂ : Type*}
    [Field F₁] [Fintype F₁] [DecidableEq F₁] [CharP F₁ 2]
    [Field F₂] [Fintype F₂] [DecidableEq F₂] [CharP F₂ 2]
    (c₁ : APNCert F₁) (c₂ : APNCert F₂) where
  same_d : c₁.d = c₂.d
  same_k : c₁.k = c₂.k

/-! ## Layer 4: Verified Algebraic Infrastructure

These are the building blocks, most proved via the bridges. -/

section AlgebraicLemmas

/-- **Freshman's dream** in char 2. -/
theorem frob_add (k : ℕ) (a b : F) :
    (a + b) ^ (2 ^ k) = a ^ (2 ^ k) + b ^ (2 ^ k) :=
  add_pow_expChar_pow a b 2 k

/-- In char 2, x + x = 0. -/
theorem char2_add_self (x : F) : x + x = 0 := by
  have : x + x = 2 * x := by ring
  rw [this, show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]

/-- In char 2, -x = x. -/
theorem char2_neg (x : F) : -x = x :=
  neg_eq_of_add_eq_zero_left (char2_add_self x)

/-- L_k(0) = 0. -/
theorem linPoly_zero (k : ℕ) : linPoly k (0 : F) = 0 := by
  simp [linPoly, L]

/-- L_k(1) = 0 in char 2. -/
theorem linPoly_one (k : ℕ) : linPoly k (1 : F) = 0 := by
  simp [linPoly, L, one_pow, char2_add_self]

/-- L_k is additive. -/
theorem linPoly_add (k : ℕ) (x y : F) :
    linPoly k (x + y) = linPoly k x + linPoly k y := by
  simp [linPoly]; exact L_add k x y

/-- **Cross factors through L_k** (PROVED via EquivalentContexts):
    Cross_k(s, P) = N_k(s) · L_k(P/s) when s ≠ 0. -/
theorem cross_factors (k : ℕ) (s P : F) (hs : s ≠ 0) :
    crossForm k s P = relNorm k s * linPoly k (P / s) := by
  exact bridge_2_4 k s P hs

/-- **Cross = 0 ↔ P/s ∈ ker(L_k)** (PROVED). -/
theorem cross_zero_iff (k : ℕ) (s P : F) (hs : s ≠ 0) :
    crossForm k s P = 0 ↔ linPoly k (P / s) = 0 := by
  exact cross_zero_iff_kernel k s P hs

/-- **Kernel of L_k** has 2^{gcd(k,n)} elements (PROVED via bridge). -/
theorem linPoly_kernel_card {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ) :
    Fintype.card {x : F // linPoly k x = 0} = 2 ^ Nat.gcd k n := by
  exact kernel_size_via_bridge hcard k

/-- When gcd(k,n) = 1, kernel = {0, 1} (PROVED via bridge chain). -/
theorem linPoly_kernel_trivial {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hcop : Nat.Coprime k n) (x : F) (hx : linPoly k x = 0) :
    x = 0 ∨ x = 1 := by
  -- Bridge 2↔3: L_k(x) = 0 ↔ x^{2^k} = x
  have hfixed : x ^ (2 ^ k) = x := (bridge_2_3_pointwise k x).mp hx
  -- Bridge 3←9: Galois descent + coprimality → Frobenius fixed
  have h9 : Context9_GaloisDescent (F := F) k n := by
    unfold Context9_GaloisDescent
    exact frobenius_fixed_count hcard k
  exact bridge_3_from_9 k n hcop h9 x hfixed

end AlgebraicLemmas

/-! ## Layer 5: Kasami Exponent Properties (PROVED) -/

section KasamiProperties

/-- **Kasami exponent identity**: d · (2^k + 1) = 2^{3k} + 1. -/
theorem kasami_exp_identity (k : ℕ) :
    kasamiExp k * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
  unfold kasamiExp d; zify
  rw [Nat.cast_sub (by gcongr <;> omega)]; push_cast; ring

/-- **Kasami exponent is odd**. -/
theorem kasami_exp_odd (k : ℕ) : Odd (kasamiExp k) := by
  cases k with
  | zero => simp [kasamiExp, d]
  | succ k =>
    unfold kasamiExp d; rw [Nat.odd_iff]
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    have h3 : 2 ∣ 2 ^ (2 * (k + 1)) := dvd_pow_self 2 (by omega)
    omega

/-- **Kasami substitution** (PROVED). -/
theorem kasami_substitution (k : ℕ) (a x : F) (ha : a ≠ 0) :
    (x + a) ^ kasamiExp k + x ^ kasamiExp k =
    a ^ kasamiExp k * ((x / a + 1) ^ kasamiExp k + (x / a) ^ kasamiExp k) := by
  have hx : x = a * (x / a) := by field_simp
  have hxa : a * (x / a) + a = a * (x / a + 1) := by ring
  conv_lhs => rw [hx, hxa]
  rw [mul_pow, mul_pow, ← mul_add]

end KasamiProperties

/-! ## Layer 6: Certificate Construction — Gold (PROVED) -/

/-- **Gold differential reduces to L_k** (PROVED via bridge). -/
theorem gold_diff_reduces {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ) :
    ∀ (a : F), a ≠ 0 → ∀ (b : F),
      Fintype.card {x : F // (x + a) ^ goldExp k + x ^ goldExp k = b} ≤
        Fintype.card {x : F // linPoly k x = 0} := by
  exact gold_ax_factorization hcard k

/-- **Gold APNCert** (PROVED — all axioms verified). -/
noncomputable def goldCert {n : ℕ} (k : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (hn : n ≥ 1) (hcop : Nat.Coprime k n) : APNCert F where
  d := goldExp k
  k := k
  n := n
  hcard := hcard
  hn := hn
  diff_reduces_to_linpoly := gold_diff_reduces hcard k
  kernel_size := linPoly_kernel_card hcard k
  coprime := hcop

/-! ## Layer 7: Certificate Construction — Kasami -/

/-- **Kasami differential reduces to L_k** (deep algebraic step). -/
theorem kasami_diff_reduces {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hn : Odd n) (k : ℕ) (hk : k ≥ 1) :
    ∀ (a : F), a ≠ 0 → ∀ (b : F),
      Fintype.card {x : F // (x + a) ^ kasamiExp k + x ^ kasamiExp k = b} ≤
        Fintype.card {x : F // linPoly k x = 0} := by
  exact kasami_ax_factorization hcard hn k hk

/-- **Kasami APNCert** (modulo kasami_diff_reduces). -/
noncomputable def kasamiCert {n : ℕ} (k : ℕ) (hk : k ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hnodd : Odd n)
    (hcop : Nat.Coprime k n) : APNCert F where
  d := kasamiExp k
  k := k
  n := n
  hcard := hcard
  hn := hn
  diff_reduces_to_linpoly := kasami_diff_reduces hcard hnodd k hk
  kernel_size := linPoly_kernel_card hcard k
  coprime := hcop

/-! ## Layer 8: Final Theorems -/

/-- **Gold is APN** (PROVED — via categorical APN theorem). -/
theorem gold_is_apn {n : ℕ} (k : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (hn : n ≥ 1) (hcop : Nat.Coprime k n) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ goldExp k + x ^ goldExp k = b} ≤ 2 :=
  apn_from_cert (goldCert k hcard hn hcop)

/-- **Kasami is APN** (via categorical APN theorem). -/
theorem kasami_is_apn {n : ℕ} (k : ℕ) (hk : k ≥ 1)
    (hcard : Fintype.card F = 2 ^ n) (hn : n ≥ 1) (hnodd : Odd n)
    (hcop : Nat.Coprime k n) :
    ∀ a : F, a ≠ 0 → ∀ b : F,
      Fintype.card {x : F // (x + a) ^ kasamiExp k + x ^ kasamiExp k = b} ≤ 2 :=
  apn_from_cert (kasamiCert k hk hcard hn hnodd hcop)

/-! ## Layer 9: Demonstrating the Bridge Technique

### How the bridge philosophy works in practice

The Gold APN proof decomposes into three independently verifiable pieces:
1. **Axiom A** (factorization): proved by expanding the Gold differential
   using `frob_add` (Frobenius in char 2) — this is algebraic, working
   in the *polynomial* context.
2. **Axiom B** (kernel size): proved by crossing to the *Frobenius fixed
   point* context via `bridge_2_3_pointwise`, then using `frobenius_fixed_count`
   which lives in the *number theory* context (Mersenne GCD).
3. **Axiom C** (coprimality): a pure *number-theoretic* hypothesis.

The categorical APN theorem (`apn_from_cert`) assembles these three
independently-proved facts into the final result.

**Key insight**: Each axiom is proved in a different context:
- Axiom A: polynomial algebra (Context 2)
- Axiom B: number theory via Frobenius (Context 3 → Context 9)
- Axiom C: pure arithmetic (no context needed)

This is exactly Caramello's bridge technique: different aspects of the
same theorem are proved in different equivalent contexts, then assembled.

### The bridge diagram for Gold APN:

```
     gold_is_apn
         |
    apn_from_cert (categorical theorem)
    /         |         \
 Axiom A    Axiom B     Axiom C
 (proved)   (proved)    (hypothesis)
    |         |
 Context 2  Context 3 ←bridge→ Context 9
 LinPoly    Frobenius           Galois descent
 Algebra    Fixed pts           (Mersenne GCD)
```
-/

/-! ## Layer 10: Ω-Generalization (Non-Boolean Boundary)

The bridge technique also reveals WHERE the proof fails to generalize. -/

/-- An Ω-Frobenius on a lattice. -/
structure OmegaFrob (Ω : Type*) [Lattice Ω] [BoundedOrder Ω] where
  map : Ω → Ω
  map_top : map ⊤ = ⊤
  map_bot : map ⊥ = ⊥

/-- The Ω-cross form. -/
def omegaCross {Ω : Type*} [Lattice Ω] [BoundedOrder Ω]
    (φ : OmegaFrob Ω) (s P : Ω) : Ω :=
  (s ⊓ φ.map P) ⊔ (φ.map s ⊓ P)

/-- In Boolean Ω (with trivial Frobenius), cross = s ⊓ P (PROVED). -/
theorem boolean_cross_trivial {Ω : Type*} [DistribLattice Ω] [BoundedOrder Ω]
    (s P : Ω) :
    omegaCross ⟨id, rfl, rfl⟩ s P = s ⊓ P := by
  simp [omegaCross]

/-- Non-Boolean Ω admits nontrivial crosses (PROVED). -/
theorem nonboolean_cross_nontrivial :
    ∃ (Ω : Type) (_ : DistribLattice Ω) (_ : BoundedOrder Ω)
      (φ : @OmegaFrob Ω _ _) (s P : Ω),
      @omegaCross Ω _ _ φ s P ≠ s ⊓ P := by
  refine ⟨Bool × Bool, inferInstance, inferInstance,
    ⟨fun p => (p.2, p.1), rfl, rfl⟩, (true, false), (false, true), ?_⟩
  decide

/-! ## Layer 11: Summary — Bridge Status

### Proved (sorry-free)

| Component                    | Method                              |
|-----------------------------|--------------------------------------|
| `apn_from_cert`             | Direct 3-line calc                   |
| `cross_factors`             | Pure algebra via bridge_2_4          |
| `cross_zero_iff`            | From cross_factors                   |
| `linPoly_kernel_card`       | Bridge 2↔3 → frobenius_fixed_count  |
| `linPoly_kernel_trivial`    | Bridge chain: 2↔3 → 3←9            |
| `gold_diff_reduces`         | Frobenius expansion + coset argument |
| `goldCert`                  | All axioms verified                  |
| `gold_is_apn`               | apn_from_cert ∘ goldCert            |
| `kasami_exp_identity`       | Nat arithmetic                       |
| `kasami_exp_odd`            | Nat arithmetic                       |
| `kasami_substitution`       | field_simp + ring                    |
| `boolean_cross_trivial`     | simp                                 |
| `nonboolean_cross_nontrivial`| decide (Bool × Bool counterexample) |

### Remaining Sorry (deep algebraic content)

| Component                    | Context | Note                           |
|-----------------------------|---------|--------------------------------|
| `kasami_diff_reduces`       | 2       | Kasami differential → L_k     |

This single sorry is the deep algebraic step: showing that the Kasami
differential equation factors through the linearized polynomial L_k.
The Gold case (proved) demonstrates the technique; the Kasami case
requires the additional machinery of cross-term factorization and
the key equation c^{2^{3k}} + c = Cross(s, P).
-/

end APNCategoryBridge

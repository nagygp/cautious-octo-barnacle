import Mathlib
import KasamiPermutation.TraceFreeCriterion
import KasamiPermutation.TraceVersionInfra
import KasamiPermutation.TraceVersionBase
import KasamiPermutation.Headlines.TraceVersionCriterion

/-!
# Dobbertin (1999), pp. 133–138 — a faithful skeleton transcription

**Status (this pass).**  The proofs of the transcribed statements are now filled
in, reusing the library's finite-field machinery (`TraceFreeCriterion`, `TraceVersionInfra`,
`TraceVersionBase`, and the new parity-general `q₁` criterion in
`Headlines.TraceVersionCriterion`).  A few of the *internal* skeleton statements had to be
minimally corrected to be provable — this is documented at each such statement:

* `eqn2_of_eqn1` — the original is *false* as stated (it holds at `x = 0`, where
  `ℓ(0) = 1 ≠ 0`, while the cleared equation `eqn1` is satisfied vacuously).  The
  faithful version adds `x ≠ 0` and the field hypotheses `hn`, `k·k' ≡ 1 (mod n)`.
* `qKasami_bijective_iff_case2` — the original counts *all* solutions of the cleared equation
  `eqn1`, but `x = 0` always satisfies `eqn1` (both sides are `0`).  The faithful
  version counts the **nonzero** solutions (as in the paper) and adds `c ≠ 0`.
* The permutation/APN statements carry the non-degeneracy hypothesis
  `2^k + 1 < 2^n - 1` (excluding only the marginal fields `𝔽₂`, `𝔽₄`), exactly as
  the library's `TraceFreeCriterion.qeps_bijective_iff` does, together with `0 < k`.

The original statements are kept (commented out) next to their corrected forms.

This file is a **faithful, statement-level transcription** of the opening of

> Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets"*, in *Difference Sets, Sequences and their Correlation
> Properties*, NATO Sci. Ser. C **542**, Kluwer Academic Publishers, 1999,
> pp. 133–158,

covering the **first six pages (133–138)**: the abstract, the Introduction
(Section 1), and Section 2 up to — **but not including — Theorem 3**.  Concretely
it transcribes the definitions of the generalized Kasami and MCM polynomials,
**Theorem 1** (with its proof broken into the paper's Case 1 / Case 2), and
**Corollary 2**.

It began life as a *skeleton* (definitions stated as in the paper, every theorem or
proof-step left as `sorry`).  In this pass the proofs have been **filled in**
(see the Status note above): the transcribed statements are now proved, reusing
the library's finite-field machinery, and nothing that is not in these pages of the
paper is included as a *result* (only the bridges to the library are added).

## Abstract (Dobbertin 1999)

We study permutation polynomials on `𝔽_{2ⁿ}`, which are associated with Kasami
power functions `xᵈ`, i.e. `d = 2^{2k} − 2^k + 1` for `k < n` with `gcd(k, n) = 1`.
We describe the equivalence of a class of ("Kasami") permutation polynomials,
considered to derive the APN property of Kasami power functions, and the well-known
class of MCM permutation polynomials.  Explicit and recursive formulae for the
inverses of Kasami and MCM permutation polynomials are given.  As an application
the image `B` under the two-to-one mapping `(x+1)ᵈ + xᵈ + 1` can be characterized
by a trace condition, and the 2-rank of `B* = B ∖ {0}` can be determined.  We
conjecture that `B*` is a cyclic difference set.

## 1. Introduction

Janwa and Wilson (1993) seem to have been the first to prove, in a coding-theory
context, that Kasami power functions `xᵈ` are almost perfect nonlinear (APN) on
`L = 𝔽_{2ⁿ}`.  We call `xᵈ` a **Kasami power function** and `d` a **Kasami
exponent** if
```
   d = 2^{2k} − 2^k + 1,   where  k < n  and  gcd(k, n) = 1.
```
Recall (Nyberg 1994) that `xᵈ` is **APN** if for all `a ∈ L*`, `b ∈ L` the equation
`(x+a)ᵈ + xᵈ = b` has either no or precisely two solutions in `L`.

In Section 2 we state and verify (Theorem 1) which generalized Kasami polynomials
are permutation polynomials; this yields a short new proof that MCM polynomials are
permutations, and — via a two-to-one factorization — the APN property of Kasami
power functions (Corollary 2).
-/

namespace KasamiPerm.Headlines

open scoped BigOperators
open Finset

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

/-! ## Basic notions -/

/-- The absolute **trace** `Tr : 𝔽_{2ⁿ} → 𝔽₂ ⊆ L`, `Tr(x) = ∑_{i<n} x^{2^i}`. -/
def Tr (n : ℕ) (x : L) : L := ∑ i ∈ Finset.range n, x ^ (2 ^ i)

/-- The **Kasami exponent** `d = 2^{2k} − 2^k + 1`. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- A map `f : L → L` is **two-to-one** if `|f⁻¹(f x)| = 2` for all `x ∈ L`. -/
def TwoToOne (f : L → L) : Prop := ∀ x : L, {y : L | f y = f x}.ncard = 2

/-- `f` is **almost perfect nonlinear (APN)**: for every `a ≠ 0` and every `b`, the
equation `f(x+a) + f(x) = b` has either no or precisely two solutions. -/
def IsAPN (f : L → L) : Prop :=
  ∀ a : L, a ≠ 0 → ∀ b : L,
    {x : L | f (x + a) + f x = b}.ncard = 0 ∨ {x : L | f (x + a) + f x = b}.ncard = 2

/-! ## Section 2 — the generalized Kasami and MCM polynomials

Throughout Section 2 we assume
```
   gcd(k, n) = 1,   k < n,   k' ≡ 1/k (mod n).
```
For `α = 0, 1` the paper defines the **generalized Kasami polynomial**
```
                 ( Σ_{i=1}^{k'} z^{2^{ik}} )  +  α·Tr(z)
   q_α(z)  =    ─────────────────────────────────────────
                              z^{2^k + 1}
```
and for `β = 0, 1` the **generalized MCM polynomial**
```
                 ( Σ_{i=0}^{k-1} z^{2^i}  +  β·Tr(z) )^{2^k + 1}
   P_β(z)  =    ─────────────────────────────────────────────────
                              z^{2^k}
```
(the factors `1/z^{2^k+1}` and `1/z^{2^k}` being replaced by `z^{(2ⁿ−1)−(2^k+1)}`
and `z^{(2ⁿ−1)−2^k}` respectively to obtain genuine polynomials on `L`, with the
convention `0/0 = 0`).  Recall that `P₀` is an MCM permutation polynomial if `k`
is odd. -/

/-- The **generalized Kasami polynomial** `q_α`, as a genuine function on
`L = 𝔽_{2ⁿ}` (with `0/0 = 0`):
`q_α(z) = (Σ_{i=1}^{k'} z^{2^{ik}} + α·Tr(z)) · z^{(2ⁿ−1)−(2^k+1)}`. -/
def qKasami (n k k' : ℕ) (α : ℕ) (z : L) : L :=
  ((∑ i ∈ Finset.Icc 1 k', z ^ (2 ^ (i * k))) + (α : L) * Tr n z)
    * z ^ (2 ^ n - 1 - (2 ^ k + 1))

/-- The **generalized MCM polynomial** `P_β`, as a genuine function on
`L = 𝔽_{2ⁿ}` (with `0/0 = 0`):
`P_β(z) = (Σ_{i=0}^{k-1} z^{2^i} + β·Tr(z))^{2^k+1} · z^{(2ⁿ−1)−2^k}`. -/
def pMCM (n k : ℕ) (β : ℕ) (z : L) : L :=
  ((∑ i ∈ Finset.range k, z ^ (2 ^ i)) + (β : L) * Tr n z) ^ (2 ^ k + 1)
    * z ^ (2 ^ n - 1 - 2 ^ k)

/-! ## Bridges to the library machinery

The generalized Kasami polynomial `qKasami` of this skeleton coincides, for the
two admissible values `α = 0, 1`, with the library polynomials `TraceFree.qeps`
(trace-free, `ε = 0`) and `TraceParityCase.gmap` (the trace version `q^{(Tr·)}`).  These
bridges let us reuse the library's permutation criteria. -/

open KasamiPerm FiniteFieldCharTwo

omit [Fintype L] [CharP L 2] in
/-- `qKasami … 0` is the library trace-free polynomial `TraceFree.qeps … 0`. -/
lemma qKasami_zero_eq_qeps (z : L) :
    qKasami (L := L) n k k' 0 z = KasamiPerm.TraceFree.qeps n k k' (0 : L) z := by
  simp [qKasami, KasamiPerm.TraceFree.qeps, KasamiPerm.TraceFree.sTrace]

omit [Fintype L] [CharP L 2] in
/-- `qKasami … 1` is the library trace-version polynomial `TraceParityCase.gmap`. -/
lemma qKasami_one_eq_gmap (z : L) :
    qKasami (L := L) n k k' 1 z = KasamiPerm.TraceParityCase.gmap n k k' z := by
  simp only [qKasami, KasamiPerm.TraceParityCase.gmap, KasamiPerm.TraceFree.qeps, KasamiPerm.TraceFree.sTrace,
    Tr, FiniteFieldCharTwo.truncTrace, Nat.cast_one, one_mul]

omit [CharP L 2] in
/-- Clearing the denominator of `qKasami` on units: for `x ≠ 0`,
`q_α(x)·x^{2^k+1}` equals the numerator `Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`. -/
lemma qKasami_mul_unit (hn : Fintype.card L = 2 ^ n) (hexp : 2 ^ k + 1 ≤ 2 ^ n - 1)
    (α : ℕ) {x : L} (hx : x ≠ 0) :
    qKasami (L := L) n k k' α x * x ^ (2 ^ k + 1)
      = (∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))) + (α : L) * Tr n x := by
  unfold qKasami
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hexp, ← hn,
    FiniteField.pow_card_sub_one_eq_one x hx, mul_one]

/-! ## The elementary shortcut invariant `k' + alpha*n (mod 2)`

The value of `q_alpha` at `1` is the single number `k' + alpha*n (mod 2)`, and it
already decides the necessary direction of Theorem 1 with no finite-field
machinery: `q_alpha` fixes `0` (the `0/0 = 0` convention makes the numerator
vanish), and `q_alpha(1) = k' + alpha*n`; so if `k' + alpha*n` were even, then
`q_alpha` would identify `0` and `1` in the field.  This is the small structural
invariant that propagates from the Mathlib base straight to the headline, and
`qKasami_bijective_iff` below discharges its necessary half through it, reserving the heavy
engine (`TraceFreeCriterion`/`gmap_bijective_iff`) for the sufficient half only. -/

omit [Fintype L] [CharP L 2] in
/-- `q_alpha(0) = 0` (the `0/0 = 0` convention: the numerator already vanishes). -/
lemma qKasami_zero (α : ℕ) : qKasami (L := L) n k k' α 0 = 0 := by
  unfold qKasami Tr
  have h1 : (∑ i ∈ Finset.Icc 1 k', (0 : L) ^ (2 ^ (i * k))) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    have : 0 < 2 ^ (i * k) := pow_pos (by norm_num) _
    simp [zero_pow this.ne']
  have h2 : (∑ i ∈ Finset.range n, (0 : L) ^ (2 ^ i)) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    have : 0 < 2 ^ i := pow_pos (by norm_num) _
    simp [zero_pow this.ne']
  rw [h1, h2]; ring

omit [Fintype L] [CharP L 2] in
/-- `q_alpha(1) = k' + alpha*n` in `L`. -/
lemma qKasami_one (α : ℕ) :
    qKasami (L := L) n k k' α 1 = ((k' + α * n : ℕ) : L) := by
  unfold qKasami Tr; simp

omit [Fintype L] in
/-- **Engine-free necessary direction of Theorem 1.**  If `q_alpha` is bijective
then `k' + alpha*n` is odd, proved from the two evaluations `q_alpha(0) = 0`,
`q_alpha(1) = k'+alpha*n` and injectivity alone, using none of the finite-field
telescoping engine. -/
lemma qKasami_bijective_imp_parity (α : ℕ)
    (h : Function.Bijective (qKasami (L := L) n k k' α)) :
    (k' + α * n) % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one (k' + α * n) with h0 | h1
  · refine absurd (h.injective (a₁ := (1 : L)) (a₂ := 0) ?_) one_ne_zero
    rw [qKasami_one, qKasami_zero, CharP.cast_eq_zero_iff L 2]; omega
  · exact h1

/-! ## Theorem 1

> **Theorem 1.** A generalized Kasami polynomial `q_α` is a permutation polynomial
> on `L` if and only if `k' + α·n ≡ 1 (mod 2)`.  That is,
> * `q₀` is a permutation polynomial if and only if `k'` is odd,
> * `q₁` is a permutation polynomial if and only if `n ≡ k' + 1 (mod 2)`.

(Note that generalized Kasami permutation polynomials always exist, since
`gcd(k', n) = 1` and therefore not both of `k'` and `n` can be even.) -/

/-
**Theorem 1 (Dobbertin 1999).**  `q_α` is a permutation polynomial on
`L = 𝔽_{2ⁿ}` iff `k' + α·n ≡ 1 (mod 2)`.
-/
theorem qKasami_bijective_iff (hn : Fintype.card L = 2 ^ n) (hk : k < n) (hcop : Nat.Coprime k n)
    (hk' : k * k' % n = 1 % n) (hk0 : 0 < k) (hexp : 2 ^ k + 1 < 2 ^ n - 1)
    (α : ℕ) (hα : α = 0 ∨ α = 1) :
    Function.Bijective (qKasami (L := L) n k k' α) ↔ (k' + α * n) % 2 = 1 := by
  -- Necessary direction: the engine-free shortcut invariant.
  refine ⟨fun h => qKasami_bijective_imp_parity α h, fun hpar => ?_⟩
  -- Sufficient direction: the finite-field engine (`TraceFreeCriterion` / `gmap_bijective_iff`).
  have hkk1 : k * k' % n = 1 := by
    rw [hk']; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ]
  rcases hα with ( rfl | rfl )
  · have hfun : (qKasami (L := L) n k k' 0) = KasamiPerm.TraceFree.qeps n k k' (0 : L) :=
      funext qKasami_zero_eq_qeps
    have hodd : Odd k' := Nat.odd_iff.mpr (by omega)
    rw [hfun]
    exact (KasamiPerm.TraceFree.qeps_bijective_iff hn hk0 hk hcop hkk1 hexp (Or.inl rfl)).mpr
      (iff_of_false (by simp) (by rw [Nat.not_even_iff_odd]; exact hodd))
  · rw [ show qKasami n k k' 1 = TraceParityCase.gmap n k k' from funext fun z => qKasami_one_eq_gmap z ]
    exact (TraceCriterion.gmap_bijective_iff hn hk0 hk hcop hkk1 hexp).mpr (Nat.odd_iff.mpr (by omega))

/-- **Theorem 1, case `α = 0`.**  `q₀` is a permutation polynomial iff `k'` is odd. -/
theorem qKasami_bijective_iff_q0 (hn : Fintype.card L = 2 ^ n) (hk : k < n) (hcop : Nat.Coprime k n)
    (hk' : k * k' % n = 1 % n) (hk0 : 0 < k) (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    Function.Bijective (qKasami (L := L) n k k' 0) ↔ Odd k' := by
  rw [qKasami_bijective_iff hn hk hcop hk' hk0 hexp 0 (Or.inl rfl), Nat.odd_iff]; omega

/-- **Theorem 1, case `α = 1`.**  `q₁` is a permutation polynomial iff
`n ≡ k' + 1 (mod 2)`. -/
theorem qKasami_bijective_iff_q1 (hn : Fintype.card L = 2 ^ n) (hk : k < n) (hcop : Nat.Coprime k n)
    (hk' : k * k' % n = 1 % n) (hk0 : 0 < k) (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    Function.Bijective (qKasami (L := L) n k k' 1) ↔ n % 2 = (k' + 1) % 2 := by
  rw [qKasami_bijective_iff hn hk hcop hk' hk0 hexp 1 (Or.inr rfl)]; omega

/-! ### Proof of Theorem 1 (the paper's argument)

First note that `(2^k − 1)⁻¹ (mod 2ⁿ−1)` exists, since `gcd(k, n) = 1`.  We have
`q_α(0) = 0`, using the convention `0/0 = 0`.

*Only if.*  `k' + α·n ≡ 0 (mod 2)` is equivalent to `q_α(1) = k'·1 + α·Tr(1) = 0`,
so `q_α` is not injective.

*If.*  Assume `k' + α·n ≡ 1 (mod 2)`.  We show that for each fixed `c ∈ L`, the
equation
```
   c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)                     (1)
```
(i.e. `q_α(x) = c`) has at most one solution.  Adding the `2^k`-th power of (1) to
itself gives
```
   ℓ(x) = c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x + 1 = 0.                  (2)
```
Note that `ℓ(x) = 0` iff `c·x^{2^k+1} + Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x) ∈ {0, 1}`.
`ℓ` has one, two or four roots in `L`; at most one of them solves (1). -/

/-- Equation (1): the equation `q_α(x) = c` cleared of denominators,
`c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`. -/
def eqn1 (n k k' : ℕ) (α : ℕ) (c x : L) : Prop :=
  c * x ^ (2 ^ k + 1) = (∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))) + (α : L) * Tr n x

/-- The linearized polynomial `ℓ(x) = c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x + 1` of
equation (2), obtained by adding to (1) its `2^k`-th power. -/
def ell (k : ℕ) (c x : L) : L :=
  c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1

/-
Equation (2) is derived from equation (1) by adding its `2^k`-th power.

**Correction.**  The original skeleton statement (kept commented out below) is
*false*: at `x = 0` the cleared equation `eqn1` holds vacuously (`0 = 0`), yet
`ℓ(0) = 1 ≠ 0`.  The faithful version adds `x ≠ 0` and the field hypotheses
`hn` and `k·k' ≡ 1 (mod n)` (used by the Artin–Schreier telescoping).

theorem eqn2_of_eqn1_orig (α : ℕ) (c x : L) (h : eqn1 (L := L) n k k' α c x) :
    ell (L := L) k c x = 0 := by
  sorry
-/
theorem eqn2_of_eqn1 (hn : Fintype.card L = 2 ^ n) (hkk1 : k * k' % n = 1)
    (α : ℕ) (c x : L) (hx : x ≠ 0) (h : eqn1 (L := L) n k k' α c x) :
    ell (L := L) k c x = 0 := by
  -- Apply the lemma `ell_of_eq` with the given hypotheses.
  apply KasamiPerm.TraceFree.ell_of_eq hn hkk1 (by
  have hα : (α : L) = 0 ∨ (α : L) = 1 := by
    rcases Nat.even_or_odd' α with ⟨ c, rfl | rfl ⟩ <;> simp +decide [ *, CharTwo.two_eq_zero ];
  have hTr : Tr n x = 0 ∨ Tr n x = 1 := by
    convert KasamiPerm.TraceParityCase.trace_bit hn x using 1
  aesop) hx h.symm

/-- The homogeneous part `ℓ₀(x) = ℓ(x) + 1` of (2). -/
def ell0 (k : ℕ) (c x : L) : L := ell (L := L) k c x + 1

/-! #### Case 1: `c ≠ γ^{2^k+1} + γ` for all `γ ∈ L`

In this case the homogeneous part `ℓ₀(x) = ℓ(x) + 1` has no non-zero solution,
since `ℓ₀(x) = (1/c)·(γ₀(x)^{2^k+1} + γ₀(x) + c)²·x` for `γ₀(x) = (c·x^{2^k−1})^{2ⁿ−1}`.
Hence (2) has precisely one solution, and we are done. -/

/-
**Theorem 1, Case 1.**  If `c` is not of the form `γ^{2^k+1} + γ`, then
equation (2) `ℓ(x) = 0` has precisely one solution in `L`.
-/
theorem qKasami_bijective_iff_case1 (hn : Fintype.card L = 2 ^ n) (hk0 : 0 < k) (hkn : k < n)
    (c : L) (hc : ∀ γ : L, c ≠ γ ^ (2 ^ k + 1) + γ) :
    {x : L | ell (L := L) k c x = 0}.ncard = 1 := by
  -- By definition of $ell$, we know that $ell k c x = 0$ if and only if $ell0 k c x = 1$.
  simp [ell];
  -- By definition of $phi$, we know that $phi(x) = c^{2^k} * x^{2^{2k}} + x^{2^k} + c * x$.
  set phi : L → L := fun x => c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x;
  -- To show that `phi` is injective, suppose `phi a = phi b`; set `z := a + b`; then `phi z = phi a + phi b = 0` (additivity, characteristic 2). If `z ≠ 0`, then `KasamiPerm.TraceFree.ell0_root_imp_image hn hk0 hkn (hc' : c ≠ 0) (hz : z ≠ 0) (h0 : c^(2^k)*z^(2^(2*k)) + z^(2^k) + c*z = 0)` produces `γ` with `c = γ^(2^k+1)+γ`, contradicting `hc γ`. So `z = 0`, i.e. `a = b` (char 2: `a + b = 0 → a = b`).
  have h_inj : Function.Injective phi := by
    intro a b hab
    have hz : phi (a + b) = 0 := by
      simp +zetaDelta at *;
      simp_all +decide [ add_pow_char_pow, mul_add, add_assoc ];
      grind
    have hz_zero : a + b = 0 := by
      by_contra hz_nonzero
      have hz_root : ∃ γ : L, c = γ ^ (2 ^ k + 1) + γ := by
        have := @KasamiPerm.TraceFree.ell0_root_imp_image L;
        exact this hn hk0 hkn ( show c ≠ 0 from fun h => hc 0 <| by simp +decide [ h ] ) hz_nonzero hz
      exact hc (hz_root.choose) hz_root.choose_spec
    have h_eq : a = b := by
      grind +revert
    exact h_eq;
  -- Since `phi` is bijective, there is a unique `x` with `phi x = 1`.
  obtain ⟨x, hx⟩ : ∃! x, phi x = 1 := by
    exact ( Finite.injective_iff_surjective.mp h_inj ) 1 |> fun ⟨ x, hx ⟩ => ⟨ x, hx, fun y hy => h_inj <| hy.trans hx.symm ⟩;
  use x;
  grind +suggestions

/-! #### Case 2: `c = γ^{2^k+1} + γ` for some `γ ∈ L`

Setting `Q(x) = c·x^{2^k} + γ²·x + γ` and `f = γ^{2^k−1} + 1/γ` we have
`ℓ(x) = Q(x)^{2^k} + f·Q(x)`, and therefore `ℓ(x) = 0` iff `Q(x) = 0` or
`Q(x) = 1/f^{2^k−1}`.  Introduce auxiliary quantities `λ, Δ, μ` (equations (3)–(5))
so that certain relations (6)–(7) hold.  One shows that precisely one of the two
solutions of `Q(x) = 1/f^{2^k−1}` and none of the solutions of `Q(x) = 0` solves
(1).  For the two roots `x₀, x₁` of `Q(x) = 1/Δ` (with `x₀ + x₁ = Δ`,
`Tr(Δ) = 0`), setting `εⱼ = c·xⱼ^{2^k+1} + Σ_{i=1}^{k'} xⱼ^{2^{ik}} + α·Tr(xⱼ)`
one computes `ε₀ + ε₁ = 1`, hence exactly one `xⱼ` solves (1).  For a root `z` of
`Q(x) = 0` one computes
`c·z^{2^k+1} + Σ_{i=1}^{k'} z^{2^{ik}} + α·Tr(z) = k' + α·n ≡ 1 (mod 2)`, so `z`
does not solve (1). -/

/-- The quadratic-type map `Q(x) = c·x^{2^k} + γ²·x + γ` used in Case 2. -/
def Qmap (k : ℕ) (c γ x : L) : L := c * x ^ (2 ^ k) + γ ^ 2 * x + γ

omit [Fintype L] in
/-- In Case 2, `ℓ(x) = Q(x)^{2^k} + f·Q(x)` where `f = γ^{2^k−1} + γ⁻¹`. -/
theorem ell_eq_Q (k : ℕ) (c γ x : L) (hγ : γ ≠ 0)
    (hc : c = γ ^ (2 ^ k + 1) + γ) :
    ell (L := L) k c x
      = Qmap (L := L) k c γ x ^ (2 ^ k)
        + (γ ^ (2 ^ k - 1) + γ⁻¹) * Qmap (L := L) k c γ x := by
  unfold ell Qmap
  exact KasamiPerm.TraceFree.Q_factor hγ hc x

/-
**Theorem 1, Case 2.**  If `c = γ^{2^k+1} + γ` (with `c ≠ 0`), then exactly one
**nonzero** `x` solves equation (1).

**Correction.**  The original skeleton statement (kept commented out below)
counted *all* solutions of the cleared equation `eqn1`; but `x = 0` always
satisfies `eqn1` (both sides are `0`), so that count is never `1` when a genuine
(nonzero) solution exists.  The paper's claim — "exactly one of the roots solves
(1)" — is faithfully the count of **nonzero** solutions, which needs `c ≠ 0`
(equivalently `γ ≠ 1`, since `γ = 1` gives `c = 0`).

theorem qKasami_bijective_iff_case2_orig (hn : Fintype.card L = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (α : ℕ) (hα : α = 0 ∨ α = 1)
    (hpar : (k' + α * n) % 2 = 1) (c γ : L) (hγ : γ ≠ 0)
    (hc : c = γ ^ (2 ^ k + 1) + γ) :
    {x : L | eqn1 (L := L) n k k' α c x}.ncard = 1 := by
  sorry
-/
theorem qKasami_bijective_iff_case2 (hn : Fintype.card L = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (hk0 : 0 < k)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (α : ℕ) (hα : α = 0 ∨ α = 1)
    (hpar : (k' + α * n) % 2 = 1) (c γ : L) (hc0 : c ≠ 0)
    (hc : c = γ ^ (2 ^ k + 1) + γ) :
    {x : L | x ≠ 0 ∧ eqn1 (L := L) n k k' α c x}.ncard = 1 := by
  convert Set.ncard_eq_one.mpr _ using 1;
  obtain ⟨a, ha⟩ : ∃ a : L, qKasami (L := L) n k k' α a = c ∧ a ≠ 0 := by
    obtain ⟨a, ha⟩ : ∃ a : L, qKasami (L := L) n k k' α a = c := by
      convert Function.Bijective.surjective ( qKasami_bijective_iff hn hk hcop hk' hk0 hexp α hα |>.2 hpar ) c using 1;
    refine' ⟨ a, ha, _ ⟩ ; rintro rfl ; simp_all +decide [ qKasami ];
    rw [ zero_pow ( Nat.sub_ne_zero_of_lt hexp ) ] at ha ; aesop;
  refine' ⟨ a, Set.eq_singleton_iff_unique_mem.mpr ⟨ _, fun x hx => _ ⟩ ⟩ <;> simp_all +decide [ eqn1 ];
  · convert qKasami_mul_unit ( hn := hn ) ( show 2 ^ k + 1 ≤ 2 ^ n - 1 from le_of_lt hexp ) α ha.2 using 1 ; aesop;
  · have h_eq : qKasami (L := L) n k k' α x = γ ^ (2 ^ k + 1) + γ := by
      have h_eq : qKasami (L := L) n k k' α x * x ^ (2 ^ k + 1) = (∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))) + (α : L) * Tr n x := by
        convert qKasami_mul_unit hn ( le_of_lt hexp ) α hx.1 using 1;
      exact mul_left_cancel₀ ( pow_ne_zero ( 2 ^ k + 1 ) hx.1 ) ( by linear_combination' h_eq - hx.2 );
    have h_eq : Function.Bijective (qKasami (L := L) n k k' α) := by
      apply (qKasami_bijective_iff hn hk hcop hk' hk0 hexp α hα).mpr hpar;
    exact h_eq.injective ( by aesop )

/-! ## Corollary 2

> **Corollary 2.** Kasami power functions are almost perfect nonlinear.

*Proof.*  If `k' ≡ 1/k (mod n)` is odd, set `q = q₀`; otherwise set `q = q₁`
(if `k'` is even then `n` must be odd, since `k'` and `n` are relatively prime).
By Theorem 1, `q` is a permutation polynomial.  A routine computation shows that
for `p(t) = (t+1)ᵈ + tᵈ + 1` we have `p(t) = 1/q(t^{2^k} + t)`.  On the other hand
`t ↦ t^{2^k} + t` maps two-to-one, since `gcd(k, n) = 1`.  ∎ -/

/-- The Kasami derivative `p(t) = (t+1)ᵈ + tᵈ + 1`. -/
def kasamiDeriv (k : ℕ) (t : L) : L :=
  (t + 1) ^ (kasamiExp k) + t ^ (kasamiExp k) + 1

/-
The routine computation of the proof of Corollary 2:
`p(t) = 1/q(t^{2^k} + t)`, i.e. `p(t)·q(t^{2^k} + t) = 1` for `t ∉ 𝔽₂`.
-/
theorem routine_computation (hn : Fintype.card L = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (hk0 : 0 < k) (α : ℕ)
    (t : L) (ht : t ^ 2 + t ≠ 0) :
    kasamiDeriv (L := L) k t * qKasami (L := L) n k k' α (t ^ (2 ^ k) + t) = 1 := by
  have h_sub : qKasami n k k' α (t ^ (2 ^ k) + t) = qKasami n k k' 0 (t ^ (2 ^ k) + t) := by
    have h_trace_zero : Tr n (t ^ (2 ^ k) + t) = 0 := by
      convert KasamiPerm.TraceCore.trace_artin_schreier_zero hn k t using 1;
    unfold qKasami; aesop;
  rw [ h_sub, qKasami_zero_eq_qeps ];
  have h_sub : TraceFree.qeps n k k' 0 (t ^ (2 ^ k) + t) * (t ^ (2 ^ k) + t) ^ (2 ^ k + 1) = (t ^ 2 + t) ^ (2 ^ k) := by
    rw [ TraceFree.qeps_mul_unit ];
    · have h_sub : TraceFree.sTrace k k' (t ^ (2 ^ k) + t) = (t ^ 2 + t) ^ (2 ^ k) := by
        have h_sub : ∑ i ∈ Finset.Ico 1 (k' + 1), (t ^ (2 ^ k) + t) ^ (2 ^ (i * k)) = (t ^ 2 + t) ^ (2 ^ k) := by
          apply KasamiPerm.TraceCore.sum_u_collapse hn;
          exact Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide );
          rw [ mul_comm, ← Nat.mod_add_div ( k * k' ) n, hk' ];
          rw [ Nat.mod_eq_of_lt ( show 1 < n from lt_of_le_of_lt ( Nat.succ_le_of_lt hk0 ) hk ), add_comm ];
          rw [ mul_comm ]
        convert h_sub using 1;
      rw [ h_sub, add_zero ];
    · exact hn;
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ];
      exact lt_tsub_iff_left.mpr ( by rw [ show 2 ^ k = 2 ^ ( k - 1 ) * 2 by rw [ ← pow_succ, Nat.sub_add_cancel hk0 ] ] ; nlinarith [ pow_pos ( zero_lt_two' ℕ ) ( k - 1 ), pow_le_pow_right₀ ( show 1 ≤ 2 by decide ) ( show k - 1 ≤ n by exact Nat.sub_le_of_le_add <| by linarith ) ] );
    · contrapose! ht;
      have h_frob : t ^ (2 ^ k) = t := by
        grind;
      have := KasamiPerm.TraceCore.frob_k_fixed hn hk0 hcop h_frob; aesop;
  have h_sub : kasamiDeriv k t * (t ^ 2 + t) ^ (2 ^ k) = (t ^ (2 ^ k) + t) ^ (2 ^ k + 1) := by
    convert KasamiPerm.MCMtoAPN.kasami_key_identity hn k hk0 hk t using 1;
  have h_sub : (t ^ (2 ^ k) + t) ^ (2 ^ k + 1) ≠ 0 := by
    intro h; simp_all +decide [ pow_succ' ] ;
    rw [ eq_comm ] at ‹0 = ( t * t + t ) ^ 2 ^ k› ; simp_all +decide;
  grind

/-
The map `t ↦ t^{2^k} + t` is two-to-one on `L = 𝔽_{2ⁿ}` when `gcd(k, n) = 1`.
-/
theorem frob_shift_two_to_one (hn : Fintype.card L = 2 ^ n) (hk0 : 0 < k)
    (hcop : Nat.Coprime k n) :
    TwoToOne (fun t : L => t ^ (2 ^ k) + t) := by
  intro x
  have h_eq : {y : L | y ^ (2 ^ k) + y = x ^ (2 ^ k) + x} = {x, x + 1} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff];
    constructor <;> intro h;
    · have h_eq : (y - x) ^ (2 ^ k) = y - x := by
        simp_all +decide [ sub_pow_char_pow ];
        grind;
      have h_eq : (y - x) ^ 2 = y - x := by
        convert KasamiPerm.TraceCore.frob_k_fixed hn hk0 hcop h_eq using 1;
      exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linear_combination' h_eq;
    · rcases h with ( rfl | rfl ) <;> simp +decide [ add_pow_char_pow ];
      grind
  rw [h_eq, Set.ncard_pair];
  simp +decide

/-
The Kasami derivative `p(t) = (t+1)ᵈ + tᵈ + 1` is two-to-one on `L = 𝔽_{2ⁿ}`.

This is the heart of Corollary 2: choosing `α` so that `q_α` is a permutation
(possible since `k'` and `n` are not both even), the routine computation
`p(t)·q_α(t^{2^k}+t) = 1` (for `t ∉ 𝔽₂`) writes `p = (·)⁻¹ ∘ q_α ∘ (t ↦ t^{2^k}+t)`.
Since `t ↦ t^{2^k}+t` is two-to-one (`frob_shift_two_to_one`), `q_α` is a
bijection, and `(·)⁻¹` is injective on units, every fibre of `p` has exactly two
elements (the fibre over `0` being `{0, 1}`).
-/
theorem kasamiDeriv_two_to_one (hn : Fintype.card L = 2 ^ n) (hk : k < n)
    (hcop : Nat.Coprime k n) (hk' : k * k' % n = 1 % n) (hk0 : 0 < k)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    TwoToOne (kasamiDeriv (L := L) k) := by
  intro x
  by_cases hx : kasamiDeriv (L := L) k x = 0;
  · have h_cases : ∀ t : L, kasamiDeriv (L := L) k t = 0 ↔ (t = 0 ∨ t = 1) := by
      intro t
      constructor
      intro ht
      have h_cases : t = 0 ∨ t = 1 := by
        by_contra h_contra;
        have h_nonzero : t ^ 2 + t ≠ 0 := by
          grind +suggestions;
        have := KasamiPerm.Headlines.routine_computation hn hk hcop hk' hk0 0 t h_nonzero; simp_all +decide ;
      exact h_cases
      intro ht
      cases ht <;> simp_all +decide [ kasamiDeriv ];
      · rw [ zero_pow ] <;> norm_num [ kasamiExp ];
        exact CharP.cast_eq_zero L 2;
      · grind +locals;
    simp_all +decide;
    rw [ show kasamiDeriv k x = 0 by cases hx <;> simp +decide [ * ] ] ; rw [ show { y : L | kasamiDeriv k y = 0 } = { 0, 1 } by ext; simp +decide [ h_cases ] ] ; simp +decide ;
  · have h_eq : ∀ y : L, kasamiDeriv k y = kasamiDeriv k x → y = x ∨ y = x + 1 := by
      intro y hy
      have h_eq : (y ^ (2 ^ k) + y) = (x ^ (2 ^ k) + x) := by
        have h_eq : kasamiDeriv k x * qKasami (L := L) n k k' (if Odd k' then 0 else 1) (x ^ (2 ^ k) + x) = 1 ∧ kasamiDeriv k y * qKasami (L := L) n k k' (if Odd k' then 0 else 1) (y ^ (2 ^ k) + y) = 1 := by
          apply And.intro;
          · apply routine_computation hn hk hcop hk' hk0 (if Odd k' then 0 else 1) x;
            intro h;
            have h_cases : x = 0 ∨ x = 1 := by
              grind +suggestions;
            cases h_cases <;> simp_all +decide [ kasamiDeriv ];
            · simp_all +decide [ kasamiExp ];
              grind;
            · simp_all +decide [ kasamiExp ];
          · apply KasamiPerm.Headlines.routine_computation hn hk hcop hk' hk0 (if Odd k' then 0 else 1) y;
            contrapose! hy; simp_all +decide [ kasamiDeriv ] ;
            have hy_cases : y = 0 ∨ y = 1 := by
              grind +suggestions;
            cases hy_cases <;> simp_all +decide [ kasamiExp ]; all_goals grind +suggestions;
        have h_eq : Function.Bijective (qKasami (L := L) n k k' (if Odd k' then 0 else 1)) := by
          apply (qKasami_bijective_iff hn hk hcop hk' hk0 hexp (if Odd k' then 0 else 1) (by split_ifs <;> simp +decide)).mpr;
          split_ifs <;> simp_all +decide [ Nat.odd_iff ];
          rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
          replace hk' := congr_arg ( · % 2 ) hk'; simp_all +decide [ Nat.mul_mod ] ;
        exact h_eq.injective ( mul_left_cancel₀ hx <| by aesop );
      have h_eq : (y - x) ^ (2 ^ k) = y - x := by
        have h_eq : (y - x) ^ (2 ^ k) + (y - x) = 0 := by
          rw [ sub_pow_char_pow ] ; linear_combination' h_eq;
        grind;
      have h_eq : (y - x) ^ 2 = y - x := by
        apply KasamiPerm.TraceCore.frob_k_fixed hn hk0 hcop h_eq;
      exact Classical.or_iff_not_imp_left.2 fun h => mul_left_cancel₀ ( sub_ne_zero_of_ne h ) <| by linear_combination' h_eq;
    rw [ Set.ncard_eq_two ];
    refine' ⟨ x, x + 1, _, _ ⟩ <;> simp_all +decide [ Set.ext_iff ];
    intro y; specialize h_eq y; simp_all +decide [ kasamiDeriv ] ;
    refine' ⟨ h_eq, fun h => _ ⟩ ; rcases h with ( rfl | rfl ) <;> ring;
    rw [ show ( 2 : L ) = 0 by exact CharTwo.two_eq_zero ] ; ring

/-
**Corollary 2 (Dobbertin 1999).**  Kasami power functions `x ↦ xᵈ` with
`d = 2^{2k} − 2^k + 1`, `k < n`, `gcd(k, n) = 1`, are almost perfect nonlinear.
-/
theorem kasami_isAPN (hn : Fintype.card L = 2 ^ n) (hk : k < n) (hcop : Nat.Coprime k n)
    (hk0 : 0 < k) (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    IsAPN (fun x : L => x ^ kasamiExp k) := by
  intro a ha b;
  obtain ⟨c, hc⟩ : ∃ c : L, {x : L | (x + a) ^ (kasamiExp k) + x ^ (kasamiExp k) = b} = (fun y => y * a) '' {y : L | kasamiDeriv (L := L) k y + 1 = c} := by
                                                                                                              refine' ⟨ b * ( a ^ kasamiExp k ) ⁻¹, _ ⟩;
                                                                                                              ext x
                                                                                                              simp [kasamiDeriv];
                                                                                                              constructor;
                                                                                                              · intro hx
                                                                                                                use x / a;
                                                                                                                field_simp [hx];
                                                                                                                simp +decide [ ← hx, add_mul, add_comm, div_pow, ha ];
                                                                                                                grind;
                                                                                                              · rintro ⟨ y, hy, rfl ⟩;
                                                                                                                convert congr_arg ( · * a ^ kasamiExp k ) hy using 1 <;> ring;
                                                                                                                · rw [ show y * a + a = a * ( 1 + y ) by ring, mul_pow ] ; ring;
                                                                                                                  grind;
                                                                                                                · simp +decide [ ha ];
  have h_card : {y : L | kasamiDeriv (L := L) k y + 1 = c}.ncard = 0 ∨ {y : L | kasamiDeriv (L := L) k y + 1 = c}.ncard = 2 := by
                                                                          have h_card : TwoToOne (kasamiDeriv (L := L) k) := by
                                                                            have h_two_to_one : ∃ k' : ℕ, k * k' % n = 1 % n := by
                                                                              have := Nat.exists_mul_mod_eq_one_of_coprime hcop;
                                                                              rcases n with ( _ | _ | n ) <;> simp_all +decide;
                                                                              exact ⟨ this.choose, this.choose_spec.2 ⟩;
                                                                            exact KasamiPerm.Headlines.kasamiDeriv_two_to_one hn hk hcop h_two_to_one.choose_spec hk0 hexp;
                                                                          by_cases h : ∃ y : L, kasamiDeriv (L := L) k y + 1 = c <;> simp_all +decide [ TwoToOne ];
                                                                          obtain ⟨ y, hy ⟩ := h; specialize h_card y; simp_all +decide [ ← eq_sub_iff_add_eq ] ;
  rw [ hc, Set.ncard_image_of_injective _ fun x y hxy => mul_right_cancel₀ ha hxy ] ; tauto;

end KasamiPerm.Headlines
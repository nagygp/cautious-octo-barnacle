import Mathlib
import RequestProject.KasamiPermutation.Casoratian

/-!
# Theorem 6 (Dobbertin 1999) — the concrete cubic collapse

This file builds, *bottom up*, the concrete layer of the proof of Theorem 6 that
sits on top of the abstract Casoratian core in `Casoratian.lean`.

Dobbertin introduces three polynomial families `A_i , B_i , C_i` (here
`Aseq , Bseq , Cseq`) obeying a shared two-step linear recurrence with the
**concrete Frobenius exponents**

* `u_i = z ^ (2 ^ ((i+1) k))`               (`Zc z k (i+1)`),
* `v_i = z ^ (2 ^ ((i+1) k) − 2 ^ (i k))`   (`vc z k i`),

together with the driven `C`-family whose source term is `u_i` again.  The proof
of Theorem 6 substitutes the inductively unfolded equation (10) into equation (8)
and collapses everything to a single cubic

  `x³ + Λ₂ x² + Λ₁ x + Λ₀ = 0`,

and then observes (the "lucky" step) that `Λ₁ = Λ₀ = 0` **as polynomial
identities in `Aᵢ, Bᵢ, Cᵢ`**.  Crucially these identities are *not* consequences
of the abstract recurrence alone: they need the concrete relation
`v_i · Zᵢ = Z_{i+1} = u_i` between the Frobenius exponents.  This file carries
that arithmetic through the whole collapse.

The dependency DAG (bottom up):

```
  exponent arithmetic (vc_mul_Zc)                -- concrete Frobenius layer
        │
  recurrences (Aseq_rec, Bseq_rec, Cseq_rec)     -- A_i, B_i, C_i
        │
  eq (11)  cross_invariant  ── key_identity  →   AB_cross  (= Casoratian core)
        │
  driven  AC_cross                               -- inhomogeneous Casoratian
        │
  eq (12)  sum_eq12   ──►  Λ₁ = 0
  eq (13)  sum_eq13   ──►  Λ₀ = 0
```
-/

namespace KasamiPerm.InverseRec

open scoped BigOperators

/-! ## Generic two-step recurrences -/

/-- A two-step linear recurrence `s (n+2) = u n · s (n+1) + v n · s n` with the
two seed values `a = s 0`, `b = s 1`. -/
def twoStep {R : Type*} [CommRing R] (a b : R) (u v : ℕ → R) : ℕ → R
  | 0 => a
  | 1 => b
  | (n + 2) => u n * twoStep a b u v (n + 1) + v n * twoStep a b u v n

/-- A *driven* (inhomogeneous) two-step linear recurrence
`s (n+2) = u n · s (n+1) + v n · s n + w n`. -/
def twoStepSrc {R : Type*} [CommRing R] (a b : R) (u v w : ℕ → R) : ℕ → R
  | 0 => a
  | 1 => b
  | (n + 2) => u n * twoStepSrc a b u v w (n + 1) + v n * twoStepSrc a b u v w n + w n

@[simp] theorem twoStep_zero {R : Type*} [CommRing R] (a b : R) (u v : ℕ → R) :
    twoStep a b u v 0 = a := rfl

@[simp] theorem twoStep_one {R : Type*} [CommRing R] (a b : R) (u v : ℕ → R) :
    twoStep a b u v 1 = b := rfl

theorem twoStep_succ_succ {R : Type*} [CommRing R] (a b : R) (u v : ℕ → R) (n : ℕ) :
    twoStep a b u v (n + 2) = u n * twoStep a b u v (n + 1) + v n * twoStep a b u v n := rfl

@[simp] theorem twoStepSrc_zero {R : Type*} [CommRing R] (a b : R) (u v w : ℕ → R) :
    twoStepSrc a b u v w 0 = a := rfl

@[simp] theorem twoStepSrc_one {R : Type*} [CommRing R] (a b : R) (u v w : ℕ → R) :
    twoStepSrc a b u v w 1 = b := rfl

theorem twoStepSrc_succ_succ {R : Type*} [CommRing R] (a b : R) (u v w : ℕ → R) (n : ℕ) :
    twoStepSrc a b u v w (n + 2)
      = u n * twoStepSrc a b u v w (n + 1) + v n * twoStepSrc a b u v w n + w n := rfl

/-- A custom two-step induction principle: to prove `P j` for all `j`, prove it for
`0, 1, 2`, and prove `P (n+3)` from `P (n+1)` and `P (n+2)`.  The step always fires
at an index `n+1 ≥ 1`, which is what lets us split the partial sums cleanly. -/
theorem two_step_ind (P : ℕ → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (step : ∀ n, P (n + 1) → P (n + 2) → P (n + 3)) : ∀ j, P j := by
  have key : ∀ n, P n ∧ P (n + 1) ∧ P (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2⟩
    | succ m ih =>
      obtain ⟨hm, hm1, hm2⟩ := ih
      exact ⟨hm1, hm2, step m hm1 hm2⟩
  intro j
  exact (key j).1

/-! ## The concrete Frobenius exponent layer (characteristic-free) -/

section CommRingLayer

variable {R : Type*} [CommRing R] (z : R) (k : ℕ)

/-- `Zc z k i = z ^ (2 ^ (i k))`, the `i`-th Frobenius power of `z` along step `k`.
This plays the role of the conserved Casoratian value `z_i` of equation (11). -/
def Zc (i : ℕ) : R := z ^ (2 ^ (i * k))

/-- `vc z k i = z ^ (2 ^ ((i+1) k) − 2 ^ (i k))`, the lower recurrence coefficient. -/
def vc (i : ℕ) : R := z ^ (2 ^ ((i + 1) * k) - 2 ^ (i * k))

theorem Zexp_le (i : ℕ) : 2 ^ (i * k) ≤ 2 ^ ((i + 1) * k) := by
  apply Nat.pow_le_pow_right (by norm_num)
  have : (i + 1) * k = i * k + k := by ring
  omega

/-- The single concrete Frobenius fact that powers the whole collapse:
`v_i · Z_i = Z_{i+1}`. -/
theorem vc_mul_Zc (i : ℕ) : vc z k i * Zc z k i = Zc z k (i + 1) := by
  unfold vc Zc
  rw [← pow_add]
  congr 1
  have h := Zexp_le (k := k) i
  omega

/-! ## The three families `A_i , B_i , C_i` -/

/-- `Aseq z k`: `A₀ = 0`, `A₁ = z`, `A_{i+2} = u_i A_{i+1} + v_i A_i`. -/
def Aseq : ℕ → R := twoStep (0 : R) z (fun n => Zc z k (n + 1)) (fun n => vc z k n)

/-- `Bseq z k`: `B₀ = 1`, `B₁ = 0`, `B_{i+2} = u_i B_{i+1} + v_i B_i`. -/
def Bseq : ℕ → R := twoStep (1 : R) (0 : R) (fun n => Zc z k (n + 1)) (fun n => vc z k n)

/-- `Cseq z k`: `C₀ = 0`, `C₁ = 0`, `C_{i+2} = u_i C_{i+1} + v_i C_i + u_i`. -/
def Cseq : ℕ → R :=
  twoStepSrc (0 : R) (0 : R) (fun n => Zc z k (n + 1)) (fun n => vc z k n) (fun n => Zc z k (n + 1))

@[simp] theorem Aseq_zero : Aseq z k 0 = 0 := rfl
@[simp] theorem Aseq_one : Aseq z k 1 = z := rfl
@[simp] theorem Bseq_zero : Bseq z k 0 = 1 := rfl
@[simp] theorem Bseq_one : Bseq z k 1 = 0 := rfl
@[simp] theorem Cseq_zero : Cseq z k 0 = 0 := rfl
@[simp] theorem Cseq_one : Cseq z k 1 = 0 := rfl

theorem Aseq_rec (n : ℕ) :
    Aseq z k (n + 2) = Zc z k (n + 1) * Aseq z k (n + 1) + vc z k n * Aseq z k n := rfl

theorem Bseq_rec (n : ℕ) :
    Bseq z k (n + 2) = Zc z k (n + 1) * Bseq z k (n + 1) + vc z k n * Bseq z k n := rfl

theorem Cseq_rec (n : ℕ) :
    Cseq z k (n + 2)
      = Zc z k (n + 1) * Cseq z k (n + 1) + vc z k n * Cseq z k n + Zc z k (n + 1) := rfl

/-! ## Partial sums (`∑_{i=1}^{j-1}`) -/

/-- `SA z k j = ∑_{i=1}^{j-1} Aᵢ`. -/
def SA (j : ℕ) : R := ∑ i ∈ Finset.Ico 1 j, Aseq z k i
/-- `SB z k j = ∑_{i=1}^{j-1} Bᵢ`. -/
def SB (j : ℕ) : R := ∑ i ∈ Finset.Ico 1 j, Bseq z k i
/-- `SC z k j = ∑_{i=1}^{j-1} Cᵢ`. -/
def SC (j : ℕ) : R := ∑ i ∈ Finset.Ico 1 j, Cseq z k i
/-- `TA z k j = ∑_{i=1}^{j} Aᵢ` (running total including index `j`). -/
def TA (j : ℕ) : R := ∑ i ∈ Finset.Ico 1 (j + 1), Aseq z k i

@[simp] theorem SA_zero : SA z k 0 = 0 := by simp [SA]
@[simp] theorem SA_one : SA z k 1 = 0 := by simp [SA]
@[simp] theorem SB_zero : SB z k 0 = 0 := by simp [SB]
@[simp] theorem SB_one : SB z k 1 = 0 := by simp [SB]
@[simp] theorem SC_zero : SC z k 0 = 0 := by simp [SC]
@[simp] theorem SC_one : SC z k 1 = 0 := by simp [SC]

theorem SA_succ (j : ℕ) (hj : 1 ≤ j) : SA z k (j + 1) = SA z k j + Aseq z k j := by
  simp only [SA]; rw [Finset.sum_Ico_succ_top hj]

theorem SB_succ (j : ℕ) (hj : 1 ≤ j) : SB z k (j + 1) = SB z k j + Bseq z k j := by
  simp only [SB]; rw [Finset.sum_Ico_succ_top hj]

theorem SC_succ (j : ℕ) (hj : 1 ≤ j) : SC z k (j + 1) = SC z k j + Cseq z k j := by
  simp only [SC]; rw [Finset.sum_Ico_succ_top hj]

theorem TA_eq_SA_succ (j : ℕ) : TA z k j = SA z k (j + 1) := rfl

theorem TA_succ (j : ℕ) (hj : 1 ≤ j) : TA z k j = SA z k j + Aseq z k j := by
  rw [TA_eq_SA_succ, SA_succ z k j hj]

/-! ## The normalized coefficient family `aᵢ = Aᵢ / y`

In the field-level equation (10), the coefficient of `x^{2^k}` is `aᵢ = Aᵢ(y)/y`,
whereas `bᵢ = Bᵢ(y)` and `cᵢ = Cᵢ(y)` are the families themselves.  Rather than
divide, we record `aseq` as the same two-step recurrence with seed `1` (instead of
`z`): then `z · aseq i = Aseq z k i`, and `aseq` obeys the exact same recurrence. -/

/-- `aseq z k`: `a₀ = 0`, `a₁ = 1`, `a_{i+2} = u_i a_{i+1} + v_i a_i`.  This is
`Aseq z k` renormalized by the seed, i.e. `aseq i = Aᵢ(z)/z`. -/
def aseq : ℕ → R := twoStep (0 : R) (1 : R) (fun n => Zc z k (n + 1)) (fun n => vc z k n)

@[simp] theorem aseq_zero : aseq z k 0 = 0 := rfl
@[simp] theorem aseq_one : aseq z k 1 = 1 := rfl

theorem aseq_rec (n : ℕ) :
    aseq z k (n + 2) = Zc z k (n + 1) * aseq z k (n + 1) + vc z k n * aseq z k n := rfl

theorem aseq_two : aseq z k 2 = Zc z k 1 := by
  rw [aseq_rec]; simp

/-- Iterated-Frobenius law for `Zc`: `(Zᵐ)^{2^{ik}} = Z_{m+i}`. -/
theorem Zc_pow (m i : ℕ) : (Zc z k m) ^ (2 ^ (i * k)) = Zc z k (m + i) := by
  unfold Zc
  rw [← pow_mul, ← pow_add, Nat.add_mul]

/-- Iterated-Frobenius law identifying `(v₀)^{2^{ik}}` with `vᵢ`. -/
theorem vc_pow0 (i : ℕ) : (vc z k 0) ^ (2 ^ (i * k)) = vc z k i := by
  unfold vc
  rw [← pow_mul]
  congr 1
  have e3 : 2 ^ k * 2 ^ (i * k) = 2 ^ ((i + 1) * k) := by
    rw [← pow_add]; congr 1; ring
  have h1 : (0 + 1) * k = k := by ring
  have h2 : 0 * k = 0 := by ring
  rw [h1, h2, pow_zero, Nat.sub_mul, one_mul, e3]

end CommRingLayer

/-! ## The characteristic-2 layer -/

section CharTwoLayer

variable {R : Type*} [CommRing R] [CharP R 2] (z : R) (k : ℕ)

/-- **Equation (11)**: `Aᵢ B_{i+1} + A_{i+1} Bᵢ = Zᵢ` for all `i`.  This is the
char-2 Casoratian / cross-invariant of the shared homogeneous recurrence,
reusing the abstract `KasamiPerm.Casoratian.key_identity`, together with the concrete
Frobenius fact `vc_mul_Zc`. -/
theorem AB_cross (i : ℕ) :
    Aseq z k i * Bseq z k (i + 1) + Aseq z k (i + 1) * Bseq z k i = Zc z k i := by
  have hstep : KasamiPerm.Casoratian.TwoStep (fun n => Zc z k (n + 1)) (fun n => vc z k n)
      (Aseq z k) (Bseq z k) :=
    ⟨Aseq_rec z k, Bseq_rec z k⟩
  have hz : ∀ i, Zc z k (i + 1) = vc z k i * Zc z k i := fun i => (vc_mul_Zc z k i).symm
  have h0 : Aseq z k 0 * Bseq z k 1 + Aseq z k 1 * Bseq z k 0 = Zc z k 0 := by
    simp [Zc]
  exact KasamiPerm.Casoratian.key_identity hstep hz h0 i

/-
Driven Casoratian for the inhomogeneous `C`-family:
`Aⱼ C_{j+1} + A_{j+1} Cⱼ = Zⱼ · (∑_{i=1}^{j} Aᵢ)`.  Proved by induction using the
`C`-recursion, the exponent fact `vc_mul_Zc`, and characteristic 2.
-/
theorem AC_cross (j : ℕ) :
    Aseq z k j * Cseq z k (j + 1) + Aseq z k (j + 1) * Cseq z k j
      = Zc z k j * TA z k j := by
  induction' j with j ih
  · simp [Aseq, Cseq, TA]
  · have hTA_succ : TA z k (j + 1) = TA z k j + Aseq z k (j + 1) :=
      Finset.sum_Ico_succ_top (by linarith) _
    have hv := vc_mul_Zc z k j
    have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
    rw [Aseq_rec, Cseq_rec, hTA_succ]
    linear_combination vc z k j * ih + TA z k j * hv
      + (Zc z k (j + 1) * Aseq z k (j + 1) * Cseq z k (j + 1)) * h2

/-
**Equation (12)**: `Aⱼ (∑_{i<j} Bᵢ) + Bⱼ (∑_{i<j} Aᵢ) = Cⱼ`.  This is the
identity that forces `Λ₁ = 0`.
-/
theorem sum_eq12 (j : ℕ) :
    Aseq z k j * SB z k j + Bseq z k j * SA z k j = Cseq z k j := by
  induction' j using KasamiPerm.InverseRec.two_step_ind with j ih₁ ih₂;
  · simp +decide [ KasamiPerm.InverseRec.Aseq, KasamiPerm.InverseRec.Bseq, KasamiPerm.InverseRec.Cseq, KasamiPerm.InverseRec.SA, KasamiPerm.InverseRec.SB ];
  · simp +decide [ SB, SA, Cseq ];
  · simp +decide [ KasamiPerm.InverseRec.Aseq_rec, KasamiPerm.InverseRec.Bseq_rec, KasamiPerm.InverseRec.Cseq_rec, KasamiPerm.InverseRec.SA, KasamiPerm.InverseRec.SB ];
    convert vc_mul_Zc z k 0 using 1 ; simp +decide [ Zc ];
  · simp_all +decide [ SB_succ, SA_succ, Cseq_rec, Aseq_rec, Bseq_rec ];
    grind +suggestions

/-
**Equation (13)**: `Aⱼ (∑_{i<j} Cᵢ) + Cⱼ (∑_{i<j} Aᵢ) = (j+1) Aⱼ`.  This is the
identity that forces `Λ₀ = 0`.
-/
theorem sum_eq13 (j : ℕ) :
    Aseq z k j * SC z k j + Cseq z k j * SA z k j = (j + 1 : ℕ) * Aseq z k j := by
  induction' j using KasamiPerm.InverseRec.two_step_ind with j ih;
  · simp +decide [ Aseq, Cseq, SA, SC ];
  · simp +decide [ Aseq, Cseq, SA, SC ];
    rw [ CharTwo.two_eq_zero, MulZeroClass.zero_mul ];
  · simp +decide [ Aseq_rec, Cseq_rec, SA_succ, SC_succ ];
    grind +suggestions;
  · have := KasamiPerm.InverseRec.AC_cross z k ( j + 1 ) ; have := KasamiPerm.InverseRec.vc_mul_Zc z k ( j + 1 ) ; have := KasamiPerm.InverseRec.TA_succ z k ( j + 1 ) ; simp_all +decide [ Nat.cast_add, CharTwo.two_eq_zero ] ;
    simp_all +decide [ KasamiPerm.InverseRec.Aseq_rec, KasamiPerm.InverseRec.Cseq_rec, KasamiPerm.InverseRec.SC_succ, KasamiPerm.InverseRec.SA_succ ];
    grind +ring

/-! ## The cubic collapse: `Λ₁ = Λ₀ = 0` -/

/-- The linear coefficient of the collapsed cubic (equation for `Λ₁`):
`Λ₁ = C_{k'} + A_{k'} (∑_{i<k'} Bᵢ) + B_{k'} (∑_{i<k'} Aᵢ)`. -/
def Lam1 (kk : ℕ) : R :=
  Cseq z k kk + (Aseq z k kk * SB z k kk + Bseq z k kk * SA z k kk)

/-- The constant coefficient of the collapsed cubic (equation for `Λ₀`):
`Λ₀ = A_{k'} (∑_{i<k'} Cᵢ) + C_{k'} (∑_{i<k'} Aᵢ) + (k'+1) A_{k'}`. -/
def Lam0 (kk : ℕ) : R :=
  (Aseq z k kk * SC z k kk + Cseq z k kk * SA z k kk) + (kk + 1 : ℕ) * Aseq z k kk

/-- **`Λ₁ = 0`.**  The linear coefficient of the cubic vanishes, for every `k'`. -/
theorem Lam1_eq_zero (kk : ℕ) : Lam1 z k kk = 0 := by
  have h := sum_eq12 z k kk
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  unfold Lam1
  rw [h]
  linear_combination (Cseq z k kk) * h2

/-- **`Λ₀ = 0`.**  The constant coefficient of the cubic vanishes, for every `k'`. -/
theorem Lam0_eq_zero (kk : ℕ) : Lam0 z k kk = 0 := by
  have h := sum_eq13 z k kk
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  unfold Lam0
  rw [h]
  linear_combination ((kk + 1 : ℕ) : R) * (Aseq z k kk) * h2

/-! ## Equation (10): the inductive unfolding

Following Dobbertin, equation (10) states that the element `x` (a root of the
inverse equation) satisfies, for every `i`,

  `x^{2^{ik}} + aᵢ x^{2^k} + bᵢ x + cᵢ = 0`,

with `aᵢ = Aᵢ(y)/y`, `bᵢ = Bᵢ(y)`, `cᵢ = Cᵢ(y)`.  Here `z` plays the role of the
parameter `y` and `x` is the variable.  We package the left-hand side as the
residual `Eqn10 z k x i` and prove that it vanishes for all `i` as soon as it
vanishes at `i = 2` (which is equation (9), the linearized form of (8)).  The
base case `i = 1` (and `i = 0`) is automatic in characteristic 2. -/

/-- The residual of equation (10):
`Eqn10 z k x i = x^{2^{ik}} + aᵢ x^{2^k} + bᵢ x + cᵢ`. -/
def Eqn10 (x : R) (i : ℕ) : R :=
  x ^ (2 ^ (i * k)) + aseq z k i * x ^ (2 ^ k) + Bseq z k i * x + Cseq z k i

/-
**The equation-(10) recurrence.**  The residuals obey the same homogeneous
two-step recurrence as the coefficient families, driven by the `2^{ik}`-th
Frobenius power of the base residual `Eqn10 z k x 2` (equation (9)):

  `E_{i+2} = u_i E_{i+1} + v_i E_i + (E_2)^{2^{ik}}`.

This is the identity Dobbertin obtains by adding the `2^{ik}`-th power of (9) to
the two previous instances of (10); the two middle Frobenius terms cancel in
characteristic 2.  Its proof carries the concrete Frobenius exponent arithmetic
(`Zc_pow`, `vc_pow0`, the freshman's dream `add_pow_char_pow`).
-/
theorem Eqn10_rec (x : R) (i : ℕ) :
    Eqn10 z k x (i + 2)
      = Zc z k (i + 1) * Eqn10 z k x (i + 1) + vc z k i * Eqn10 z k x i
        + (Eqn10 z k x 2) ^ (2 ^ (i * k)) := by
  -- Apply the Frobenius endomorphism to each term on the right-hand side.
  have h_frobenius : ∀ a b c d : R, (a + b + c + d)^(2^(i*k)) = a^(2^(i*k)) + b^(2^(i*k)) + c^(2^(i*k)) + d^(2^(i*k)) := by
    induction' i * k with n ih <;> simp_all +decide [ pow_succ, pow_mul ];
    grind;
  simp +decide [ Eqn10, h_frobenius ];
  simp +decide only [Cseq_rec, Bseq_rec, aseq_rec];
  simp +decide [ Zc, vc, pow_mul ] ; ring;
  rw [ show ( 2 ^ k - 1 : ℕ ) * 2 ^ ( i * k ) = 2 ^ ( i * k ) * 2 ^ k - 2 ^ ( i * k ) by rw [ tsub_mul, one_mul, mul_comm ] ] ; ring;
  grind

/-
**Equation (10), unfolded.**  If the base residual `Eqn10 z k x 2` vanishes
(equation (9)), then every residual `Eqn10 z k x i` vanishes.  In particular `x`
satisfies equation (10) for all `i`.
-/
theorem Eqn10_unfold (x : R) (h9 : Eqn10 z k x 2 = 0) (i : ℕ) :
    Eqn10 z k x i = 0 := by
  induction' i using Nat.twoStepInduction with i ih1 ih2;
  · simp +decide [ Eqn10, aseq, Bseq, Cseq ];
    rw [ ← two_smul R x, CharTwo.two_eq_zero, zero_smul ];
  · simp only [Eqn10, aseq_one, Bseq_one, Cseq_one, one_mul, zero_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  · rw [Eqn10_rec, ih1, ih2, h9]; ring

end CharTwoLayer

end KasamiPerm.InverseRec
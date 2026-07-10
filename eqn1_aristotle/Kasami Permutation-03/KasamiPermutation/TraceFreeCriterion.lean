import Mathlib
import KasamiPermutation.FiniteField.LinearizedBijection

/-!
# Theorem 5 (Dobbertin 1999) — the trace-free permutation criterion

This module formalises **Theorem 5** of

> Hans Dobbertin, *"Kasami Power Functions, Permutation Polynomials and Cyclic
> Difference Sets"*, in *Difference Sets, Sequences and their Correlation
> Properties*, NATO Sci. Ser. C **542**, Kluwer, 1999, pp. 133–158.

Let `L = 𝔽_{2ⁿ}`, `gcd(k, n) = 1`, `k < n`, and `k·k' ≡ 1 (mod n)`.  For a bit
`ε ∈ {0, 1}` Dobbertin defines the **trace-free generalized Kasami polynomial**
```
                 (∑_{i=1}^{k'} z^{2^{ik}}) + ε
   q^{(ε)}(z) =  ─────────────────────────────
                          z^{2^k + 1}
```
(the factor `1/z^{2^k+1}` being replaced by `z^{(2ⁿ−1)−(2^k+1)}` to obtain a
genuine polynomial on `L`, with the convention `0/0 = 0`, so `q^{(ε)}(0) = 0`).

> **Theorem 5.** `q^{(ε)}` is a permutation polynomial on `L` if and only if
> `ε ≡ k' + 1 (mod 2)`.

Dobbertin proves it by reusing the root-count argument of Theorem 1: for a fixed
value `c`, the equation `q^{(ε)}(x) = c` reduces, after adding its `2^k`-th power
to itself, to the **linearized** equation
```
   ℓ(x) = c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1 = 0,        (ℓ)
```
which has at most one solution of the original equation.

The parity condition is encoded as `ε = 1 ↔ Even k'` (which, for `ε ∈ {0,1}`, is
equivalent to `ε ≡ k' + 1 (mod 2)`).
-/

namespace KasamiPerm.TraceFree

open Finset BigOperators FiniteFieldCharTwo

/-- The **step-`2^k` partial trace** `P(x) = ∑_{j=0}^{k'-1} x^{2^{jk}}`.  This is
the length-`k'` linearized (additive) polynomial built from the Frobenius power
`x ↦ x^{2^k}`; it is the analogue of `truncTrace` for step `2^k`. -/
noncomputable def pTrace {F : Type*} [CommSemiring F] (k k' : ℕ) (x : F) : F :=
  ∑ j ∈ Finset.range k', x ^ (2 ^ (j * k))

/-- The **numerator sum** `S(x) = ∑_{i=1}^{k'} x^{2^{ik}}`.  It equals
`P(x)^{2^k}` (`sTrace_eq_pTrace`). -/
noncomputable def sTrace {F : Type*} [CommSemiring F] (k k' : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))

/-- The **trace-free generalized Kasami polynomial** `q^{(ε)}` of Theorem 5,
as a genuine function on `L = 𝔽_{2ⁿ}` (with `0/0 = 0`, so `q^{(ε)}(0) = 0`
whenever the exponent `(2ⁿ−1)−(2^k+1)` is positive). -/
noncomputable def qeps {F : Type*} [CommSemiring F] (n k k' : ℕ) (ε : F) (x : F) : F :=
  (sTrace k k' x + ε) * x ^ (2 ^ n - 1 - (2 ^ k + 1))

/-! ## Structural identities for the partial trace -/

/-- `S(x) = P(x)^{2^k}`: the numerator sum is the Frobenius-`2^k` image of the
partial trace. -/
lemma sTrace_eq_pTrace {F : Type*} [CommSemiring F] [CharP F 2] (k k' : ℕ) (x : F) :
    sTrace k k' x = (pTrace k k' x) ^ (2 ^ k) := by
  unfold sTrace pTrace
  rw [sum_pow_char_pow, ← Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by simp)
  intro i hi
  rw [← pow_mul, ← pow_add]
  ring_nf

/-- **Raw telescoping** of the partial trace: `P(x)^{2^k} + P(x) = x^{2^{k'k}} + x`
in characteristic `2`.  (No field/Fermat hypotheses needed.) -/
lemma pTrace_telescope_raw {F : Type*} [CommSemiring F] [CharP F 2] (k k' : ℕ) (x : F) :
    (pTrace k k' x) ^ (2 ^ k) + pTrace k k' x = x ^ (2 ^ (k' * k)) + x := by
  unfold pTrace
  rw [sum_pow_char_pow]
  induction k' with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have e1 : ((x ^ (2 ^ (m * k))) ^ (2 ^ k)) = x ^ (2 ^ ((m + 1) * k)) := by
      rw [← pow_mul, ← pow_add]; ring_nf
    have key : (∑ j ∈ Finset.range m, (x ^ (2 ^ (j * k))) ^ (2 ^ k)) + (x ^ (2 ^ (m * k))) ^ (2 ^ k)
        + ((∑ j ∈ Finset.range m, x ^ (2 ^ (j * k))) + x ^ (2 ^ (m * k)))
        = ((∑ j ∈ Finset.range m, (x ^ (2 ^ (j * k))) ^ (2 ^ k)) + (∑ j ∈ Finset.range m, x ^ (2 ^ (j * k))))
          + ((x ^ (2 ^ (m * k))) ^ (2 ^ k) + x ^ (2 ^ (m * k))) := by ring
    rw [key, ih, e1]
    rw [show ∀ a b c : F, a + b + (c + a) = c + b from fun a b c => by
      rw [add_comm c a, ← add_assoc, add_assoc a b a, add_comm b a, ← add_assoc,
        CharTwo.add_self_eq_zero, zero_add, add_comm]]

/-- `x^{2^{k'k}} = x^2` on `𝔽_{2ⁿ}` when `k·k' ≡ 1 (mod n)`. -/
lemma pow_frob_kk' {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ} (hkk' : k * k' % n = 1) (x : F) :
    x ^ (2 ^ (k' * k)) = x ^ 2 := by
  rw [frob_mod 2 hn x (k' * k), Nat.mul_comm k' k, hkk', pow_one]

/-- **Field telescoping** (Artin–Schreier for the step-`2^k` partial trace):
`P(x)^{2^k} + P(x) = x^2 + x` on `𝔽_{2ⁿ}` when `k·k' ≡ 1 (mod n)`. -/
lemma pTrace_telescope {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ} (hkk' : k * k' % n = 1) (x : F) :
    (pTrace k k' x) ^ (2 ^ k) + pTrace k k' x = x ^ 2 + x := by
  rw [pTrace_telescope_raw, pow_frob_kk' hn hkk']

/-- `P(1) = k'` and `S(1) = k'`. -/
lemma pTrace_one {F : Type*} [CommSemiring F] (k k' : ℕ) : pTrace k k' (1 : F) = (k' : F) := by
  unfold pTrace; simp

lemma sTrace_one {F : Type*} [CommSemiring F] (k k' : ℕ) :
    sTrace k k' (1 : F) = (k' : F) := by
  unfold sTrace; simp

/-- The nat-cast `(k' : F)` in characteristic `2` is `0` exactly when `k'` is even. -/
lemma natCast_eq_zero_iff_even {F : Type*} [Field F] [CharP F 2] (k' : ℕ) :
    (k' : F) = 0 ↔ Even k' := by
  rw [CharP.cast_eq_zero_iff F 2 k']; exact even_iff_two_dvd.symm

/-- The nat-cast `(k' : F)` in characteristic `2` is `1` when `k'` is odd. -/
lemma natCast_odd {F : Type*} [Field F] [CharP F 2] {k' : ℕ} (h : Odd k') :
    (k' : F) = 1 := by
  obtain ⟨m, rfl⟩ := h; simp [Nat.cast_add, Nat.cast_mul, CharTwo.two_eq_zero]

/-- A bit `ε ∈ {0,1}` satisfies `ε^{2^k} = ε` in characteristic `2`. -/
lemma bit_pow {F : Type*} [Field F] [CharP F 2] {ε : F} (hε : ε = 0 ∨ ε = 1) (m : ℕ) :
    ε ^ (2 ^ m) = ε := by
  have h : 2 ^ m ≠ 0 := by positivity
  rcases hε with rfl | rfl <;> simp [zero_pow h]

/-! ## The map on `0` and on units -/

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

omit [Fintype F] [CharP F 2] in
/-- `q^{(ε)}(0) = 0` when the exponent `(2ⁿ−1)−(2^k+1)` is positive. -/
lemma qeps_zero {n k k' : ℕ} (hpos : 0 < 2 ^ n - 1 - (2 ^ k + 1)) (ε : F) :
    qeps n k k' ε (0 : F) = 0 := by
  unfold qeps; rw [zero_pow hpos.ne', mul_zero]

omit [CharP F 2] in
/-- On units, `q^{(ε)}(x)·x^{2^k+1} = S(x) + ε` — the working form of the equation
`q^{(ε)}(x) = c`. -/
lemma qeps_mul_unit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k k' : ℕ)
    (hexp : 2 ^ k + 1 ≤ 2 ^ n - 1) (ε : F) {x : F} (hx : x ≠ 0) :
    qeps n k k' ε x * x ^ (2 ^ k + 1) = sTrace k k' x + ε := by
  unfold qeps
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hexp, ← hn,
    FiniteField.pow_card_sub_one_eq_one x hx, mul_one]

/-! ## The linearized equation `ℓ`

For a fixed value `c`, the equation `q^{(ε)}(x) = c` on units implies the
linearized equation `ℓ(x) = c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1 = 0`. -/

/-
**Derivation of `ℓ` (eq. (ℓ)).**  If `x ≠ 0` and `S(x) + ε = c·x^{2^k+1}`
(the equation `q^{(ε)}(x) = c`), then `c^{2^k} x^{2^{2k}} + x^{2^k} + c x + 1 = 0`.

Mechanism: `S = P^{2^k}` (`sTrace_eq_pTrace`) and `P^{2^k} + P = x² + x`
(`pTrace_telescope`), so `P = c x^{2^k+1} + x² + x + ε`.  Raising to the `2^k`
power and using `P^{2^k} = S = c x^{2^k+1} + ε` and `ε^{2^k} = ε` gives, after
dividing by `x^{2^k}`, the linearized identity.
-/
lemma ell_of_eq {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hkk' : k * k' % n = 1) {ε : F} (hε : ε = 0 ∨ ε = 1) {c x : F} (hx : x ≠ 0)
    (hex : sTrace k k' x + ε = c * x ^ (2 ^ k + 1)) :
    c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1 = 0 := by
  -- By definition of $P$ and $S$, we know that $S = P^{2^k}$ and $P^{2^k} + P = x^2 + x$.
  set P := pTrace k k' x
  set S := sTrace k k' x
  have hS : S = P ^ (2 ^ k) := by
    exact sTrace_eq_pTrace k k' x
  have hP : P ^ (2 ^ k) + P = x ^ 2 + x := pTrace_telescope hn hkk' x
  have hHex : S + ε = c * x ^ (2 ^ k + 1) := by
    exact hex;
  -- Substitute $P = (x^2 + x) + S$ into $P^{2^k} = S$ and simplify.
  have hP_sub : P = (x^2 + x) + c * x ^ (2 ^ k + 1) + ε := by
    grind +ring
  have hP_sub_pow : P ^ (2 ^ k) = S := by
    exact hS.symm
  have hP_sub_pow_simplified : S = (x^2) ^ (2 ^ k) + x ^ (2 ^ k) + (c * x ^ (2 ^ k + 1)) ^ (2 ^ k) + ε := by
    convert hP_sub_pow.symm using 1 ; rw [ hP_sub ] ; ring;
    simp +decide [ add_pow_char_pow, mul_pow, pow_mul ] ; ring;
    grind +suggestions;
  convert mul_left_cancel₀ ( pow_ne_zero ( 2 ^ k ) hx ) _ using 1 ; ring;
  convert sub_eq_zero.mpr hHex using 1 ; rw [ hP_sub_pow_simplified ] ; ring;
  grind

/-! ## The root count (heart of Theorem 5)

Dobbertin's argument: for a fixed `c`, the equation `q^{(ε)}(x) = c` has at most
one solution.  Two solutions `x, y` both satisfy `ℓ = 0`; a case analysis on
whether `c` lies in the image of `γ ↦ γ^{2^k+1} + γ` shows `x = y`. -/

/-
**Case 1 factorization.**  For `c ≠ 0` and `t ≠ 0`, the linear part
`ℓ₀(t) = c^{2^k} t^{2^{2k}} + t^{2^k} + c t` factors as
`ℓ₀(t) = c⁻¹ · (h^{2^k+1} + h + c)² · t` where `h = (c t^{2^k-1})^{2^{n-1}}`
satisfies `h² = c t^{2^k-1}` (Fermat).  Consequently, if `ℓ₀(t) = 0` with
`t ≠ 0` then `c = h^{2^k+1} + h`, i.e. `c` lies in the image of
`γ ↦ γ^{2^k+1} + γ`.
-/
lemma ell0_root_imp_image {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k : ℕ}
    (hk : 0 < k) (hkn : k < n) {c t : F} (hc : c ≠ 0) (ht : t ≠ 0)
    (h0 : c ^ (2 ^ k) * t ^ (2 ^ (2 * k)) + t ^ (2 ^ k) + c * t = 0) :
    ∃ γ : F, c = γ ^ (2 ^ k + 1) + γ := by
  -- Set `h := (c * t^(2^k-1))^(2^(n-1))` and take `γ := h`.
  set h := (c * t ^ (2 ^ k - 1)) ^ (2 ^ (n - 1)) with hh_def
  use h;
  -- By Fermat's Little Theorem, we know that $h^2 = c * t^{2^k - 1}$.
  have hh_sq : h ^ 2 = c * t ^ (2 ^ k - 1) := by
    rw [ ← pow_mul, ← pow_succ, Nat.sub_add_cancel ( by linarith ) ];
    rw [ ← hn, FiniteField.pow_card ];
  -- Substitute `h^2 = c * t^(2^k-1)` into the identity.
  have h_identity : (h ^ (2 ^ k + 1) + h + c) ^ 2 * t = c * (c ^ (2 ^ k) * t ^ (2 ^ (2 * k)) + t ^ (2 ^ k) + c * t) := by
    rw [ show 2 ^ ( 2 * k ) = 2 ^ k * 2 ^ k by ring ] ; rw [ show 2 ^ k = 2 ^ k - 1 + 1 by rw [ Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ] ; ring;
    rw [ show h ^ 4 = ( h ^ 2 ) ^ 2 by ring, show h ^ 3 = h * h ^ 2 by ring, show h ^ ( ( 2 ^ k - 1 ) * 2 ) = ( h ^ 2 ) ^ ( 2 ^ k - 1 ) by ring, hh_sq ] ; ring;
    grobner;
  grind +ring

/-
**Fact I core.**  Under the parity criterion, `S(x) + ε ≠ 0` for `x ≠ 0`.

If `S(x) + ε = 0` then `P(x)^{2^k} = ε`, so (Frobenius injective) `P(x) = ε`, and
the telescoping `P(x)^{2^k} + P(x) = x² + x` gives `x² + x = ε + ε = 0`, i.e.
`x ∈ {0,1}`.  With `x ≠ 0` we get `x = 1`, whence `S(1) = k' ≡ ε`, contradicting
the parity criterion.
-/
lemma sTrace_add_ne_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hkk' : k * k' % n = 1) {ε : F} (hε : ε = 0 ∨ ε = 1) (hcrit : ε = 1 ↔ Even k')
    {x : F} (hx : x ≠ 0) :
    sTrace k k' x + ε ≠ 0 := by
  intro h_contra
  have hP : (pTrace k k' x) ^ (2 ^ k) = ε := by
    grind +suggestions;
  have hP_eq : pTrace k k' x = ε := by
    have hP_eq : Function.Injective (fun y : F => y ^ (2 ^ k)) := by
      exact Function.Bijective.injective ( FiniteFieldCharTwo.frob_bijective 2 k );
    apply hP_eq;
    cases hε <;> simp +decide [ * ];
  have := pTrace_telescope hn hkk' x; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
  grind +suggestions

omit [Fintype F] in
/-- `S` is additive. -/
lemma sTrace_add (k k' : ℕ) (x y : F) :
    sTrace k k' (x + y) = sTrace k k' x + sTrace k k' y := by
  unfold sTrace
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => add_pow_char_pow (p := 2) (n := i * k) x y)

omit [CharP F 2] in
/-- Injectivity of `w ↦ w^{2^k-1}` on `F` (from `gcd(k,n) = 1`, so
`gcd(2^k-1, 2^n-1) = 1`). -/
lemma pow2k1_inj {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k : ℕ} (hk : 0 < k)
    (hcop : Nat.Coprime k n) : Function.Injective (fun w : F => w ^ (2 ^ k - 1)) := by
  have hgcdnk : Nat.gcd n k = 1 := by rw [Nat.gcd_comm]; exact hcop
  have hco : Nat.Coprime (Fintype.card F - 1) (2 ^ k - 1) := by
    rw [hn]; unfold Nat.Coprime; rw [Nat.pow_sub_one_gcd_pow_sub_one, hgcdnk]; norm_num
  exact (FiniteFieldCharTwo.pow_field_bijective hco
    (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega)))).injective

/-- The quadratic `Q(t) = c t^{2^k} + γ² t + γ` of the Case-2 factorization. -/
noncomputable def qPoly (γ c : F) (k : ℕ) (t : F) : F := c * t ^ (2 ^ k) + γ ^ 2 * t + γ

/-
**Driven telescoping of `S`.**  If `z^{2^k} = a^{2^k} + a + b` with `b ∈ {0,1}`,
then `S(z) = a² + a + (k':F)·b` (each term `z^{2^{ik}} = a^{2^{ik}} + a^{2^{(i-1)k}} + b`
telescopes; `a^{2^{k'k}} = a²` by `pow_frob_kk'`).
-/
lemma sTrace_telescope_gen {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hkk' : k * k' % n = 1) {a b z : F} (hb : b = 0 ∨ b = 1)
    (hstep : z ^ (2 ^ k) = a ^ (2 ^ k) + a + b) :
    sTrace k k' z = a ^ 2 + a + (k' : F) * b := by
  -- By induction on $m$, we show that $sTrace k m z = a^{2^{mk}} + a + b \cdot m$.
  have h_ind : ∀ m : ℕ, sTrace k m z = a ^ (2 ^ (m * k)) + a + b * m := by
    intro m
    induction' m with m ih;
    · simp +decide [ sTrace ] ; ring;
      rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;
    · convert congr_arg ( · + z ^ ( 2 ^ ( ( m + 1 ) * k ) ) ) ih using 1;
      · unfold sTrace; simp +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
      · rw [ show z ^ 2 ^ ( ( m + 1 ) * k ) = ( z ^ 2 ^ k ) ^ 2 ^ ( m * k ) by ring, hstep ] ; ring;
        rw [ add_pow_char_pow, add_pow_char_pow ] ; ring;
        cases hb <;> simp +decide [ *, pow_mul' ] ; ring;
        · exact Or.inr ( CharP.cast_eq_zero F 2 );
        · rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;
  rw [ h_ind, mul_comm ];
  rw [ mul_comm, pow_frob_kk' hn hkk' a ] ; ring

/-
**Case-2 factorization** `ℓ(t) = Q(t)^{2^k} + Γ·Q(t)` with `Γ = γ^{2^k-1} + γ⁻¹`,
given `c = γ^{2^k+1} + γ` and `γ ≠ 0`.
-/
omit [Fintype F] in
lemma Q_factor {k : ℕ} {γ c : F} (hγ : γ ≠ 0)
    (hcdef : c = γ ^ (2 ^ k + 1) + γ) (t : F) :
    c ^ (2 ^ k) * t ^ (2 ^ (2 * k)) + t ^ (2 ^ k) + c * t + 1
      = (qPoly γ c k t) ^ (2 ^ k) + (γ ^ (2 ^ k - 1) + γ⁻¹) * (qPoly γ c k t) := by
  unfold qPoly; simp +decide [ *, pow_add, pow_mul' ] ; ring;
  simp +decide [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ; ring;
  simp +decide [ add_pow_char_pow, mul_assoc, mul_comm, mul_left_comm, hγ ] ; ring;
  rw [ show γ ^ 2 = γ * γ by ring, show γ ^ ( 2 ^ k ) = γ * γ ^ ( 2 ^ k - 1 ) by rw [ ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ] ; ring;
  grind +splitImp

/-
If `Q(t) = 0` (with `γ ≠ 0`, `c = γ^{2^k+1}+γ`) then the Artin–Schreier step
`t^{2^k} = (γ t)^{2^k} + γ t + 1` holds.
-/
omit [Fintype F] in
lemma qPoly_zero_step {k : ℕ} {γ c t : F} (hγ : γ ≠ 0)
    (hcdef : c = γ ^ (2 ^ k + 1) + γ) (hQ0 : qPoly γ c k t = 0) :
    t ^ (2 ^ k) = (γ * t) ^ (2 ^ k) + γ * t + 1 := by
  unfold qPoly at hQ0;
  simp_all +decide [ mul_pow, pow_add ];
  grind +ring

/-
**Sub-claim A.**  Under the parity criterion, a nonzero solution `t` of the
equation (`ε_t = c t^{2^k+1} + S(t) + ε = 0`) has `Q(t) ≠ 0`.

If `Q(t) = 0` the step lemma gives `t^{2^k} = (γt)^{2^k} + γt + 1`, so by the driven
telescoping `S(t) = (γt)² + γt + (k':F)`, and `c t^{2^k+1} = (γt)² + γt` (from
`c t^{2^k} = γ² t + γ`).  Hence `c t^{2^k+1} + S(t) + ε = (k':F) + ε = 1` (parity),
contradicting `ε_t = 0`.
-/
lemma sol_qPoly_ne_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hkk' : k * k' % n = 1) {ε : F} (hcrit : ε = 1 ↔ Even k')
    {γ c t : F} (hγ : γ ≠ 0) (hcdef : c = γ ^ (2 ^ k + 1) + γ)
    (hεt : c * t ^ (2 ^ k + 1) + sTrace k k' t + ε = 0) :
    qPoly γ c k t ≠ 0 := by
  contrapose! hεt; simp_all +decide [ qPoly ] ;
  have hstep : t ^ (2 ^ k) = (γ * t) ^ (2 ^ k) + γ * t + 1 := by
    have hstep : qPoly γ c k t = 0 := by
      unfold qPoly; aesop;
    generalize_proofs at *; (
    convert qPoly_zero_step hγ hcdef hstep using 1)
  have hSt : sTrace k k' t = (γ * t) ^ 2 + (γ * t) + (k' : F) * 1 := by
    convert sTrace_telescope_gen hn hkk' ( Or.inr rfl ) hstep using 1
  have hct : (γ ^ (2 ^ k + 1) + γ) * t ^ (2 ^ k + 1) = (γ * t) ^ 2 + (γ * t) := by
    grind +qlia
  simp_all +decide [ pow_succ, mul_assoc ] ;
  by_cases heven : Even k' <;> simp_all +decide [ ← add_assoc ];
  · obtain ⟨ k', rfl ⟩ := even_iff_two_dvd.mp heven; simp_all +decide ;
    grind;
  · obtain ⟨ m, rfl ⟩ := heven; simp_all +decide [ mul_left_comm ] ;
    grind +qlia

/-
**The root count, Case 2** (`c` lies in the image of `γ ↦ γ^{2^k+1} + γ`).

This is the delicate case of Dobbertin's Theorem-1 root count: writing
`c = γ^{2^k+1} + γ`, the linearized `ℓ` factors through the quadratic
`Q(t) = c t^{2^k} + γ² t + γ`, its four roots split into `Q = 0` (which never
solve the original equation) and `Q = Δ⁻¹` (two roots summing to `Δ`, of which
exactly one solves it — this is where the parity criterion `ε ≡ k'+1` is used).
-/
lemma root_count_image {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hk : 0 < k) (hcop : Nat.Coprime k n) (hkk' : k * k' % n = 1)
    {ε : F} (hε : ε = 0 ∨ ε = 1) (hcrit : ε = 1 ↔ Even k')
    {c x y : F} (hc : c ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hex : sTrace k k' x + ε = c * x ^ (2 ^ k + 1))
    (hey : sTrace k k' y + ε = c * y ^ (2 ^ k + 1))
    (hg : ∃ γ : F, c = γ ^ (2 ^ k + 1) + γ) :
    x = y := by
  obtain ⟨γ, hcdef⟩ := hg
  have hγ0 : γ ≠ 0 := by
    grind +splitImp
  have hΓγ : (γ^(2^k-1)+γ⁻¹) * γ^2 = c := by
    have e : γ ^ (2^k-1) * γ^2 = γ ^ (2^k+1) := by
      rw [← pow_add]; congr 1; have := Nat.one_le_two_pow (n := k); omega
    have hiv : γ⁻¹ * γ^2 = γ := by field_simp
    rw [add_mul, e, hiv, hcdef]
  have hQx : qPoly γ c k x ≠ 0 := by
    apply sol_qPoly_ne_zero hn hkk' hcrit hγ0 hcdef;
    grind +splitIndPred
  have hQy : qPoly γ c k y ≠ 0 := by
    apply sol_qPoly_ne_zero hn hkk' hcrit hγ0 hcdef;
    grind +suggestions
  have hQeq : qPoly γ c k x = qPoly γ c k y := by
    have hΓx : qPoly γ c k x ^ (2 ^ k - 1) = γ ^ (2 ^ k - 1) + γ⁻¹ := by
      have hΓx : qPoly γ c k x ^ (2 ^ k) + (γ ^ (2 ^ k - 1) + γ⁻¹) * qPoly γ c k x = 0 := by
        have hΓx : c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1 = 0 := by
          apply ell_of_eq hn hkk' hε hx hex;
        rw [ ← hΓx, Q_factor hγ0 hcdef ];
      rw [ show qPoly γ c k x ^ 2 ^ k = qPoly γ c k x ^ ( 2 ^ k - 1 ) * qPoly γ c k x by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ] at hΓx;
      grind +suggestions
    have hΓy : qPoly γ c k y ^ (2 ^ k - 1) = γ ^ (2 ^ k - 1) + γ⁻¹ := by
      have hΓy : qPoly γ c k y ^ (2 ^ k) + (γ ^ (2 ^ k - 1) + γ⁻¹) * qPoly γ c k y = 0 := by
        have hΓy : c ^ (2 ^ k) * y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + c * y + 1 = 0 := by
          apply ell_of_eq hn hkk' hε hy hey;
        rw [ ← hΓy, Q_factor hγ0 hcdef ];
      rw [ show qPoly γ c k y ^ 2 ^ k = qPoly γ c k y ^ ( 2 ^ k - 1 ) * qPoly γ c k y by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ] at hΓy;
      grind +suggestions;
    have := pow2k1_inj hn hk hcop;
    exact this ( hΓx.trans hΓy.symm );
  -- Set `d := x + y ≠ 0` (in char 2, `x+y=0 → x=y`).
  set d := x + y with hd
  by_cases hd0 : d = 0;
  · grind +splitIndPred;
  · -- Step for `d`: `hstepd : d^(2^k) = (γ*d)^(2^k) + γ*d + 0`.
    have hstepd : d ^ (2 ^ k) = (γ * d) ^ (2 ^ k) + γ * d + 0 := by
      have hker : c * d ^ (2 ^ k) + γ ^ 2 * d = 0 := by
        unfold qPoly at hQeq; simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ] ;
        simp_all +decide [ add_pow_char_pow, mul_add, add_mul, mul_comm, mul_left_comm ];
        grind +ring;
      rw [ mul_pow, mul_comm ];
      grind;
    have hSd := sTrace_telescope_gen hn hkk' (Or.inl rfl) hstepd
    have hSadd := sTrace_add k k' x y
    simp_all +decide [ qPoly ];
    grind +suggestions

/-- **The root count** (`q^{(ε)}(x) = q^{(ε)}(y) = c` on units forces `x = y`).
This is the injectivity of `q^{(ε)}` on `L*`, and the crux of Theorem 5.

Both `x, y` satisfy the linearized `ℓ = 0` (`ell_of_eq`).  If `c` is **not** in the
image of `γ ↦ γ^{2^k+1} + γ`, then `ℓ₀` (the linear part) is injective
(`ell0_root_imp_image` contrapositive) and additivity forces `x = y`.  Otherwise
we are in Case 2 (`root_count_image`). -/
lemma root_count {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * k' % n = 1)
    {ε : F} (hε : ε = 0 ∨ ε = 1) (hcrit : ε = 1 ↔ Even k')
    {c x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hex : sTrace k k' x + ε = c * x ^ (2 ^ k + 1))
    (hey : sTrace k k' y + ε = c * y ^ (2 ^ k + 1)) :
    x = y := by
  have hc : c ≠ 0 := by
    intro hc0
    exact sTrace_add_ne_zero hn hkk' hε hcrit hx (by rw [hex, hc0, zero_mul])
  have hlx := ell_of_eq hn hkk' hε hx hex
  have hly := ell_of_eq hn hkk' hε hy hey
  by_cases hg : ∃ γ : F, c = γ ^ (2 ^ k + 1) + γ
  · exact root_count_image hn hk hcop hkk' hε hcrit hc hx hy hex hey hg
  · by_contra hxy
    have hd : x + y ≠ 0 := by
      intro h
      apply hxy
      have := add_eq_zero_iff_eq_neg.mp h
      rwa [CharTwo.neg_eq] at this
    have hlx' : c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x = 1 := by
      have := eq_neg_of_add_eq_zero_left hlx; rwa [CharTwo.neg_eq] at this
    have hly' : c ^ (2 ^ k) * y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + c * y = 1 := by
      have := eq_neg_of_add_eq_zero_left hly; rwa [CharTwo.neg_eq] at this
    have hl0 : c ^ (2 ^ k) * (x + y) ^ (2 ^ (2 * k)) + (x + y) ^ (2 ^ k) + c * (x + y) = 0 := by
      have ex2 : (x + y) ^ (2 ^ (2 * k)) = x ^ (2 ^ (2 * k)) + y ^ (2 ^ (2 * k)) :=
        add_pow_char_pow (p := 2) (n := 2 * k) x y
      have ex1 : (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) :=
        add_pow_char_pow (p := 2) (n := k) x y
      rw [ex2, ex1]
      have hsplit : c ^ (2 ^ k) * (x ^ (2 ^ (2 * k)) + y ^ (2 ^ (2 * k)))
            + (x ^ (2 ^ k) + y ^ (2 ^ k)) + c * (x + y)
          = (c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x)
            + (c ^ (2 ^ k) * y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + c * y) := by ring
      rw [hsplit, hlx', hly']
      exact CharTwo.add_self_eq_zero 1
    obtain ⟨γ, hγ⟩ := ell0_root_imp_image hn hk hkn hc hd hl0
    exact hg ⟨γ, hγ⟩

/-! ## `q^{(ε)}` sends nonzero to nonzero (no extra zero) -/

/-
**Fact I.**  Under the parity criterion, `q^{(ε)}(x) ≠ 0` for `x ≠ 0`.

If `S(x) + ε = 0` then `P(x)^{2^k} = ε`, so (Frobenius injective) `P(x) = ε`, and
the telescoping `P(x)^{2^k} + P(x) = x² + x` gives `x² + x = ε + ε = 0`, i.e.
`x ∈ {0,1}`.  With `x ≠ 0` we get `x = 1`, whence `S(1) = k' ≡ ε`, contradicting
the parity criterion.
-/
lemma qeps_ne_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hkk' : k * k' % n = 1) {ε : F} (hε : ε = 0 ∨ ε = 1) (hcrit : ε = 1 ↔ Even k')
    {x : F} (hx : x ≠ 0) :
    qeps n k k' ε x ≠ 0 := by
  unfold qeps
  exact mul_ne_zero (sTrace_add_ne_zero hn hkk' hε hcrit hx) (pow_ne_zero _ hx)

/-! ## Theorem 5 -/

/-- **Theorem 5 (Dobbertin 1999) — the trace-free permutation criterion.**

Let `F = 𝔽_{2ⁿ}`, `gcd(k, n) = 1`, `k < n`, `k·k' ≡ 1 (mod n)`, and let
`ε ∈ {0,1}`.  Then the trace-free generalized Kasami polynomial `q^{(ε)}` is a
permutation of `F` **iff** `ε ≡ k' + 1 (mod 2)` (encoded as `ε = 1 ↔ Even k'`).

The non-degeneracy hypothesis `2^k + 1 < 2^n - 1` makes `1/z^{2^k+1}` a genuine
inverse power (so `q^{(ε)}(0) = 0`); it holds for all `k < n` except the marginal
`n = 2, k = 1` case over `𝔽₄`. -/
theorem qeps_bijective_iff {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k k' : ℕ}
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * k' % n = 1)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) {ε : F} (hε : ε = 0 ∨ ε = 1) :
    Function.Bijective (qeps n k k' ε) ↔ (ε = 1 ↔ Even k') := by
  have hexp' : 2 ^ k + 1 ≤ 2 ^ n - 1 := le_of_lt hexp
  have hpos : 0 < 2 ^ n - 1 - (2 ^ k + 1) := Nat.sub_pos_of_lt hexp
  constructor
  · -- only if: bijective ⟹ criterion.  Contrapose: ¬criterion ⟹ q(0) = q(1) = 0.
    intro hbij
    by_contra hcrit
    have h0 : qeps n k k' ε (0 : F) = 0 := qeps_zero hpos ε
    have h1 : qeps n k k' ε (1 : F) = (k' : F) + ε := by
      unfold qeps; rw [sTrace_one, one_pow, mul_one]
    have hzero : (k' : F) + ε = 0 := by
      rcases hε with rfl | rfl
      · have heven : Even k' := by
          have h01 : ¬ ((0 : F) = 1) := zero_ne_one
          tauto
        rw [add_zero, (natCast_eq_zero_iff_even k').2 heven]
      · have hodd : Odd k' := by
          have hne : ¬ Even k' := fun hev => hcrit ⟨fun _ => hev, fun _ => rfl⟩
          exact Nat.not_even_iff_odd.1 hne
        rw [natCast_odd hodd]; exact CharTwo.add_self_eq_zero 1
    exact one_ne_zero (hbij.injective (by rw [h1, h0, hzero]))
  · -- if: criterion ⟹ bijective (injective on a finite type).
    intro hcrit
    refine ⟨?_, ?_⟩
    · intro x y hxy
      by_cases hx : x = 0 <;> by_cases hy : y = 0
      · rw [hx, hy]
      · exfalso; rw [hx, qeps_zero hpos] at hxy
        exact qeps_ne_zero hn hkk' hε hcrit hy hxy.symm
      · exfalso; rw [hy, qeps_zero hpos] at hxy
        exact qeps_ne_zero hn hkk' hε hcrit hx hxy
      · -- both nonzero: root count
        have hex := qeps_mul_unit hn k k' hexp' ε hx
        have hey := qeps_mul_unit hn k k' hexp' ε hy
        rw [hxy] at hex
        exact root_count hn hk hkn hcop hkk' hε hcrit hx hy (by rw [← hex]) (by rw [← hey])
    · exact (Finite.injective_iff_surjective).mp (by
        intro x y hxy
        by_cases hx : x = 0 <;> by_cases hy : y = 0
        · rw [hx, hy]
        · exfalso; rw [hx, qeps_zero hpos] at hxy
          exact qeps_ne_zero hn hkk' hε hcrit hy hxy.symm
        · exfalso; rw [hy, qeps_zero hpos] at hxy
          exact qeps_ne_zero hn hkk' hε hcrit hx hxy
        · have hex := qeps_mul_unit hn k k' hexp' ε hx
          have hey := qeps_mul_unit hn k k' hexp' ε hy
          rw [hxy] at hex
          exact root_count hn hk hkn hcop hkk' hε hcrit hx hy (by rw [← hex]) (by rw [← hey]))

end KasamiPerm.TraceFree
import Mathlib
import RequestProject.AutBase

/-!
# Foundational Layer F1: Frobenius Operator Algebra

A systematic theory of the Frobenius endomorphism and its interaction
with linearized polynomials over finite fields.

**Motivation.** Many `sorry`s in the Dempwolff–Müller formalization reduce to
"obvious" Frobenius identities that are tedious to prove one at a time.
This layer provides reusable tools that collapse entire classes of such identities.

## Main results

1. **Frobenius cycling** (`frob_cycle`): `x^{p^n} = x` on `GF(p^n)`.
2. **Frobenius periodicity** (`frob_periodic`): `x^{p^{n+k}} = x^{p^k}`.
3. **Linearized polynomial under Frobenius** (`linpoly_frob_output`):
   `L(x)^{p^s} = ∑ aᵢ^{p^s} x^{p^{i+s}}`.
4. **Linearized polynomial of Frobenius** (`linpoly_frob_input`):
   `L(x^{p^s}) = ∑ aᵢ x^{p^{s+i}}`.
5. **Frobenius composition preserves bijection** (`frob_comp_bijective_right`).
6. **Key transfer** (`linpoly_mul_pow_frob_bijective`):
   `L(x)·x^k` bijective ⟹ `L(x)^{p^s}·x^{k·p^s}` bijective.
7. **Exponent reduction** (`pow_eq_pow_of_mod_eq`):
   `a ≡ b (mod |F|−1) ⟹ x^a = x^b` for `x ≠ 0`.

These lemmas are the "engine" behind trace/norm identities, adjoint
computations, and Frobenius-composition arguments throughout Sections 3–6.
-/

namespace DempwolffMueller

open Finset BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

-- ═══════════════════════════════════════════
-- Layer F1.1 : Frobenius cycling on finite fields
-- ═══════════════════════════════════════════

/-- **Frobenius cycling.** Every element of `GF(p^n)` satisfies `x^{|F|} = x`.
    This is the finite field identity (Fermat–Euler). -/
lemma frob_cycle (x : F) : x ^ Fintype.card F = x :=
  FiniteField.pow_card x

/-- **Frobenius periodicity.** `x^{p^{n+k}} = x^{p^k}` on `GF(p^n)`.
    Since `x^{p^n} = x`, raising to the `p^n`-th power is the identity. -/
lemma frob_periodic {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (k : ℕ) :
    x ^ (p ^ (n + k)) = x ^ (p ^ k) := by
  rw [pow_add, pow_mul, ← hn, frob_cycle]

/-- **Frobenius mod n.** On `GF(p^n)`, the Frobenius `x ↦ x^{p^r}` depends
    only on `r mod n`: `x^{p^r} = x^{p^{r mod n}}`. -/
lemma frob_mod {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (r : ℕ) :
    x ^ (p ^ r) = x ^ (p ^ (r % n)) := by
  have hcycle : ∀ y : F, y ^ (p ^ n) = y := by
    intro y; rw [← hn]; exact FiniteField.pow_card y
  have hmul : ∀ k : ℕ, x ^ (p ^ (n * k)) = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, hcycle, ih]
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
                   pow_add, pow_mul, hmul]

-- ═══════════════════════════════════════════
-- Layer F1.2 : Frobenius as a ring homomorphism
-- ═══════════════════════════════════════════

/-- **Product Frobenius.** `(a · b)^{p^r} = a^{p^r} · b^{p^r}`. -/
lemma mul_frob_eq (a b : F) (r : ℕ) :
    (a * b) ^ (p ^ r) = a ^ (p ^ r) * b ^ (p ^ r) :=
  mul_pow a b (p ^ r)

/-- **Sum Frobenius.** `(a + b)^{p^r} = a^{p^r} + b^{p^r}` in characteristic `p`. -/
lemma add_frob_eq (a b : F) (r : ℕ) :
    (a + b) ^ (p ^ r) = a ^ (p ^ r) + b ^ (p ^ r) :=
  add_pow_char_pow (p := p) (n := r) a b

/-- **Finset sum Frobenius.** `(∑ fᵢ)^{p^r} = ∑ fᵢ^{p^r}` in characteristic `p`.
    This is the key identity for distributing Frobenius over linearized polynomials. -/
lemma finset_sum_frob_eq {ι : Type*} (s : Finset ι) (f : ι → F) (r : ℕ) :
    (∑ i ∈ s, f i) ^ (p ^ r) = ∑ i ∈ s, (f i) ^ (p ^ r) := by
  simp_rw [← show ∀ x : F, (iterateFrobenius F p r) x = x ^ (p ^ r) from
    fun x => by simp [iterateFrobenius]]
  rw [← map_sum]

/-- **Negation Frobenius.** `(-a)^{p^r} = -(a^{p^r})`. -/
lemma neg_frob_eq (a : F) (r : ℕ) :
    (-a) ^ (p ^ r) = -(a ^ (p ^ r)) := by
  have : (iterateFrobenius F p r) (-a) = -(iterateFrobenius F p r a) :=
    map_neg _ _
  simp only [iterateFrobenius] at this
  exact this

-- ═══════════════════════════════════════════
-- Layer F1.3 : Frobenius on linearized polynomials (output)
-- ═══════════════════════════════════════════

/-- **Frobenius on linearized polynomial output.**
    If `L(x) = ∑ aᵢ x^{p^i}`, then `L(x)^{p^s} = ∑ aᵢ^{p^s} x^{p^{i+s}}`.
    The coefficients get Frobenius-shifted.

    This is the key identity behind `L*(x) = L(x)^{2^{n-m+1}}` in Thm32Kprime. -/
lemma linpoly_frob_output (n : ℕ) (coeffs : Fin n → F) (x : F) (s : ℕ) :
    (additivePolyEval p n coeffs x) ^ (p ^ s) =
    ∑ i : Fin n, (coeffs i) ^ (p ^ s) * x ^ (p ^ ((i : ℕ) + s)) := by
  rw [additivePolyEval, finset_sum_frob_eq]
  congr 1; ext i
  rw [mul_frob_eq, ← pow_mul, ← pow_add]

/-- **Frobenius on truncated trace output.**
    When `L(x) = ∑_{i=0}^{m-1} x^{p^i}` (all coefficients 1),
    `L(x)^{p^s} = ∑_{i=0}^{m-1} x^{p^{i+s}}` since `1^{p^s} = 1`. -/
lemma truncTrace_frob_output_general (m : ℕ) (x : F) (s : ℕ) :
    (∑ i ∈ Finset.range m, x ^ (p ^ i)) ^ (p ^ s) =
    ∑ i ∈ Finset.range m, x ^ (p ^ (i + s)) := by
  have hpp := Nat.pos_of_ne_zero (pow_ne_zero s hp.out.ne_zero)
  induction m with
  | zero => simp [zero_pow hpp.ne']
  | succ m ih =>
    rw [Finset.sum_range_succ, add_pow_char_pow (p := p) (n := s), ih,
        Finset.sum_range_succ, ← pow_mul, ← pow_add]

-- ═══════════════════════════════════════════
-- Layer F1.4 : Frobenius on linearized polynomials (input)
-- ═══════════════════════════════════════════

/-- **Frobenius on linearized polynomial input.**
    `L(x^{p^s}) = ∑ aᵢ x^{p^{s+i}}`. The indices shift by `s`. -/
lemma linpoly_frob_input (n : ℕ) (coeffs : Fin n → F) (x : F) (s : ℕ) :
    additivePolyEval p n coeffs (x ^ (p ^ s)) =
    ∑ i : Fin n, coeffs i * x ^ (p ^ (s + (i : ℕ))) := by
  simp only [additivePolyEval, ← pow_mul, ← pow_add]

/-- **Commutativity of Frobenius on linearized polynomials.**
    `L(x^{p^s}) = L(x)^{p^s}` when all coefficients are Frobenius-stable
    (`aᵢ^{p^s} = aᵢ`), e.g., when `aᵢ ∈ GF(p)`.

    This is the abstract version of `truncTrace_frob_comm`. -/
lemma linpoly_frob_comm (n : ℕ) (coeffs : Fin n → F) (x : F) (s : ℕ)
    (hcoeffs : ∀ i : Fin n, (coeffs i) ^ (p ^ s) = coeffs i) :
    additivePolyEval p n coeffs (x ^ (p ^ s)) =
    (additivePolyEval p n coeffs x) ^ (p ^ s) := by
  rw [linpoly_frob_input, linpoly_frob_output]
  congr 1; ext i; rw [hcoeffs, add_comm]

-- ═══════════════════════════════════════════
-- Layer F1.5 : Frobenius preserves bijection
-- ═══════════════════════════════════════════

/-- **Frobenius is bijective** on any finite field. -/
lemma frob_bijective (r : ℕ) :
    Function.Bijective (fun x : F => x ^ (p ^ r)) :=
  ⟨iterateFrobenius_inj F p r,
   (Finite.injective_iff_surjective).mp (iterateFrobenius_inj F p r)⟩

/-- **Frobenius composition preserves bijection (right).**
    If `f` is bijective, then `x ↦ (f x)^{p^r}` is bijective. -/
lemma frob_comp_bijective_right {f : F → F} (hf : Function.Bijective f) (r : ℕ) :
    Function.Bijective (fun x : F => (f x) ^ (p ^ r)) :=
  (frob_bijective p r).comp hf

/-- **Frobenius composition preserves bijection (left).**
    If `f` is bijective, then `x ↦ f(x^{p^r})` is bijective. -/
lemma frob_comp_bijective_left {f : F → F} (hf : Function.Bijective f) (r : ℕ) :
    Function.Bijective (fun x : F => f (x ^ (p ^ r))) :=
  hf.comp (frob_bijective p r)

-- ═══════════════════════════════════════════
-- Layer F1.6 : The key Frobenius-bijection transfer
-- ═══════════════════════════════════════════

/-- **Frobenius on a product with a linearized polynomial.**
    `(L(x) · x^k)^{p^s} = L(x)^{p^s} · x^{k · p^s}`. -/
lemma linpoly_mul_pow_frob (n : ℕ) (coeffs : Fin n → F) (k : ℕ)
    (x : F) (s : ℕ) :
    (additivePolyEval p n coeffs x * x ^ k) ^ (p ^ s) =
    (additivePolyEval p n coeffs x) ^ (p ^ s) * x ^ (k * p ^ s) := by
  rw [mul_pow, ← pow_mul]

/-- **The key Frobenius-bijection transfer.**
    If `x ↦ L(x) · x^k` is bijective on `F`, then
    `x ↦ L(x)^{p^s} · x^{k · p^s}` is bijective on `F`.

    This is the abstract engine behind sorry E1 in Thm32Kprime:
    from `L(x)·x^k` bijective, derive `L*(x)·x^{k·2^{n-m+1}}` bijective. -/
lemma linpoly_mul_pow_frob_bijective (n : ℕ) (coeffs : Fin n → F) (k : ℕ)
    (hbij : Function.Bijective (fun x : F => additivePolyEval p n coeffs x * x ^ k))
    (s : ℕ) :
    Function.Bijective (fun x : F =>
      (additivePolyEval p n coeffs x) ^ (p ^ s) * x ^ (k * p ^ s)) := by
  have : Function.Bijective (fun x : F =>
      (additivePolyEval p n coeffs x * x ^ k) ^ (p ^ s)) :=
    frob_comp_bijective_right p hbij s
  convert this using 1
  ext x; exact (linpoly_mul_pow_frob p n coeffs k x s).symm

-- ═══════════════════════════════════════════
-- Layer F1.7 : GF(p) coefficient stability
-- ═══════════════════════════════════════════

/-- **GF(p)-coefficients are Frobenius-stable.**
    If `c ∈ GF(p)` (i.e., `c^p = c`), then `c^{p^r} = c` for all `r`. -/
lemma gfp_frob_stable {c : F} (hc : c ^ p = c) (r : ℕ) :
    c ^ (p ^ r) = c := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, pow_mul, ih, hc]

/-- **All-ones coefficients are Frobenius-stable.**
    `1^{p^r} = 1`, which applies to the truncated trace. -/
lemma one_frob_stable (r : ℕ) : (1 : F) ^ (p ^ r) = 1 :=
  one_pow _

-- ═══════════════════════════════════════════
-- Layer F1.8 : Fermat's little theorem for power maps
-- ═══════════════════════════════════════════

/-- **Fermat's little theorem (unit form).**
    For `x ≠ 0` in `GF(p^n)`, `x^{|F|−1} = 1`. -/
lemma pow_card_sub_one_eq_one' {x : F} (hx : x ≠ 0) :
    x ^ (Fintype.card F - 1) = 1 :=
  FiniteField.pow_card_sub_one_eq_one x hx

/-- **Exponent reduction on units.**
    For `x ≠ 0`, `x^a = x^{a mod (|F|−1)}`. -/
lemma pow_mod_card_sub_one {x : F} (hx : x ≠ 0) (a : ℕ) :
    x ^ a = x ^ (a % (Fintype.card F - 1)) := by
  have hord : orderOf x ∣ Fintype.card F - 1 :=
    orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx)
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x (a % (Fintype.card F - 1))]
  congr 1; exact (Nat.mod_mod_of_dvd a hord).symm

/-- **Congruent exponents give equal powers on units.**
    If `a ≡ b (mod |F|−1)` and `x ≠ 0`, then `x^a = x^b`. -/
lemma pow_eq_pow_of_mod_eq {x : F} (hx : x ≠ 0) {a b : ℕ}
    (hab : a % (Fintype.card F - 1) = b % (Fintype.card F - 1)) :
    x ^ a = x ^ b := by
  have hord : orderOf x ∣ Fintype.card F - 1 :=
    orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx)
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x b]; congr 1
  rw [show a % orderOf x = a % (Fintype.card F - 1) % orderOf x from
        (Nat.mod_mod_of_dvd a hord).symm,
      show b % orderOf x = b % (Fintype.card F - 1) % orderOf x from
        (Nat.mod_mod_of_dvd b hord).symm,
      hab]

end DempwolffMueller

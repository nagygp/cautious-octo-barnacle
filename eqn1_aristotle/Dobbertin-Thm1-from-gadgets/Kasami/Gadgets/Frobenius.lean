import Mathlib

/-!
# Gadget F — the Frobenius (doubling) block

The first primitive LEGO brick of the Kasami/Dobbertin development: the
**Frobenius endomorphism** `φ : x ↦ x²` of a characteristic-two finite field,
together with its iterates `φ^r : x ↦ x^{2^r}` ("doubling on exponents").

Everything a downstream module needs from this brick:

* `frobenius`      — the map `x ↦ x²` packaged as `φ`;
* `frobeniusPow`   — its `r`-fold iterate `x ↦ x^{2^r}` (the "doubling" map);
* `frobeniusPow_bijective` — every iterate is a permutation of the field;
* `frob_cycle`, `frobeniusPow_periodic` — the closing/cycling laws that make the
  iterate depend only on `r mod n` when `|F| = 2ⁿ` (this is the arithmetic that
  cyclotomic-coset bookkeeping — gadget C — turns into orbit combinatorics).

The block is stated for a general prime `p` where that costs nothing, and
specialised to `p = 2` (the characteristic of interest) by the `doubling`
abbreviations at the end.  It depends only on `Mathlib`, so it is reusable and
upstreamable on its own.
-/

namespace Kasami.Gadgets

open Finset

section GeneralPrime

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p]

/-- The **Frobenius endomorphism** `φ : x ↦ x^p`, the inserted map of the trace
loop.  For `p = 2` this is the squaring (doubling) map. -/
def frobenius (x : F) : F := x ^ p

/-- The `r`-fold iterate of Frobenius, `φ^r : x ↦ x^{p^r}` — "doubling on the
exponent" `r` times. -/
def frobeniusPow (r : ℕ) (x : F) : F := x ^ (p ^ r)

omit [Fintype F] hp [CharP F p] in
@[simp] lemma frobeniusPow_zero (x : F) : frobeniusPow p 0 x = x := by
  simp [frobeniusPow]

omit [Fintype F] hp [CharP F p] in
@[simp] lemma frobeniusPow_one (x : F) : frobeniusPow p 1 x = frobenius p x := by
  simp [frobeniusPow, frobenius]

/-- **Closing law (Fermat).**  Raising to the `|F|`-th power is the identity —
the loop of length `n = log_p |F|` returns to its start. -/
lemma frob_cycle (x : F) : x ^ Fintype.card F = x := FiniteField.pow_card x

omit hp [CharP F p] in
/-- **Cycling / periodicity.**  When `|F| = pⁿ`, `φ^r` depends only on `r mod n`:
the exponent lives in the cyclotomic cosets of `×p mod (pⁿ−1)`. -/
lemma frobeniusPow_periodic {n : ℕ} (hn : Fintype.card F = p ^ n) (x : F) (r : ℕ) :
    frobeniusPow p r x = frobeniusPow p (r % n) x := by
  show x ^ (p ^ r) = x ^ (p ^ (r % n))
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
    pow_add, pow_mul]
  have : ∀ k : ℕ, x ^ (p ^ (n * k)) = x := by
    intro k; induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ← hn, frob_cycle, ih]
  rw [this]

/-- **F preserves bijectivity.**  Every Frobenius iterate is a permutation of the
field. -/
lemma frobeniusPow_bijective (r : ℕ) : Function.Bijective (frobeniusPow (F := F) p r) :=
  ⟨iterateFrobenius_inj F p r,
   (Finite.injective_iff_surjective).mp (iterateFrobenius_inj F p r)⟩

/-- Frobenius is a permutation of the field. -/
lemma frobenius_bijective : Function.Bijective (frobenius (F := F) p) := by
  simpa [frobenius, frobeniusPow] using frobeniusPow_bijective (F := F) p 1

/-- Post-composing any bijection with a Frobenius iterate stays a bijection. -/
lemma frobeniusPow_comp_bijective {f : F → F} (hf : Function.Bijective f) (r : ℕ) :
    Function.Bijective (fun x : F => frobeniusPow (F := F) p r (f x)) :=
  (frobeniusPow_bijective (F := F) p r).comp hf

end GeneralPrime

/-! ## The characteristic-two specialisation (the doubling map) -/

section CharTwo

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The **doubling map** `x ↦ x²`, i.e. Frobenius in characteristic two. -/
abbrev doubling : F → F := frobenius (F := F) 2

/-- The `r`-fold doubling `x ↦ x^{2^r}`. -/
abbrev doublingPow (r : ℕ) : F → F := frobeniusPow (F := F) 2 r

lemma doublingPow_bijective (r : ℕ) : Function.Bijective (doublingPow (F := F) r) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  frobeniusPow_bijective 2 r

omit [CharP F 2] in
lemma doublingPow_periodic {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) (r : ℕ) :
    doublingPow (F := F) r x = doublingPow (F := F) (r % n) x :=
  frobeniusPow_periodic 2 hn x r

end CharTwo

end Kasami.Gadgets

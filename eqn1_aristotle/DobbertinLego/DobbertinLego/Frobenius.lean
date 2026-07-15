import Mathlib

/-!
# Gadget **F** — the Frobenius brick

The first of the two LEGO bricks from which the whole step `(1) ⟹ (2)` of
Dobbertin's Theorem 1 is assembled.

Over `F = 𝔽_{2ⁿ}` the Frobenius map is `x ↦ x²`; its `r`-fold iterate is the
"doubling on the exponent"

```
   frob r x = x^{2^r}.
```

Everything downstream is expressed through this one map.  Its laws are the whole
finite-field vocabulary the development needs:

* `frob_add`      — additivity (the char-2 freshman's dream);
* `frob_comp`     — iterates compose: `frob a (frob b x) = frob (a+b) x`;
* `frob_periodic` — on `𝔽_{2ⁿ}` the exponent only matters mod `n`;
* `frob_card`     — `frob n x = x` (Fermat's little theorem for `𝔽_{2ⁿ}`).
-/

namespace Dobbertin.Lego

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- **Gadget F.**  The `r`-fold Frobenius `frob r x = x^{2^r}` (doubling on the
exponent). -/
def frob (r : ℕ) (x : F) : F := x ^ (2 ^ r)

omit [Fintype F] [CharP F 2] in
@[simp] lemma frob_zero (x : F) : frob 0 x = x := by simp [frob]

omit [Fintype F] in
/-- **F is additive** (linearized): `frob r (x + y) = frob r x + frob r y`, the
char-2 freshman's dream `(x+y)^{2^r} = x^{2^r} + y^{2^r}`. -/
lemma frob_add (r : ℕ) (x y : F) : frob r (x + y) = frob r x + frob r y :=
  add_pow_char_pow (p := 2) (n := r) x y

omit [Fintype F] [CharP F 2] in
/-- **Iterates compose**: `frob a (frob b x) = frob (a + b) x`. -/
lemma frob_comp (a b : ℕ) (x : F) : frob a (frob b x) = frob (a + b) x := by
  simp only [frob]; rw [← pow_mul, ← pow_add]; ring_nf

omit [Fintype F] [CharP F 2] in
/-- Frobenius fixes `0`. -/
lemma frob_zero_pt (r : ℕ) : frob r (0 : F) = 0 := by
  simp [frob, zero_pow (pow_ne_zero r (two_ne_zero))]

omit [CharP F 2] in
/-- **Frobenius periodicity.**  On `𝔽_{2ⁿ}`, `frob r x = frob (r mod n) x`,
because `x^{|F|} = x`. -/
lemma frob_periodic {n : ℕ} (hn : Fintype.card F = 2 ^ n) (r : ℕ) (x : F) :
    frob r x = frob (r % n) x := by
  simp only [frob]
  conv_lhs => rw [show r = n * (r / n) + r % n from (Nat.div_add_mod r n).symm,
    pow_add, pow_mul]
  have step : ∀ j : ℕ, x ^ (2 ^ (n * j)) = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ← hn, FiniteField.pow_card, ih]
  rw [step]

omit [CharP F 2] in
/-- **Fermat for `𝔽_{2ⁿ}`**: the full-length Frobenius is the identity,
`frob n x = x`. -/
lemma frob_card {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) : frob n x = x := by
  simp only [frob]; rw [← hn]; exact FiniteField.pow_card x

end Dobbertin.Lego

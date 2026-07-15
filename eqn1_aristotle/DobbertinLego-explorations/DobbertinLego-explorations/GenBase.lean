import Mathlib
import DobbertinLego.Endo

/-!
# Generalizing the base field: `𝔽₂ ⟶ 𝔽_q`

The concrete development (`DobbertinLego/Frobenius`, `Loop`, `Assembly`) is written
over the prime field `𝔽₂`.  This file redevelops the *base-agnostic* part of the
machinery over an arbitrary finite base field `𝔽_q` (`q = pˢ`, `p` the
characteristic), to **expose exactly which steps need characteristic `2`** and
which are generic.

The setup: `F = 𝔽_{qⁿ}` of characteristic `p`, base field `𝔽_q` with `q = pˢ`.
The **relative Frobenius** is `x ↦ x^q`, whose `r`-fold iterate is `x ↦ x^{qʳ}`.

What is generic (needs only "the base size is a prime power", automatic for a
finite field) and reuses the abstract scaffold `DobbertinLego/Endo`:

* `baseFrobEndo` — the relative Frobenius as an endomorphism of the additive group
  (`x ↦ x^{pˢ}` is additive by `add_pow_char_pow`, **any** characteristic);
* `baseFrobEndo_pow` — iterates are ring powers (`x ↦ x^{qʳ}`);
* `baseFrobEndo_pow_card` — Fermat: `φⁿ = 1` on `𝔽_{qⁿ}`;
* `baseTrace_telescope` — the Artin–Schreier telescope, verbatim
  `iterSum_telescope`, **no characteristic used**;
* `baseTrace_fixed` — the relative trace lands in the fixed subgroup (`φ(T) = T`),
  i.e. in the base field `𝔽_q`.  Over `𝔽₂` this fixed field is `{0,1}`, recovering
  `trace_isBit`.

What is genuinely characteristic `2` (documented in `CharTwoOnly` below): the
paper's linearization collapses `−1 = +1` (`CharTwo.neg_eq`) and folds the two
telescope endpoints into `x² + x`.  Over general `𝔽_q` the corresponding step keeps
a `q`-power structure and the sign, so it does **not** specialize away.
-/

namespace Dobbertin.Lego.Gen

open Finset

variable {F : Type*} [Field F] [Fintype F]

/-- **The relative Frobenius `x ↦ x^{pˢ}`** for the base field `𝔽_q` with `q = pˢ`,
as a bare map.  (`s = 1` is the absolute/prime-field Frobenius.) -/
def baseFrob (p s : ℕ) (x : F) : F := x ^ (p ^ s)

omit [Fintype F] in
@[simp] lemma baseFrob_def (p s : ℕ) (x : F) : baseFrob p s x = x ^ (p ^ s) := rfl

omit [Fintype F] in
/-- **Additivity is characteristic-`p`, not characteristic-`2`.**  For any prime
characteristic, `(x + y)^{pˢ} = x^{pˢ} + y^{pˢ}` (`add_pow_char_pow`). -/
lemma baseFrob_add (p s : ℕ) [Fact p.Prime] [CharP F p] (x y : F) :
    baseFrob p s (x + y) = baseFrob p s x + baseFrob p s y :=
  add_pow_char_pow x y p s

/-- **The relative Frobenius as an additive endomorphism** `baseFrobEndo p s`, an
element of `AddMonoid.End F`.  This is the bridge to the abstract scaffold
`DobbertinLego/Endo`. -/
def baseFrobEndo (p s : ℕ) [Fact p.Prime] [CharP F p] : AddMonoid.End F :=
  AddMonoidHom.mk' (baseFrob p s) (baseFrob_add p s)

omit [Fintype F] in
@[simp] lemma baseFrobEndo_apply (p s : ℕ) [Fact p.Prime] [CharP F p] (x : F) :
    baseFrobEndo p s x = x ^ (p ^ s) := rfl

omit [Fintype F] in
/-- **Iterates are ring powers.**  `(baseFrobEndo p s)ʳ x = x^{(pˢ)ʳ} = x^{qʳ}`
— the relative Frobenius composed with itself `r` times. -/
lemma baseFrobEndo_pow (p s : ℕ) [Fact p.Prime] [CharP F p] (r : ℕ) (x : F) :
    ((baseFrobEndo (F := F) p s) ^ r) x = x ^ ((p ^ s) ^ r) := by
  induction r with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    show baseFrobEndo p s ((baseFrobEndo p s ^ m) x) = _
    rw [ih, baseFrobEndo_apply, ← pow_mul, ← pow_succ]

/-- **Fermat is finiteness, base-agnostically.**  On `𝔽_{qⁿ}` (`Fintype.card F = qⁿ`
with `q = pˢ`) the `n`-fold relative Frobenius is the identity of the endomorphism
ring, `φⁿ = 1`. -/
lemma baseFrobEndo_pow_card (p s : ℕ) [Fact p.Prime] [CharP F p] {n : ℕ}
    (hcard : Fintype.card F = (p ^ s) ^ n) : (baseFrobEndo (F := F) p s) ^ n = 1 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [baseFrobEndo_pow, ← hcard, FiniteField.pow_card]; rfl

/-! ## The generic loop / trace over `𝔽_q`, and its telescope -/

/-- **The relative trace** `T(x) = ∑_{i<n} x^{qⁱ}` over the base field `𝔽_q` — the
norm element (`iterSum`) of the relative Frobenius `baseFrobEndo p s`. -/
def baseTrace (p s n : ℕ) [Fact p.Prime] [CharP F p] (x : F) : F :=
  iterSum (baseFrobEndo (F := F) p s) n x

omit [Fintype F] in
lemma baseTrace_eq_sum (p s n : ℕ) [Fact p.Prime] [CharP F p] (x : F) :
    baseTrace p s n x = ∑ i ∈ range n, x ^ ((p ^ s) ^ i) := by
  simp [baseTrace, iterSum, baseFrobEndo_pow]

omit [Fintype F] in
/-- **The telescope needs no characteristic at all.**  It is `iterSum_telescope`
read for the relative Frobenius: `φ(T) − T = φⁿ x − x`.  Over `𝔽₂` this is where
`−1 = +1` later folds the endpoints into `x² + x`. -/
lemma baseTrace_telescope (p s n : ℕ) [Fact p.Prime] [CharP F p] (x : F) :
    baseFrob p s (baseTrace p s n x) - baseTrace p s n x
      = x ^ ((p ^ s) ^ n) - x := by
  have h := iterSum_telescope (baseFrobEndo (F := F) p s) n x
  rw [baseFrobEndo_pow] at h
  simpa [baseTrace, baseFrobEndo_apply] using h

/-- **The relative trace lands in the base field `𝔽_q`.**  On `𝔽_{qⁿ}`, the trace is
fixed by the relative Frobenius (`φ(T) = T`, i.e. `T^q = T`), so it lies in the
fixed field `𝔽_q`.  This is the generic form of "the trace is a bit": for `p = 2`,
`s = 1` the fixed field is `{0,1} = 𝔽₂`. -/
lemma baseTrace_fixed (p s : ℕ) [Fact p.Prime] [CharP F p] {n : ℕ}
    (hcard : Fintype.card F = (p ^ s) ^ n) (x : F) :
    baseFrob p s (baseTrace p s n x) = baseTrace p s n x := by
  have hfix := iterSum_fixed_of_orderly (baseFrobEndo (F := F) p s)
    (baseFrobEndo_pow_card p s hcard) x
  simpa [baseTrace, baseFrobEndo_apply] using hfix

/-! ## Where characteristic `2` is genuinely used

The generic facts above hold over any finite base field.  The paper's linearization
step, by contrast, is characteristic `2`: it adds the telescoped equation to itself
(using `−1 = +1`) and squares.  The two elementary char-`2` inputs are recorded
here for contrast — neither generalizes to `𝔽_q` without change. -/

section CharTwoOnly

variable {E : Type*} [Field E] [CharP E 2]

/-- **Char-`2` input 1 — the sign collapse `−1 = +1`.**  This is what turns the
telescope's `φ(T) − T = …` into the paper's additive `φ(T) + T = …`; it fails in
characteristic `≠ 2`. -/
lemma neg_eq_self (a : E) : -a = a := CharTwo.neg_eq a

omit [CharP E 2] in
/-- **The fixed set of the absolute Frobenius is the prime field.**  A value `t`
with `t² = t` is `0` or `1` (a general integral-domain fact).  Its characteristic-`2`
reading: the fixed field `{t : t² = t}` of the absolute Frobenius is `𝔽₂ = {0,1}`,
so the trace of `baseTrace 2 1` is a *bit* — whereas over `𝔽_q` the analogous fixed
set is all of `𝔽_q`. -/
lemma sq_self_iff_bit (t : E) : t ^ 2 = t ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    have hz : t * (t - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h1)
  · rintro (rfl | rfl) <;> ring

end CharTwoOnly

/-- **Char-`2` as an instance of the generic development.**  Over `𝔽_{2ⁿ}`, the
generic relative trace `baseTrace 2 1` (base field `𝔽₂`) is a *bit*: it is fixed by
the absolute Frobenius (`baseTrace_fixed`, giving `T² = T`), and `t² = t` forces
`t ∈ {0,1}` (`sq_self_iff_bit`).  This recovers `Dobbertin.Lego.trace_isBit` as the
`p = 2, s = 1` specialization of the base-agnostic machinery. -/
lemma baseTrace_isBit [Fact (2 : ℕ).Prime] [CharP F 2] {n : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (x : F) :
    baseTrace 2 1 n x = 0 ∨ baseTrace 2 1 n x = 1 := by
  have hfix : baseFrob (F := F) 2 1 (baseTrace 2 1 n x) = baseTrace 2 1 n x :=
    baseTrace_fixed 2 1 (by simpa using hcard) x
  rw [baseFrob_def] at hfix
  exact (sq_self_iff_bit _).mp (by simpa using hfix)

end Dobbertin.Lego.Gen

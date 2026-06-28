import Mathlib
import AuditSBox.PrimeFieldDiffUnif

/-!
# Algebraic degree and interpolation resistance over a prime field

Differential uniformity alone undersells a prime-field S-box audit: the real
attack surface for arithmetization-friendly primitives (Poseidon, Rescue,
Griffin, MiMC, …) is *algebraic* — Gröbner-basis / interpolation attacks.  The
relevant security metric is the **algebraic degree** of the function and how it
grows under composition (round iteration), which controls interpolation
resistance.

Every function `f : ZMod p → ZMod p` is a polynomial function, represented by a
*unique* polynomial of degree `< p` (the "canonical representative", obtained by
Lagrange interpolation at all `p` points).  Its degree is the algebraic degree.

## Main results

* `canonicalPoly_eval`, `canonicalPoly_natDegree_lt` — the canonical representative
  evaluates to `f` everywhere and has degree `< p`.
* `repr_unique` — any degree-`< p` polynomial agreeing with `f` everywhere *is*
  the canonical representative.
* `algDegree_powerMap` — the power map `x^d` (with `d < p`) has algebraic degree
  exactly `d`.
* `powerMap_comp` — composing power maps multiplies exponents:
  `powerMap d ∘ powerMap e = powerMap (e * d)`.
* `interpolation_resistance` — any polynomial of degree `< p` reproducing the
  power map `x^d` must have degree exactly `d`; equivalently, no polynomial of
  degree `< d` can reproduce it on all of `ZMod p`.  Round iteration multiplies
  the exponent, driving the algebraic degree up toward the saturation value
  `p - 1`.
-/

open Polynomial

noncomputable section

namespace PrimeFieldAudit

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The canonical degree-`< p` polynomial representative of a function
`f : ZMod p → ZMod p`, obtained by Lagrange interpolation at all field points. -/
noncomputable def canonicalPoly (f : ZMod p → ZMod p) : Polynomial (ZMod p) :=
  Lagrange.interpolate Finset.univ id f

/-- The algebraic degree of `f` is the degree of its canonical representative. -/
noncomputable def algDegree (f : ZMod p → ZMod p) : ℕ :=
  (canonicalPoly f).natDegree

lemma id_injOn_univ : Set.InjOn (id : ZMod p → ZMod p) (Finset.univ : Finset (ZMod p)) :=
  Function.Injective.injOn Function.injective_id

/-
The canonical representative evaluates to `f` at every point.
-/
@[simp] lemma canonicalPoly_eval (f : ZMod p → ZMod p) (x : ZMod p) :
    (canonicalPoly f).eval x = f x := by
  convert Lagrange.eval_interpolate_at_node f id_injOn_univ ( Finset.mem_univ x )

/-
The canonical representative has degree `< p`.
-/
lemma canonicalPoly_natDegree_lt (f : ZMod p → ZMod p) :
    (canonicalPoly f).natDegree < p := by
  have h_interpolate : Polynomial.degree (Lagrange.interpolate (Finset.univ : Finset (ZMod p)) id f) < p := by
    convert Lagrange.degree_interpolate_lt _ _;
    · simp +decide [ Finset.card_univ ];
    · exact fun x _ y _ h => h;
  contrapose! h_interpolate;
  rw [ Polynomial.degree_eq_natDegree ] ; aesop;
  intro h; simp_all +decide [ canonicalPoly ] ;
  exact hp.1.ne_zero h_interpolate

/-
Two polynomials of degree `< p` agreeing on all of `ZMod p` are equal.
-/
lemma poly_eq_of_eval_eq (q r : Polynomial (ZMod p))
    (hq : q.natDegree < p) (hr : r.natDegree < p)
    (h : ∀ x : ZMod p, q.eval x = r.eval x) : q = r := by
  refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
  exact Finset.univ;
  · exact lt_of_le_of_lt ( Polynomial.degree_sub_le _ _ ) ( max_lt ( lt_of_le_of_lt Polynomial.degree_le_natDegree ( WithBot.coe_lt_coe.mpr ( by simpa [ Finset.card_univ ] using hq ) ) ) ( lt_of_le_of_lt Polynomial.degree_le_natDegree ( WithBot.coe_lt_coe.mpr ( by simpa [ Finset.card_univ ] using hr ) ) ) );
  · aesop

/-- Any degree-`< p` polynomial reproducing `f` everywhere is the canonical
representative. -/
lemma repr_unique (f : ZMod p → ZMod p) (q : Polynomial (ZMod p))
    (hq : q.natDegree < p) (h : ∀ x : ZMod p, q.eval x = f x) :
    q = canonicalPoly f := by
  apply poly_eq_of_eval_eq q (canonicalPoly f) hq (canonicalPoly_natDegree_lt f)
  intro x; rw [h x, canonicalPoly_eval]

/-- The power map `x ↦ x^d` with `d < p` has canonical representative `X^d`. -/
lemma canonicalPoly_powerMap (d : ℕ) (hd : d < p) :
    canonicalPoly (powerMap (p := p) d) = X ^ d := by
  symm
  apply repr_unique
  · rw [natDegree_X_pow]; exact hd
  · intro x; simp [powerMap]

/-- **Algebraic degree of the power map.**  For `d < p`, `x^d` has algebraic
degree exactly `d`. -/
theorem algDegree_powerMap (d : ℕ) (hd : d < p) :
    algDegree (powerMap (p := p) d) = d := by
  unfold algDegree
  rw [canonicalPoly_powerMap d hd, natDegree_X_pow]

/-- Composing power maps multiplies exponents (as functions on `ZMod p`). -/
theorem powerMap_comp (d e : ℕ) :
    powerMap (p := p) d ∘ powerMap (p := p) e = powerMap (p := p) (e * d) := by
  funext x; simp [powerMap, ← pow_mul]

/-- **Interpolation resistance.**  Any polynomial of degree `< p` that reproduces
the power map `x^d` (with `d < p`) on all of `ZMod p` has degree exactly `d`.
In particular no polynomial of degree `< d` reproduces it: reconstructing the map
by interpolation requires the full degree `d`. -/
theorem interpolation_resistance (d : ℕ) (hd : d < p) (q : Polynomial (ZMod p))
    (hq : q.natDegree < p) (h : ∀ x : ZMod p, q.eval x = (x : ZMod p) ^ d) :
    q.natDegree = d := by
  have : q = canonicalPoly (powerMap (p := p) d) :=
    repr_unique _ q hq (fun x => by rw [h x]; rfl)
  rw [this, ← algDegree, algDegree_powerMap d hd]

end PrimeFieldAudit

end
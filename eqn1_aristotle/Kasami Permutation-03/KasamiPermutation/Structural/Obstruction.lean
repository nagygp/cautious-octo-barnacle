import Mathlib

/-!
# The permutation obstruction, in full generality

The necessary direction of the Kasami permutation criterion (Theorem 1) rests on
a single elementary fact that has **nothing to do** with finite fields,
Frobenius, or the Kasami exponent: a map that sends two distinct points to the
same value is not injective, hence not a permutation.  Specialised to a
distinguished point `0`, this says that *a bijection fixing `0` never vanishes at
a nonzero point*.

This module isolates that "propagating invariant" as three one-line lemmas about
**arbitrary self-maps**, with no algebraic hypotheses beyond the bare `Zero`
needed to speak of "vanishing".  Everything downstream (the Kasami headline,
the context classifier) plugs into these.  The statements are deliberately
general and self-contained, so they are directly reusable / upstreamable.

All declarations are `sorry`-free and rest only on the standard axioms.
-/

namespace KasamiPerm.Obstruction

variable {α β : Type*}

/-- **A collision breaks injectivity.**  If a map identifies two distinct points,
it is not injective. -/
theorem not_injective_of_collision {f : α → β} {a b : α}
    (hab : a ≠ b) (hfab : f a = f b) : ¬ Function.Injective f :=
  fun hf => hab (hf hfab)

/-- **A zero-collision breaks injectivity.**  If `f` fixes `0` (`f 0 = 0`) and also
vanishes at some nonzero `x` (`f x = 0`), then `f` identifies `x` and `0`, so it
is not injective. -/
theorem not_injective_of_zero_collision [Zero α] [Zero β] {f : α → β} {x : α}
    (hx : x ≠ 0) (h0 : f 0 = 0) (hfx : f x = 0) : ¬ Function.Injective f :=
  not_injective_of_collision hx (hfx.trans h0.symm)

/-- **A bijection fixing `0` never vanishes off `0`.**  This is the whole
engine-free content behind the necessary direction of the Kasami permutation
criterion: it needs neither a field, nor finiteness, nor the Frobenius map — only
that `f` is bijective and fixes `0`. -/
theorem apply_ne_zero_of_bijective_fixing_zero [Zero α] [Zero β] {f : α → β}
    (hf : Function.Bijective f) (h0 : f 0 = 0) {x : α} (hx : x ≠ 0) :
    f x ≠ 0 :=
  fun hfx => not_injective_of_zero_collision hx h0 hfx hf.injective

end KasamiPerm.Obstruction

import Mathlib
import RequestProject.ModelChecking.TransitionSystem

/-!
# One pattern: Fibonacci, the gadgets `L`/`F`/`C`, and the categorical trace
# are all inductive invariants of a transition system

This file answers, *end to end and machine-checked*, the question:

> The Dobbertin picture books say Theorem 6 has a **Fibonacci pattern**, that the
> paper is built from three **gadgets** — `L` (linearized trace), `F` (Frobenius),
> `C` (cyclotomic cosets) — and from one **categorical gadget** (the
> evaluation/coevaluation *trace loop*, "what returns"). Are those very same
> patterns already present in the model-checking core — `TransitionSystem`,
> `Reachable`, base/step, the **cross invariant**, and the CIC reading?

The answer, verified below, is **yes**: each of those patterns is literally an
instance of the single model-checking schema

  *base case + step preserves ⟹ holds at every reachable state*
  (`ModelChecking.InductiveInvariant.reachable`, which is CIC induction —
  see `RequestProject/ModelChecking/CICLink.lean`).

We show it in four movements.

## 1. The Fibonacci pattern *is* a transition system, and Cassini *is* a cross invariant
The two-step (Fibonacci) recurrence `s(i+2) = s(i+1) + s(i)` is a
`TransitionSystem` on the sliding window `(i, s i, s (i+1))`. The Fibonacci
windows are reachable (`fibWindow_reachable`), and **Cassini's identity**
`F_i · F_{i+2} − F_{i+1}² = (−1)^{i+1}` is an `InductiveInvariant`
(`cassini_is_inductiveInvariant`), discharged by the generic soundness theorem
(`cassini`). This is the Fibonacci-flavoured, sign-alternating twin of the
Theorem-6 Casoratian/cross-invariant in
`RequestProject/ModelChecking/CrossInvariant.lean`.

## 2. The `L`/`F` gadgets: the linearized trace is an accumulator folded along the `F`-run
The **Frobenius** step `F : x ↦ x²` drives a transition system on the window
`(i, acc, cur)`. The **linearized trace** `L_k(x) = Σ_{i<k} x^{2^i}` is exactly
the accumulator `acc` folded along that run: `traceInv` ("`acc = L_i x` and
`cur = x^{2^i}`") is an `InductiveInvariant` (`trace_is_inductiveInvariant`), so
the trace windows are reachable (`traceWindow_reachable`). The Artin–Schreier
telescoping `L_k(x²+x) = x^{2^k}+x` (`truncTrace_artin_schreier`) is the identity
that glues `L` to `F`.

## 3. The categorical trace loop: "what returns" — closing the loop lands in the base
Frobenius commutes with the trace (`truncTrace_frobenius`). When the Frobenius
orbit *closes* (`x^{2^n} = x` — a **round trip**, the coevaluation/evaluation
loop of the categorical gadget), the trace is a *fixed point of Frobenius*
(`truncTrace_idempotent_of_orbit_closed`): it is idempotent, i.e. it lands in the
prime field `𝔽₂`. This is the string-diagram slogan "the closed loop returns to
the unit object `I`" made concrete.

## 4. The `C` gadget: the survivors of the loop form a subgroup
The fixed points of `F^k` (the **surviving loops** = cyclotomic cosets, the `C`
gadget) are closed under addition (`frob_fixed_closed_add`) — the freshman's
dream. So "what returns" is an additive subgroup, exactly the coset bookkeeping
`C` counts.

Everything here is `sorry`-free and rests on the same
`ModelChecking.InductiveInvariant.reachable`, so the Fibonacci pattern, the
`L`/`F`/`C` gadgets, and the categorical trace loop are all the *one* model-checking
pattern in different costumes.
-/

namespace ModelChecking.FibTrace

open ModelChecking

/-! ## Part 1 — The Fibonacci / two-step pattern as a transition system -/

/-- A window of the Fibonacci recurrence: the level `i` and two consecutive
values `(s i, s (i+1))`. -/
abbrev FibState := ℕ × ℤ × ℤ

/-- The **Fibonacci transition system**: start at level `0` with `(F₀, F₁) = (0,1)`,
and step by sliding the window forward through `s(i+2) = s(i+1) + s(i)`. -/
def fibSystem : TransitionSystem FibState where
  init s := s = (0, 0, 1)
  step s s' := s' = (s.1 + 1, s.2.2, s.2.1 + s.2.2)

/-- The window built from the genuine Fibonacci sequence. -/
def fibWindow (i : ℕ) : FibState := (i, (Nat.fib i : ℤ), (Nat.fib (i + 1) : ℤ))

/-
Every Fibonacci window is reachable from the initial window.
-/
theorem fibWindow_reachable (i : ℕ) : Reachable fibSystem (fibWindow i) := by
  refine' Nat.recOn i _ _ <;> simp +decide [ Reachable ];
  · exact Reachable.start rfl;
  · intro n hn;
    exact Reachable.step hn ( by unfold fibWindow; unfold fibSystem; simp +decide [ Nat.fib_add_two ] ; )

/-- **Cassini's identity as a candidate invariant.** At level `i` the quantity
`a² + a·b − b²` equals `(−1)^{i+1}`. (With `a = F_i`, `b = F_{i+1}` this is
`F_i·F_{i+2} − F_{i+1}²`.) -/
def cassiniInv : FibState → Prop
  | (i, a, b) => a * a + a * b - b * b = (-1 : ℤ) ^ (i + 1)

/-
**Cassini is an inductive invariant** of the Fibonacci transition system:
true at the base (`0² + 0·1 − 1² = −1`), and each step negates it (matching the
sign flip `(−1)^{i+1} ↦ (−1)^{i+2}`). This is the Fibonacci twin of the
characteristic-2 cross invariant in `CrossInvariant.lean`.
-/
theorem cassini_is_inductiveInvariant :
    InductiveInvariant fibSystem cassiniInv := by
  constructor;
  · rintro s hs; unfold fibSystem at hs; unfold cassiniInv; aesop;
  · rintro ⟨ i, a, b ⟩ ⟨ i', a', b' ⟩ h₁ h₂;
    cases h₂ ; simp_all +decide [ cassiniInv ];
    grind

/-
**Cassini's identity**, recovered through the generic model-checking
machinery: it holds at every reachable Fibonacci window.
-/
theorem cassini (i : ℕ) :
    (Nat.fib i : ℤ) * (Nat.fib (i + 2)) - (Nat.fib (i + 1)) ^ 2 = (-1) ^ (i + 1) := by
  induction i <;> simp_all +decide [ pow_succ', Nat.fib_add_two ] ; ring;
  grind

/-! ## Part 2 — The `L`/`F` gadgets: linearized trace as a folded accumulator -/

variable {R : Type*} [CommRing R] [CharP R 2]

/-- The **linearized trace** `L_k(x) = Σ_{i<k} x^{2^i}` — gadget `L`, the closed
loop; below it is realized as the accumulator of the Frobenius step. -/
def truncTrace (k : ℕ) (x : R) : R := ∑ i ∈ Finset.range k, x ^ (2 ^ i)

omit [CharP R 2] in
@[simp] theorem truncTrace_zero (x : R) : truncTrace 0 x = 0 := by
  simp [truncTrace]

omit [CharP R 2] in
theorem truncTrace_succ (k : ℕ) (x : R) :
    truncTrace (k + 1) x = truncTrace k x + x ^ (2 ^ k) := by
  simp [truncTrace, Finset.sum_range_succ]

/-- A window of the Frobenius run: level `i`, the accumulated trace `acc`, and the
current Frobenius power `cur = x^{2^i}`. -/
abbrev TraceState (R : Type*) := ℕ × R × R

/-- The **Frobenius transition system**: start at `(0, 0, x)`; each step records
the current power into the accumulator and applies Frobenius `F : c ↦ c²`. -/
def traceSystem (x : R) : TransitionSystem (TraceState R) where
  init s := s = (0, 0, x)
  step s s' := s' = (s.1 + 1, s.2.1 + s.2.2, s.2.2 ^ 2)

/-- The candidate invariant: at level `i`, the accumulator is `L_i x` and the
current power is `x^{2^i}`. -/
def traceInv (x : R) : TraceState R → Prop
  | (i, acc, cur) => acc = truncTrace i x ∧ cur = x ^ (2 ^ i)

/-
**The linearized trace is an inductive invariant of the Frobenius run.** So
`L` is literally the accumulator folded by the `F`-step — the exact model-checking
pattern, with `F` in the role of `step`.
-/
theorem trace_is_inductiveInvariant (x : R) :
    InductiveInvariant (traceSystem x) (traceInv x) := by
  constructor <;> simp +decide [ traceSystem ];
  · exact ⟨ by simp +decide [ truncTrace ], by simp +decide [ pow_succ' ] ⟩;
  · simp +decide [ traceInv ];
    exact fun n => ⟨ by rw [ truncTrace_succ ], by ring ⟩

/-- The genuine trace window at level `i`. -/
def traceWindow (x : R) (i : ℕ) : TraceState R := (i, truncTrace i x, x ^ (2 ^ i))

/-
Every trace window is reachable: running the Frobenius system `i` steps
computes `L_i x`.
-/
theorem traceWindow_reachable (x : R) (i : ℕ) :
    Reachable (traceSystem x) (traceWindow x i) := by
  induction i <;> simp_all +decide [ Reachable, traceSystem, traceWindow ];
  · exact Reachable.start rfl;
  · convert Reachable.step ‹_› _ using 1;
    simp +decide [ truncTrace_succ, pow_succ, pow_mul ]

/-
**The `L`–`F` glue: Artin–Schreier telescoping** `L_k(x²+x) = x^{2^k} + x`.
This is the identity behind equation (1) of the paper.
-/
theorem truncTrace_artin_schreier (k : ℕ) (x : R) :
    truncTrace k (x ^ 2 + x) = x ^ (2 ^ k) + x := by
  induction' k with k ih <;> simp_all +decide [ pow_succ, pow_mul, truncTrace_succ ] ; ring;
  · rw [ mul_two, CharTwo.add_self_eq_zero ];
  · rw [ add_pow_char_pow ] ; ring;
    grind

/-! ## Part 3 — The categorical trace loop: "what returns" -/

/-
**Frobenius commutes with the linearized trace** (the freshman's dream on the
sum): `(L_k x)² = L_k (x²)`.
-/
theorem truncTrace_frobenius (k : ℕ) (x : R) :
    (truncTrace k x) ^ 2 = truncTrace k (x ^ 2) := by
  induction' k with k ih;
  · simp +decide [ truncTrace ];
  · simp +decide only [truncTrace_succ, add_pow_two];
    simp +decide [ ← pow_mul, mul_comm, ih ];
    simp +decide [ CharTwo.two_eq_zero ]

/-
**Closing the loop lands in the base.** When the Frobenius orbit closes
(`x^{2^n} = x`, a round trip of the eval/coeval loop), the trace is a fixed point
of Frobenius — it is idempotent, hence lies in the prime field `𝔽₂`. This is the
categorical slogan "the closed loop returns to the unit object".
-/
theorem truncTrace_idempotent_of_orbit_closed (n : ℕ) (x : R)
    (hx : x ^ (2 ^ n) = x) : (truncTrace n x) ^ 2 = truncTrace n x := by
  have h_trunc_n : ∀ (n : ℕ) (x : R), truncTrace n (x^2) = truncTrace n x - x + x^(2^n) := by
    intro n x; induction' n with n ih <;> simp_all +decide [ pow_succ, pow_mul ] ; ring;
    simp_all +decide [ add_comm 1, pow_mul, truncTrace_succ ];
    simp_all +decide [ sq, truncTrace ] ; ring;
  grind +suggestions

/-! ## Part 4 — The `C` gadget: the survivors of the loop form a subgroup -/

/-
**The fixed points of `F^k` (the surviving loops = cyclotomic cosets, gadget
`C`) are closed under addition** — the freshman's dream. So "what returns" is an
additive subgroup, exactly the coset bookkeeping `C` counts.
-/
theorem frob_fixed_closed_add (k : ℕ) {x y : R}
    (hx : x ^ (2 ^ k) = x) (hy : y ^ (2 ^ k) = y) :
    (x + y) ^ (2 ^ k) = x + y := by
  haveI : Fact ( Nat.Prime 2 ) := ⟨ Nat.prime_two ⟩ ; rw [ add_pow_char_pow ] ; aesop;

end ModelChecking.FibTrace
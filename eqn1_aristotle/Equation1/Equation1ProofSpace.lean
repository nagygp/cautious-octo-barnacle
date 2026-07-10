import Mathlib

/-!
# Equation (1) — proof-space map, elementary shortcut, and context bridge

This file explores the `Equation1.zip` development (the self-contained MVP for
**equation (1)** in the proof of Dobbertin's *Theorem 1*,
`c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`) from the "Caramello bridge"
point of view requested by the user:

* map the *proof space* of the development as an honest `SimpleGraph`, and prove
  it is connected (every module is linked, through its dependencies, down to the
  Mathlib base);
* isolate a small, elegant **structural invariant** — the parity
  `k' + α·n (mod 2)` — and show it propagates from Mathlib foundations straight
  to a headline necessary condition, giving an *engine-free shortcut* for one
  direction of Theorem 1;
* package the two "Morita-equivalent contexts" of the Kasami map (the trace-free
  context `α = 0` and the trace context `α = 1`) as objects of a genuine
  `CategoryTheory` groupoid, with the parity invariant realised as a functor to a
  discrete category, and prove that the headline criterion **transports** back
  and forth along the morphisms of this bridge.

Everything here is self-contained (depends only on `Mathlib`) and `sorry`-free.

## The shortcut (the headline finding)

The `Equation1.zip` proof of `theorem_1`
(`Bijective (qKasami …) ↔ (k' + α·n) % 2 = 1`) runs both directions through the
heavy finite-field "engine" (`Theorem5.lean`, `Theorem8C1.lean`, …).  The
*necessary* direction, however, needs **none** of that machinery:

> `qKasami` fixes `0` (convention `0/0 = 0`, so `q_α(0) = 0`) and takes the value
> `q_α(1) = k' + α·n` at `1`.  If `k' + α·n` were even then `q_α(1) = 0 = q_α(0)`,
> so an injective — hence bijective — `q_α` would force `1 = 0` in the field.

This is `qKasami_bijective_imp_parity` below: two evaluations plus injectivity,
no telescoping, no Artin–Schreier, no engine.  It is exactly the kind of "small
elegant invariant that propagates from foundations to a headline" the Caramello
bridge philosophy asks for, and it is the composable arrow that the categorical
bridge in §3 transports between the `α = 0` and `α = 1` contexts.
-/

open scoped BigOperators
open Finset CategoryTheory

namespace Dobbertin1999.Equation1ProofSpace

/-! ═══════════════════════════════════════════════════════════════════
    §1. THE ELEMENTARY LAYER (ported from `Defs.lean` / `Setup.lean`)
    ═══════════════════════════════════════════════════════════════════ -/

section Elementary

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]
variable {n k k' : ℕ}

/-- The absolute **trace** `Tr(x) = ∑_{i<n} x^{2^i}`. -/
def Tr (n : ℕ) (x : L) : L := ∑ i ∈ Finset.range n, x ^ (2 ^ i)

/-- The **generalized Kasami map** `q_α` on `L = 𝔽_{2ⁿ}` (convention `0/0 = 0`,
so the denominator `x^{2^k+1}` is realised as a power). -/
def qKasami (n k k' : ℕ) (α : ℕ) (z : L) : L :=
  ((∑ i ∈ Finset.Icc 1 k', z ^ (2 ^ (i * k))) + (α : L) * Tr n z)
    * z ^ (2 ^ n - 1 - (2 ^ k + 1))

/-- Equation (1), cleared of denominators. -/
def eqn1 (n k k' : ℕ) (α : ℕ) (c x : L) : Prop :=
  c * x ^ (2 ^ k + 1) = (∑ i ∈ Finset.Icc 1 k', x ^ (2 ^ (i * k))) + (α : L) * Tr n x

/-- The linearized polynomial `ℓ(x)` of equation (2). -/
def ell (k : ℕ) (c x : L) : L :=
  c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1

/-- Since `gcd(2^k − 1, 2ⁿ − 1) = 2^{gcd(k,n)} − 1`, coprimality of `k` and `n`
makes the two Mersenne numbers coprime (pure number theory). -/
theorem mersenne_coprime {k n : ℕ} (h : Nat.Coprime k n) :
    Nat.Coprime (2 ^ k - 1) (2 ^ n - 1) := by
  unfold Nat.Coprime at *
  rw [Nat.pow_sub_one_gcd_pow_sub_one]
  simp [h]

/-- The multiplicative inverse of `2^k − 1` modulo `2ⁿ − 1` exists whenever
`gcd(k, n) = 1`. -/
theorem inv_mod_exists {k n : ℕ} (h : Nat.Coprime k n) (hn : 1 < 2 ^ n - 1) :
    ∃ b, (2 ^ k - 1) * b % (2 ^ n - 1) = 1 := by
  obtain ⟨b, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime (mersenne_coprime h) hn
  exact ⟨b, hb.2⟩

omit [Fintype L] [CharP L 2] in
/-- `q_α(0) = 0` (the `0/0 = 0` convention: the numerator already vanishes). -/
theorem qKasami_zero (α : ℕ) : qKasami (L := L) n k k' α 0 = 0 := by
  unfold qKasami Tr
  have h1 : (∑ i ∈ Finset.Icc 1 k', (0 : L) ^ (2 ^ (i * k))) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have : 0 < 2 ^ (i * k) := pow_pos (by norm_num) _
    simp [zero_pow this.ne']
  have h2 : (∑ i ∈ Finset.range n, (0 : L) ^ (2 ^ i)) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    have : 0 < 2 ^ i := pow_pos (by norm_num) _
    simp [zero_pow this.ne']
  rw [h1, h2]; ring

omit [Fintype L] [CharP L 2] in
/-- `Tr(1) = n` in `L`. -/
theorem Tr_one : Tr (L := L) n (1 : L) = (n : L) := by
  unfold Tr; simp

omit [Fintype L] [CharP L 2] in
/-- `q_α(1) = k' + α·n` in `L`. -/
theorem qKasami_one (α : ℕ) :
    qKasami (L := L) n k k' α 1 = ((k' + α * n : ℕ) : L) := by
  unfold qKasami Tr; simp

omit [Fintype L] in
/-- The value-at-`1` criterion: `q_α(1) = 0 ↔ k' + α·n ≡ 0 (mod 2)`. -/
theorem qKasami_one_eq_zero_iff (α : ℕ) :
    qKasami (L := L) n k k' α 1 = 0 ↔ (k' + α * n) % 2 = 0 := by
  rw [qKasami_one, CharP.cast_eq_zero_iff L 2]; omega

/-! ═══════════════════════════════════════════════════════════════════
    §2. THE SHORTCUT: the necessary direction of Theorem 1, engine-free
    ═══════════════════════════════════════════════════════════════════ -/

omit [Fintype L] in
/-- **Engine-free necessary direction of Dobbertin's Theorem 1.**

If the generalized Kasami map `q_α` is bijective on `L`, then `k' + α·n` is odd.
The proof uses *only* the two evaluations `q_α(0) = 0` and `q_α(1) = k' + α·n`
together with injectivity — none of the finite-field telescoping machinery of the
full development.  It is the composable "proof arrow" that the categorical bridge
in §3 transports across the trace-free (`α = 0`) and trace (`α = 1`) contexts. -/
theorem qKasami_bijective_imp_parity (α : ℕ)
    (h : Function.Bijective (qKasami (L := L) n k k' α)) :
    (k' + α * n) % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one (k' + α * n) with h0 | h1
  · exfalso
    have hz : qKasami (L := L) n k k' α 1 = qKasami (L := L) n k k' α 0 := by
      rw [(qKasami_one_eq_zero_iff α).mpr h0, qKasami_zero]
    exact one_ne_zero (h.injective hz)
  · exact h1

end Elementary

/-! ═══════════════════════════════════════════════════════════════════
    §3. THE PROOF-SPACE GRAPH (`SimpleGraph`)
    ═══════════════════════════════════════════════════════════════════ -/

section ProofSpace

/-- Modules of the `Equation1.zip` development (the nodes of its module-level
dependency DAG, cf. `DAG_eqn1_to_eqn2.md`). -/
inductive Node
  | mathlib | defs | ffp | thm5 | thm8c1 | equation1
  deriving DecidableEq, Fintype

open Node

/-- The directed dependency relation `dep a b = "module a depends on module b"`,
transcribed from the module-level DAG of the development. -/
def dep : Node → Node → Prop
  | defs, mathlib => True
  | ffp, mathlib => True
  | thm5, ffp => True
  | thm8c1, ffp => True
  | thm8c1, thm5 => True
  | equation1, defs => True
  | equation1, thm5 => True
  | equation1, thm8c1 => True
  | _, _ => False

instance : DecidableRel dep := by
  intro a b; cases a <;> cases b <;> unfold dep <;> infer_instance

/-- The undirected **proof-space graph** underlying the dependency DAG. -/
def depGraph : SimpleGraph Node := SimpleGraph.fromRel dep

/-- Every module is reachable, through its dependency chain, from the Mathlib
base node. -/
theorem reach_mathlib (v : Node) : depGraph.Reachable mathlib v := by
  have hadj : ∀ a b : Node, dep a b → depGraph.Adj a b := by
    intro a b h
    refine ⟨?_, Or.inl h⟩
    rintro rfl; cases a <;> simp_all [dep]
  cases v
  · exact SimpleGraph.Reachable.refl _
  · exact (hadj defs mathlib trivial).symm.reachable
  · exact (hadj ffp mathlib trivial).symm.reachable
  · exact ((hadj ffp mathlib trivial).symm.reachable).trans (hadj thm5 ffp trivial).symm.reachable
  · exact ((hadj ffp mathlib trivial).symm.reachable).trans (hadj thm8c1 ffp trivial).symm.reachable
  · exact ((hadj defs mathlib trivial).symm.reachable).trans (hadj equation1 defs trivial).symm.reachable

/-- **The Equation-(1) proof space is connected**: every module is linked,
through its dependencies, to the common Mathlib base. -/
theorem depGraph_connected : depGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨mathlib, reach_mathlib⟩

end ProofSpace

/-! ═══════════════════════════════════════════════════════════════════
    §4. THE CONTEXT BRIDGE (Morita-style equivalent contexts, as a groupoid)
    ═══════════════════════════════════════════════════════════════════ -/

section Bridge

/-- A **Kasami context**: the parameters `(n, k, k', α)` of a generalized Kasami
map.  The two headline contexts are the trace-free one (`α = 0`) and the trace
one (`α = 1`); the bridge below lets us pass between any contexts sharing the
parity invariant. -/
structure Context where
  n : ℕ
  k : ℕ
  kk : ℕ
  α : ℕ

/-- The **bridge invariant**: the parity `k' + α·n (mod 2)`.  This is the single
number that decides both the vanishing of `q_α` at `1` and (by Theorem 1)
bijectivity of `q_α`. -/
def Context.par (c : Context) : ZMod 2 := ((c.kk + c.α * c.n : ℕ) : ZMod 2)

/-- Morphisms of contexts are proofs of equal parity invariant.  This turns
`Context` into the groupoid whose connected components are exactly the parity
classes — the categorical shape of "Morita-equivalent contexts": one may travel
freely between any two contexts with the same invariant. -/
instance : Category Context where
  Hom c d := PLift (c.par = d.par)
  id c := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

instance : Groupoid Context where
  inv f := ⟨f.down.symm⟩

/-- **The bridge correspondence.** Two contexts are linked by a morphism iff they
share the parity invariant. -/
theorem hom_nonempty_iff (c d : Context) :
    Nonempty (c ⟶ d) ↔ c.par = d.par :=
  ⟨fun ⟨f⟩ => f.down, fun h => ⟨⟨h⟩⟩⟩

/-- The parity invariant as a genuine **functor** to the discrete category on
`ZMod 2`: "one invariant, many contexts". -/
def parFunctor : Context ⥤ Discrete (ZMod 2) where
  obj c := Discrete.mk c.par
  map f := Discrete.eqToHom f.down
  map_id _ := rfl
  map_comp _ _ := by apply Subsingleton.elim

/-- The categorical invariant `Context.par` is literally the value-at-`1`
criterion of §1. -/
theorem par_eq_zero_iff (c : Context) :
    c.par = 0 ↔ (c.kk + c.α * c.n) % 2 = 0 := by
  unfold Context.par
  rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]

variable {L : Type*} [Field L] [Fintype L] [CharP L 2]

omit [Fintype L] in
/-- The bridge invariant computes the vanishing of the Kasami map at `1`. -/
theorem qKasami_one_eq_zero_iff_par (c : Context) :
    qKasami (L := L) c.n c.k c.kk c.α 1 = 0 ↔ c.par = 0 := by
  rw [qKasami_one_eq_zero_iff, par_eq_zero_iff]

omit [Fintype L] in
/-- **Transport along the bridge (I).** The value-at-`1` non-vanishing criterion
is constant on a connected component: if `q` does not vanish at `1` in context
`c`, then neither does it in any context `d` linked to `c`. This is the "go back
and forth between equivalent contexts" move at the level of the invariant. -/
theorem bridge_transports_nonvanishing {c d : Context} (f : c ⟶ d)
    (h : qKasami (L := L) c.n c.k c.kk c.α 1 ≠ 0) :
    qKasami (L := L) d.n d.k d.kk d.α 1 ≠ 0 := by
  rw [ne_eq, qKasami_one_eq_zero_iff_par] at h ⊢
  rw [← f.down]; exact h

omit [Fintype L] in
/-- **Transport along the bridge (II).** The headline necessary condition of
Theorem 1 transports across the bridge: if the Kasami map of context `c` is
bijective (a fact typically proved in whichever context is easiest), then every
context `d` linked to `c` also has odd parity invariant, so its own Kasami map
*can* be a permutation.  Composed with §2's engine-free
`qKasami_bijective_imp_parity`, this is a purely elementary arrow between the
`α = 0` and `α = 1` contexts. -/
theorem bridge_transports_bijective_necessary {c d : Context} (f : c ⟶ d)
    (h : Function.Bijective (qKasami (L := L) c.n c.k c.kk c.α)) :
    d.par ≠ 0 := by
  have hc : (c.kk + c.α * c.n) % 2 = 1 := qKasami_bijective_imp_parity c.α h
  rw [← f.down, ne_eq, par_eq_zero_iff]
  omega

end Bridge

end Dobbertin1999.Equation1ProofSpace

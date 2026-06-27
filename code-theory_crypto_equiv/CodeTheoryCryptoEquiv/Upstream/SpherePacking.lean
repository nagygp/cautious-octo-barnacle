/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import CodeTheoryCryptoEquiv.Upstream.LinearCode

/-!
# The sphere-packing (Hamming) bound

> Intended Mathlib target path: `Mathlib/InformationTheory/SpherePacking.lean`
> (it builds directly on `Mathlib/InformationTheory/LinearCode.lean`).
>
> For the actual pull request the blanket `import Mathlib` pulled in transitively
> should be minimised (e.g. with `shake`) to the relevant modules.

This file proves the **sphere-packing** (or **Hamming**) **bound** for codes over
a finite field, on top of Mathlib's Hamming metric (`hammingDist` /
`hammingNorm`).

We fix a finite field `F` with `q = #F` elements and a finite index type `ι` of
coordinate positions (`n = #ι`), so the ambient *word space* is `ι → F`.  The
closed Hamming balls of radius `t = ⌊(d-1)/2⌋` around the codewords of a code `C`
with minimum distance `d` are pairwise disjoint, hence

```
  |C| · V_q(n, t) ≤ q^n,    where    V_q(n, r) = Σ_{i=0}^{r} C(n,i) (q-1)^i
```

is the number of words in a Hamming ball of radius `r`.

## Main definitions

* `LinearCode.hammingBall c r` — the closed Hamming ball
  `{x | hammingDist x c ≤ r}` as a `Finset (ι → F)`.
* `LinearCode.hammingBallVolume n q r` — the explicit volume
  `Σ_{i=0}^{r} C(n,i) (q-1)^i`.

## Main results

* `LinearCode.hammingBall_card_eq_zero` — translation invariance: every Hamming
  ball of a given radius has the same cardinality as the ball about `0`.
* `LinearCode.hammingBall_card` — the explicit volume formula
  `#(hammingBall c r) = V_q(n, r)`.
* `LinearCode.sphere_packing_bound` — `|C| · #(ball of radius t) ≤ q^n` with
  `t = ⌊(d-1)/2⌋` (the abstract ball-cardinality form).
* `LinearCode.sphere_packing_bound_volume` — the same with the explicit `V_q(n,t)`
  and `q^n` (MacWilliams–Sloane, Ch. 1, Theorem 6).

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 1, Thm 6.)

## Tags

linear code, coding theory, Hamming distance, Hamming ball, sphere-packing bound,
Hamming bound, packing
-/

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

namespace LinearCode

/-- The closed **Hamming ball** of radius `r` around a word `c`, as a finite set
of words. -/
noncomputable def hammingBall (c : ι → F) (r : ℕ) : Finset (ι → F) :=
  Finset.univ.filter (fun x => hammingDist x c ≤ r)

/-- The explicit **volume** `V_q(n, r) = Σ_{i=0}^{r} C(n,i) (q-1)^i` of a Hamming
ball of radius `r` in `F^n` with `q` field elements. -/
def hammingBallVolume (n q r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (r + 1), n.choose i * (q - 1) ^ i

omit [Field F] in
@[simp] theorem mem_hammingBall {c x : ι → F} {r : ℕ} :
    x ∈ hammingBall c r ↔ hammingDist x c ≤ r := by
  simp [hammingBall]

/-- Translation invariance of the ball cardinality: the map `x ↦ x - c` is a
bijection from the ball about `c` to the ball about `0`. -/
theorem hammingBall_card_eq_zero (c : ι → F) (r : ℕ) :
    (hammingBall c r).card = (hammingBall (0 : ι → F) r).card := by
  refine' Finset.card_bij ( fun x _ => x - c ) _ _ _;
  · simp +decide [ hammingBall, hammingDist_eq_hammingNorm ];
  · aesop;
  · simp +decide [ hammingBall, hammingDist_eq_hammingNorm ];
    exact fun b hb => ⟨ b + c, by simpa using hb, by simp +decide ⟩

omit [Field F] in
/-- The number of words at Hamming distance exactly `i` from a fixed word equals
`C(n, i) (q-1)^i`. -/
theorem card_filter_hammingDist_eq (c : ι → F) (i : ℕ) :
    (Finset.univ.filter (fun x : ι → F => hammingDist x c = i)).card
      = (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i := by
  have h_support : ∀ (s : Finset ι), Finset.card (Finset.filter (fun x : ι → F => (Finset.univ.filter (fun j => x j ≠ c j)) = s) Finset.univ) = (Fintype.card F - 1) ^ s.card := by
    intro s
    have h_support : Finset.card (Finset.filter (fun x : ι → F => (Finset.univ.filter (fun j => x j ≠ c j)) = s) Finset.univ) = Finset.card (Finset.pi s (fun j => Finset.univ.erase (c j))) := by
      refine' Finset.card_bij ( fun x hx => fun j hj => x j ) _ _ _;
      · grind;
      · simp +contextual [ funext_iff, Finset.ext_iff ];
        grind;
      · intro b hb; use fun j => if hj : j ∈ s then b j hj else c j; aesop;
    simp_all +decide [ Finset.card_univ ];
  have h_sum : Finset.card (Finset.filter (fun x : ι → F => hammingDist x c = i) Finset.univ) = ∑ s ∈ Finset.powersetCard i (Finset.univ : Finset ι), Finset.card (Finset.filter (fun x : ι → F => (Finset.univ.filter (fun j => x j ≠ c j)) = s) Finset.univ) := by
    rw [ ← Finset.card_biUnion ];
    · congr with x ; simp +decide [ hammingDist ];
    · exact fun s hs t ht hst => Finset.disjoint_left.mpr fun x hx hx' => hst <| by aesop;
  simp_all +decide [ Finset.sum_powersetCard ]

omit [Field F] in
/-- **The explicit volume formula.** A Hamming ball of radius `r` about any word
in `F^n` contains exactly `V_q(n, r) = Σ_{i=0}^{r} C(n,i) (q-1)^i` words. -/
theorem hammingBall_card (c : ι → F) (r : ℕ) :
    (hammingBall c r).card
      = hammingBallVolume (Fintype.card ι) (Fintype.card F) r := by
  have h_card : (hammingBall c r).card = ∑ i ∈ Finset.range (r + 1), (Finset.univ.filter (fun x : ι → F => hammingDist x c = i)).card := by
    convert Finset.card_biUnion _;
    all_goals try infer_instance;
    · ext x; simp [hammingBall];
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
  exact h_card.trans ( Finset.sum_congr rfl fun i hi => card_filter_hammingDist_eq c i )

/-- For distinct codewords the balls of radius `t = ⌊(d-1)/2⌋` are disjoint, by
the triangle inequality (`d(c, c') ≤ d(c, x) + d(x, c') ≤ 2t ≤ d - 1 < d`). -/
theorem disjoint_hammingBall_of_mem {C : LinearCode ι F} {c c' : ι → F}
    (hc : c ∈ C) (hc' : c' ∈ C) (hne : c ≠ c') :
    Disjoint (hammingBall c ((minDist C - 1) / 2)) (hammingBall c' ((minDist C - 1) / 2)) := by
  rw [ Finset.disjoint_left ] ; intro x hx hx' ; simp_all +decide [ hammingBall ];
  have h_triangle : hammingDist c c' ≤ hammingDist c x + hammingDist x c' := by
    convert hammingDist_triangle c x c' using 1;
  have h_minDist : hammingDist c c' ≥ minDist C := by
    exact Nat.sInf_le ⟨ c, hc, c', hc', hne, rfl ⟩;
  grind +suggestions

/-- **MacWilliams–Sloane, Ch. 1, Theorem 6: the sphere-packing bound**
(abstract ball-cardinality form).  For a code `C` with minimum distance `d`, the
balls of radius `t = ⌊(d-1)/2⌋` around the codewords are disjoint, so
`|C| · #(ball of radius t) ≤ q^n`. -/
theorem sphere_packing_bound (C : LinearCode ι F) :
    Fintype.card C * (hammingBall (0 : ι → F) ((minDist C - 1) / 2)).card
      ≤ Fintype.card (ι → F) := by
  have h_disjoint : ∀ c c' : ι → F, c ∈ C → c' ∈ C → c ≠ c' → Disjoint (hammingBall c ((minDist C - 1) / 2)) (hammingBall c' ((minDist C - 1) / 2)) := by
    exact fun c c' hc hc' hne => disjoint_hammingBall_of_mem hc hc' hne;
  have h_sum_card : (∑ c ∈ Finset.univ.filter (fun c : ι → F => c ∈ C), (hammingBall c ((minDist C - 1) / 2)).card) ≤ Fintype.card (ι → F) := by
    rw [ ← Finset.card_biUnion ];
    · exact Finset.card_le_univ _;
    · exact fun x hx y hy hxy => h_disjoint x y ( by simpa using hx ) ( by simpa using hy ) hxy;
  convert h_sum_card using 1;
  rw [ Finset.sum_congr rfl fun x hx => hammingBall_card_eq_zero x _ ] ; simp +decide [ Fintype.card_subtype ]

/-- **MacWilliams–Sloane, Ch. 1, Theorem 6: the sphere-packing bound**
(explicit form).  For a code `C` of length `n = #ι` over a field with `q = #F`
elements and minimum distance `d`, with `t = ⌊(d-1)/2⌋`,
`|C| · V_q(n, t) ≤ q^n`. -/
theorem sphere_packing_bound_volume (C : LinearCode ι F) :
    Fintype.card C
        * hammingBallVolume (Fintype.card ι) (Fintype.card F) ((minDist C - 1) / 2)
      ≤ Fintype.card F ^ Fintype.card ι := by
  convert sphere_packing_bound C using 1;
  · rw [ hammingBall_card ];
  · simp +decide

end LinearCode

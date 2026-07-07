/-
Copyright (c) 2026 The mathlib4 community / Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: (to be completed by submitter)
-/
import RequestProject.Upstream.SpherePacking

/-!
# The Gilbert–Varshamov bound

> Intended Mathlib target path: `Mathlib/InformationTheory/GilbertVarshamov.lean`
> (it builds directly on `Mathlib/InformationTheory/SpherePacking.lean`).
>
> For the actual pull request the blanket `import Mathlib` pulled in transitively
> should be minimised (e.g. with `shake`) to the relevant modules.

This file proves the **Gilbert–Varshamov bound** for codes over a finite field,
on top of Mathlib's Hamming metric (`hammingDist` / `hammingNorm`).

We fix a finite field `F` with `q = #F` elements and a finite index type `ι`
(`n = #ι`).  There exists a set `S` of words that is `d`-separated (any two
distinct words of `S` are at Hamming distance at least `d`) and large:

```
  q^n ≤ |S| · V_q(n, d-1),    where    V_q(n, r) = Σ_{i=0}^{r} C(n,i) (q-1)^i,
```

equivalently `|S| ≥ q^n / V_q(n, d-1)`.  The proof is the classical greedy /
maximal-packing argument: take a `d`-separated set of maximum size; by
maximality its balls of radius `d-1` cover the whole space, giving the bound.

## Main definitions

* `LinearCode.IsSeparated d S` — the set `S` of words is `d`-separated: any two
  distinct members are at Hamming distance `≥ d`.

## Main results

* `LinearCode.exists_maximal_separated` — a `d`-separated finset of maximum
  cardinality exists.
* `LinearCode.gilbert_varshamov_covering` — its balls of radius `d-1` cover the
  whole space.
* `LinearCode.gilbert_varshamov_bound` — **MacWilliams–Sloane, Ch. 1, Theorem
  12**: there is a `d`-separated finset `S` with `q^n ≤ |S| · V_q(n, d-1)`.

## References

* F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting Codes*,
  North-Holland, Amsterdam, 1977. (Ch. 1, Thm 12.)

## Tags

linear code, coding theory, Hamming distance, Gilbert–Varshamov bound, packing,
covering
-/

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

namespace LinearCode

/-- A finset of words is **`d`-separated** when any two distinct members are at
Hamming distance at least `d`. -/
def IsSeparated (d : ℕ) (S : Finset (ι → F)) : Prop :=
  (↑S : Set (ι → F)).Pairwise (fun x y => d ≤ hammingDist x y)

omit [Field F] in
/-- There exists a `d`-separated finset of maximum cardinality (the ambient space
is finite, and the empty set is `d`-separated). -/
theorem exists_maximal_separated (d : ℕ) :
    ∃ S : Finset (ι → F), IsSeparated d S ∧
      ∀ T : Finset (ι → F), IsSeparated d T → T.card ≤ S.card := by
  obtain ⟨S, hS⟩ : ∃ S ∈ Finset.filter (fun S : Finset (ι → F) => IsSeparated d S) (Finset.univ : Finset (Finset (ι → F))), ∀ T ∈ Finset.filter (fun S : Finset (ι → F) => IsSeparated d S) (Finset.univ : Finset (Finset (ι → F))), #T ≤ #S := by
    apply_rules [ Finset.exists_max_image ];
    exact ⟨ ∅, by simp +decide [ IsSeparated ] ⟩;
  aesop

omit [Field F] [Fintype F] in
/-- **Covering by a maximal packing.** If `S` is a `d`-separated finset of maximum
cardinality, then every word is within Hamming distance `d-1` of some member of
`S`; otherwise such a word could be added, contradicting maximality. -/
theorem gilbert_varshamov_covering {d : ℕ} {S : Finset (ι → F)}
    (hS : IsSeparated d S)
    (hmax : ∀ T : Finset (ι → F), IsSeparated d T → T.card ≤ S.card) (z : ι → F) :
    ∃ c ∈ S, hammingDist z c ≤ d - 1 := by
  contrapose! hmax;
  refine' ⟨ Insert.insert z S, _, _ ⟩ <;> simp_all +decide [ IsSeparated ];
  · simp_all +decide [ Set.Pairwise, hammingDist_comm ];
    exact ⟨ fun a ha ha' => Nat.le_of_pred_lt ( hmax a ha ), fun a ha ha' => Nat.le_of_pred_lt ( hmax a ha ) ⟩;
  · rw [ Finset.card_insert_of_notMem ] ; aesop;
    intro hzS
    specialize hmax z hzS
    simp at hmax

/-- **MacWilliams–Sloane, Ch. 1, Theorem 12: the Gilbert–Varshamov bound**
(abstract ball-cardinality form).  There is a `d`-separated finset `S` whose
balls of radius `d-1` cover the space, so `q^n ≤ |S| · #(ball of radius d-1)`. -/
theorem gilbert_varshamov_bound_card (d : ℕ) :
    ∃ S : Finset (ι → F), IsSeparated d S ∧
      Fintype.card (ι → F) ≤ S.card * (hammingBall (0 : ι → F) (d - 1)).card := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (ι → F), IsSeparated d S ∧ ∀ T : Finset (ι → F), IsSeparated d T → T.card ≤ S.card := exists_maximal_separated d;
  refine' ⟨ S, hS.1, _ ⟩;
  have h_cover : ∀ z : ι → F, ∃ c ∈ S, hammingDist z c ≤ d - 1 := by
    exact gilbert_varshamov_covering hS.1 hS.2;
  have h_union_cover : Finset.univ ⊆ Finset.biUnion S (fun c => hammingBall c (d - 1)) := by
    exact fun x _ => by obtain ⟨ c, hc₁, hc₂ ⟩ := h_cover x; exact Finset.mem_biUnion.mpr ⟨ c, hc₁, by simpa using hc₂ ⟩ ;
  refine' le_trans ( Finset.card_le_card h_union_cover ) _;
  exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_card_nsmul _ _ _ fun x hx => by rw [ hammingBall_card_eq_zero ] )

/-- **MacWilliams–Sloane, Ch. 1, Theorem 12: the Gilbert–Varshamov bound**
(explicit form).  There is a `d`-separated finset `S` of words in `F^n` with
`q^n ≤ |S| · V_q(n, d-1)`, i.e. `|S| ≥ q^n / V_q(n, d-1)`. -/
theorem gilbert_varshamov_bound (d : ℕ) :
    ∃ S : Finset (ι → F), IsSeparated d S ∧
      Fintype.card F ^ Fintype.card ι
        ≤ S.card * hammingBallVolume (Fintype.card ι) (Fintype.card F) (d - 1) := by
  convert gilbert_varshamov_bound_card d;
  convert rfl;
  convert Fintype.card_fun;
  convert hammingBall_card ( 0 : ι → F ) ( d - 1 ) |> Eq.symm

end LinearCode

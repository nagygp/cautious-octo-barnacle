import CodeTheoryCryptoEquiv.CodingTheory.SpherePacking

/-!
# The Gilbert–Varshamov bound

This module continues the coding-theory development of
`CodeTheoryCryptoEquiv/CodingTheory/LinearCode.lean` and
`CodeTheoryCryptoEquiv/CodingTheory/SpherePacking.lean`, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977.

It implements §1.4 of `CODING_THEORY_DIRECTIONS.md`: the **Gilbert–Varshamov
bound** (MacWilliams–Sloane, Ch. 1, Theorem 12).  Over a finite field `F` with
`q = #F` elements and a length `n = #ι`, there exists a set `S` of words that is
`d`-separated (any two distinct words of `S` are at Hamming distance at least `d`)
and large:

```
  q^n ≤ |S| · V_q(n, d-1),    where    V_q(n, r) = Σ_{i=0}^{r} C(n,i) (q-1)^i,
```

equivalently `|S| ≥ q^n / V_q(n, d-1)`.  The proof is the classical greedy /
maximal-packing argument: take a `d`-separated set of maximum size; by
maximality its balls of radius `d-1` cover the whole space, giving the bound.

We keep the conventions of the foundational modules: words live in `ι → F` with
`[Fintype ι] [Field F] [Fintype F]`.

## Main definitions

* `IsSeparated d S` — the set `S` of words is `d`-separated: any two distinct
  members are at Hamming distance `≥ d`.

## Main results

* `exists_maximal_separated` — a `d`-separated finset of maximum cardinality
  exists.
* `gilbert_varshamov_covering` — its balls of radius `d-1` cover the whole space.
* `gilbert_varshamov_bound` — **MacWilliams–Sloane, Ch. 1, Theorem 12**: there is
  a `d`-separated finset `S` with `q^n ≤ |S| · V_q(n, d-1)`.

## References

* MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 1, §6.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- A finset of words is **`d`-separated** when any two distinct members are at
Hamming distance at least `d`. -/
def IsSeparated (d : ℕ) (S : Finset (ι → F)) : Prop :=
  (↑S : Set (ι → F)).Pairwise (fun x y => d ≤ hammingDist x y)

/-
There exists a `d`-separated finset of maximum cardinality (the ambient space
is finite, and the empty set is `d`-separated).
-/
omit [Field F] in
theorem exists_maximal_separated (d : ℕ) :
    ∃ S : Finset (ι → F), IsSeparated d S ∧
      ∀ T : Finset (ι → F), IsSeparated d T → T.card ≤ S.card := by
  obtain ⟨S, hS⟩ : ∃ S ∈ Finset.filter (fun S : Finset (ι → F) => IsSeparated d S) (Finset.univ : Finset (Finset (ι → F))), ∀ T ∈ Finset.filter (fun S : Finset (ι → F) => IsSeparated d S) (Finset.univ : Finset (Finset (ι → F))), #T ≤ #S := by
    apply_rules [ Finset.exists_max_image ];
    exact ⟨ ∅, by simp +decide [ IsSeparated ] ⟩;
  aesop

/-
**Covering by a maximal packing.** If `S` is a `d`-separated finset of maximum
cardinality, then every word is within Hamming distance `d-1` of some member of
`S`; otherwise such a word could be added, contradicting maximality.
-/
omit [Field F] [Fintype F] in
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

/-
**MacWilliams–Sloane, Ch. 1, Theorem 12: the Gilbert–Varshamov bound**
(abstract ball-cardinality form).  There is a `d`-separated finset `S` whose
balls of radius `d-1` cover the space, so `q^n ≤ |S| · #(ball of radius d-1)`.
-/
theorem gilbert_varshamov_bound_card (d : ℕ) :
    ∃ S : Finset (ι → F), IsSeparated d S ∧
      Fintype.card (ι → F) ≤ S.card * (hammingBall (0 : ι → F) (d - 1)).card := by
  -- By `exists_maximal_separated`, there exists a maximal `d`-separated finset `S`.
  obtain ⟨S, hS⟩ : ∃ S : Finset (ι → F), IsSeparated d S ∧ ∀ T : Finset (ι → F), IsSeparated d T → T.card ≤ S.card := exists_maximal_separated d;
  refine' ⟨ S, hS.1, _ ⟩;
  -- Every word is within distance `d-1` of some member of `S`.
  have h_cover : ∀ z : ι → F, ∃ c ∈ S, hammingDist z c ≤ d - 1 := by
    exact gilbert_varshamov_covering hS.1 hS.2;
  -- Therefore, the union of the balls of radius `d-1` around the members of `S` covers the entire space.
  have h_union_cover : Finset.univ ⊆ Finset.biUnion S (fun c => hammingBall c (d - 1)) := by
    exact fun x _ => by obtain ⟨ c, hc₁, hc₂ ⟩ := h_cover x; exact Finset.mem_biUnion.mpr ⟨ c, hc₁, by simpa using hc₂ ⟩ ;
  refine' le_trans ( Finset.card_le_card h_union_cover ) _;
  exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_card_nsmul _ _ _ fun x hx => by rw [ hammingBall_card_eq_zero ] )

/-
**MacWilliams–Sloane, Ch. 1, Theorem 12: the Gilbert–Varshamov bound**
(explicit form).  There is a `d`-separated finset `S` of words in `F^n` with
`q^n ≤ |S| · V_q(n, d-1)`, i.e. `|S| ≥ q^n / V_q(n, d-1)`.
-/
theorem gilbert_varshamov_bound (d : ℕ) :
    ∃ S : Finset (ι → F), IsSeparated d S ∧
      Fintype.card F ^ Fintype.card ι
        ≤ S.card * hammingBallVolume (Fintype.card ι) (Fintype.card F) (d - 1) := by
  convert gilbert_varshamov_bound_card d;
  convert rfl;
  convert Fintype.card_fun;
  convert hammingBall_card ( 0 : ι → F ) ( d - 1 ) |> Eq.symm

end CodingTheory
import Mathlib
/-!
# Chapter 3 — Binary Codes and m-Tuple Counts

## What this chapter builds

We introduce **binary linear codes** — the coding-theory objects
that sit at the other end of the "Rosetta Stone" bridge from
spectral theory.

The central result is the **m-tuple count formula**:

> For any binary linear code C, the number of m-tuples of codewords
> summing to zero is exactly |C|^{m−1}.

This is a genuinely nontrivial theorem proved by induction, using
the GF(2) linearity property that −x = x (every element is its own
inverse in characteristic 2).

## Why this matters

The m-tuple count is the coding-theory analogue of the spectral
power sum. The Rosetta Stone theorem (Chapter 5) will connect them:
the spectral side (bent spectrum) and the coding side (m-tuple count)
are measuring the same underlying combinatorial invariant.

## Key results

- `weightDistribution_zero`: The zero codeword is the unique word
  of weight 0 (A₀ = 1)
- `weightDistribution_sum`: The weight distribution sums to |C|
  (partition of codewords by weight)
- `mTupleCount_eq_card_pow`: κ_m(C) = |C|^{m−1} (THE main theorem)
- `mtuple_rigidity_from_card`: Same |C| ⟹ same κ_m (rigidity)
-/

open Finset BigOperators

set_option maxHeartbeats 800000

noncomputable section

/-! ## §1 Binary Codes — The Basic Definitions

A **binary linear code** of length n is a set of binary vectors
(elements of GF(2)^n) that:
1. Contains the zero vector
2. Is closed under addition (if c₁, c₂ are codewords, so is c₁ + c₂)

These two properties make it a subgroup of GF(2)^n.
-/

/-- **Hamming weight**: the number of nonzero coordinates in a binary
    vector. Measures how far the vector is from the zero vector. -/
def hammingWeight (n : ℕ) (v : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- A **binary linear code** of length n: a finite set of binary
    vectors containing 0 and closed under addition.

    - `codewords` = the set of valid codewords
    - `zero_mem` = the all-zeros vector is a codeword
    - `add_mem` = sum of two codewords is a codeword -/
structure BinaryCode (n : ℕ) where
  /-- The set of codewords ⊆ GF(2)^n -/
  codewords : Finset (Fin n → ZMod 2)
  /-- The zero vector is always a codeword -/
  zero_mem : (fun _ => 0) ∈ codewords
  /-- The code is closed under coordinate-wise addition -/
  add_mem : ∀ c₁ c₂, c₁ ∈ codewords → c₂ ∈ codewords →
    (fun i => c₁ i + c₂ i) ∈ codewords

/-! ## §2 Weight Distribution

The **weight distribution** of a code records how many codewords
have each possible Hamming weight. It's like a histogram of distances
from the origin.
-/

/-- Number of codewords of Hamming weight `w`. -/
def weightDistribution {n : ℕ} (C : BinaryCode n) (w : ℕ) : ℕ :=
  (C.codewords.filter (fun c => hammingWeight n c = w)).card

/-- **Lemma A₀ = 1**: There is exactly one codeword of weight 0 — the
    zero vector itself.

    This is because the zero vector is the ONLY vector with all
    coordinates equal to zero. -/
theorem weightDistribution_zero {n : ℕ} (C : BinaryCode n) :
    weightDistribution C 0 = 1 := by
  refine Finset.card_eq_one.mpr ?_
  use fun _ => 0; ext; simp [hammingWeight]
  exact ⟨fun h => funext h.2, fun h => ⟨h ▸ C.zero_mem, fun _ => h ▸ rfl⟩⟩

/-- **Lemma Σ Aᵥ = |C|**: The total weight distribution sums to the
    number of codewords — every codeword has some weight. -/
theorem weightDistribution_sum {n : ℕ} (C : BinaryCode n) :
    ∑ w ∈ Finset.range (n + 1), weightDistribution C w = C.codewords.card := by
  unfold weightDistribution
  rw [← Finset.card_eq_sum_card_fiberwise]
  exact fun x hx => Finset.mem_range_succ_iff.mpr
    (le_trans (Finset.card_le_univ _) (by norm_num))

/-! ## §3 m-Tuple Counts — The Central Object

The **m-tuple count** κ_m(C) is the number of ways to choose m
codewords that sum to zero:

    κ_m(C) = |{ (c₁, ..., c_m) ∈ C^m | c₁ + ⋯ + c_m = 0 }|

This is the coding-theory quantity that will be connected to spectral
invariants via the Rosetta Stone theorem.
-/

/-- The **m-tuple count**: number of m-tuples of codewords whose
    coordinate-wise sum is the zero vector.

    κ_m(C) = |{ (c₁, ..., cₘ) ∈ C^m | Σᵢ cⱼ = 0 }| -/
def mTupleCount {n : ℕ} (C : BinaryCode n) (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun (v : Fin m → C.codewords) =>
    ∀ (i : Fin n), ∑ j, (v j : Fin n → ZMod 2) i = 0)).card

/-! ## §4 The m-Tuple Count Formula

**THE MAIN THEOREM**: κ_m(C) = |C|^{m−1} for m ≥ 1.

**Proof idea**: By induction on m.
- Base case (m = 1): The only 1-tuple summing to zero is (0,...,0),
  and there's exactly one: the zero codeword. So κ₁ = 1 = |C|⁰.
- Inductive step (m → m+1): Choose c₁, ..., cₘ freely (|C|^m choices).
  Then c_{m+1} is *determined* as −(c₁ + ⋯ + cₘ). In GF(2), −x = x,
  and the sum c₁ + ⋯ + cₘ is in C by linearity (closure under addition).
  So each of the |C|^m free choices gives exactly one valid (m+1)-tuple.
  Hence κ_{m+1} = |C|^m = |C|^{(m+1)−1}. ∎

**Key GF(2) fact used**: In GF(2), every element is its own additive
inverse: −x = x. This means "sum = 0" is the same as "last element =
sum of the others", and the sum of codewords is always a codeword.
-/

/-- The sum of any subset of codewords is itself a codeword
    (by closure under addition). -/
private lemma sum_codewords_mem {n : ℕ} (C : BinaryCode n) (m : ℕ)
    (v : Fin m → C.codewords) (S : Finset (Fin m)) :
    (fun i => ∑ j ∈ S, (v j : Fin n → ZMod 2) i) ∈ C.codewords := by
  induction S using Finset.induction with
  | empty => simpa using C.zero_mem
  | insert j S hj ih =>
    convert C.add_mem _ _ ih (v j).2 using 1
    exact funext fun i => by rw [Finset.sum_insert hj, add_comm]

/-- **THE m-TUPLE COUNT FORMULA**: For any binary linear code C and
    m ≥ 1, the m-tuple count equals |C|^{m−1}.

    κ_m(C) = |C|^{m−1}

    This is the central theorem connecting coding theory to the
    spectral framework. -/
theorem mTupleCount_eq_card_pow {n : ℕ} (C : BinaryCode n) (m : ℕ)
    (hm : m ≥ 1) :
    mTupleCount C m = C.codewords.card ^ (m - 1) := by
  induction hm <;> simp_all +decide [mTupleCount]
  · rw [Finset.card_eq_one]
    use fun _ => ⟨fun _ => 0, C.zero_mem⟩
    ext v; simp [funext_iff]
    exact ⟨fun h => Subtype.ext <| funext h, fun h => h.symm ▸ fun _ => rfl⟩
  · rename_i k hk ih
    have h_split :
        Finset.card (Finset.filter
          (fun v : Fin (k + 1) → C.codewords =>
            ∀ i, ∑ j, (v j : Fin n → ZMod 2) i = 0)
          Finset.univ) =
        Finset.card (Finset.univ : Finset (Fin k → C.codewords)) := by
      refine Finset.card_bij ?_ ?_ ?_ ?_
      use fun a _ => fun i => a (Fin.castSucc i)
      · grind +qlia
      · simp +contextual [funext_iff]
        intro a₁ ha₁ a₂ ha₂ h x
        induction x using Fin.lastCases <;>
          simp_all +decide [Fin.sum_univ_castSucc]
        ext i; specialize ha₁ i; specialize ha₂ i
        simp_all +decide [← eq_sub_iff_add_eq']
      · intro b _
        use Fin.snoc b (⟨fun i => ∑ j, (b j : Fin n → ZMod 2) i, by
          convert sum_codewords_mem C k b Finset.univ using 1⟩ : C.codewords)
        generalize_proofs at *
        simp +decide [Fin.sum_univ_castSucc]
        grobner
    simp_all +decide [Finset.card_univ]

/-! ## §5 Rigidity from Cardinality

A beautiful consequence of the m-tuple formula: the m-tuple count
depends ONLY on |C|, nothing else about the code structure.

Two codes with the same number of codewords automatically have the
same m-tuple count — regardless of their weight distributions,
minimum distances, or any other structural properties.

This is the coding-theory version of "spectral rigidity."
-/

/-- **RIGIDITY THEOREM**: Two codes with the same cardinality have
    identical m-tuple counts.

    This is because κ_m = |C|^{m−1}, which depends only on |C|. -/
theorem mtuple_rigidity_from_card {n : ℕ}
    (C₁ C₂ : BinaryCode n)
    (hcard : C₁.codewords.card = C₂.codewords.card)
    (m : ℕ) (hm : m ≥ 1) :
    mTupleCount C₁ m = mTupleCount C₂ m := by
  rw [mTupleCount_eq_card_pow C₁ m hm, mTupleCount_eq_card_pow C₂ m hm, hcard]

end

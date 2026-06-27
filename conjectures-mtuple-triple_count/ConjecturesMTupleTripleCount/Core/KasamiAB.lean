import ConjecturesMTupleTripleCount.Walsh.WalshAB
import ConjecturesMTupleTripleCount.Core.KasamiEvenK
import ConjecturesMTupleTripleCount.Core.CrossFormAnalysis
import ConjecturesMTupleTripleCount.Core.KasamiWalshDiv

/-!
# Kasami Almost Bent (AB) Theorem

## Main Result

The Kasami power function `x ↦ x^d` with `d = 2^{2k} − 2^k + 1` is
**Almost Bent (AB)** on `GF(2ⁿ)` when:
- `n` is odd
- `gcd(k, n) = 1`
- `k ≥ 1`

This follows from the moment method (`WalshAB.ab_from_moments`): a power
permutation whose Walsh squares satisfy the Parseval (L²) and fourth-moment
(L⁴) constraints and are divisible by `2^{(n+1)/2}` takes Walsh-square values in
`{0, 2^{n+1}}`, i.e. is AB.

## Proof Architecture (DAG)

```
kasami_is_ab
  └── ab_from_moments (WalshAB: moment method for power perms, n odd)
        ├── parseval_perm           (Parseval / Plancherel, needs bijectivity)
        ├── fourth_moment_apn       (fourth moment for APN power perms)
        └── KasamiWalshDiv.kasami_walsh_div
                                    (Walsh divisibility via the quadratic substitution)

  where the two side conditions are
  ├── kasami_is_apn_pred           (Kasami is APN, count form)
  │     └── KasamiEvenK.kasami_is_apn_general / kasami_one_is_apn
  │           (first-principles collision form, via KasamiAPN)
  └── kasami_bijective             (Kasami is a permutation)
        └── kasami_d_coprime ← d_coprime_card_sub_one (gcd(d, 2ⁿ-1) = 1)
```

The abstract reformulation of the APN side in terms of differential uniformity
lives in `ConjecturesMTupleTripleCount/DiffUniformity/KasamiDiffUniformity.lean`
(`APNLib.kasami_isAPN_diffUnif`).

## Categorical Perspective

The Kasami AB theorem demonstrates a deep connection between:
- **Differential uniformity** (APN): a combinatorial property
- **Walsh spectrum** (AB): a spectral/harmonic-analytic property

This connection is mediated by the **Pontryagin self-duality** of `(GF(2ⁿ), +)`:
the trace pairing establishes an isomorphism `F ≅ F̂` between the group
and its character group. Under this Morita equivalence:
- The differential operator `D_a f(x) = f(x+a) + f(x)` on the primal side
  corresponds to multiplication by the Walsh coefficient on the dual side
- Parseval transfers L² norms between the two sides
- The fourth moment identity transfers the differential uniformity constraint
  to a spectral constraint

For `n` odd, the additional structure of `GF(2ⁿ)` (no element of order 2
in the extension degree) forces the spectral constraint to be sharp,
yielding the AB property.
-/

set_option maxHeartbeats 800000

namespace KasamiAB

open Finset Fintype CollisionAnalysis WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## Layer K1: Kasami Function is a Permutation

The power map x ↦ x^d is a bijection on F when gcd(d, |F|-1) = 1.
This was already established in CrossFormAnalysis.lean via d_coprime_card_sub_one.
-/

/-- The Kasami power map is injective (hence bijective on a finite set). -/
theorem kasami_injective {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) : Function.Injective (fun x : F => x ^ d k) := by
  intro x y (hxy : x ^ d k = y ^ d k)
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (ne_of_gt (d_pos k hk))] at hxy
    by_contra hy
    exact (pow_ne_zero _ (Ne.symm hy)) hxy.symm
  · by_cases hy : y = 0
    · subst hy
      rw [zero_pow (ne_of_gt (d_pos k hk))] at hxy
      exact absurd hxy (pow_ne_zero _ hx)
    · exact pow_d_injective hcard k hk hcop hnodd hn x y hx hy hxy

/-- The Kasami power map is bijective on F. -/
theorem kasami_bijective {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) : Function.Bijective (fun x : F => x ^ d k) :=
  (Finite.injective_iff_bijective).mp (kasami_injective hcard k hk hcop hnodd hn)

/-! ## Layer K2: Kasami is APN (from CrossPairProof)

This was proved (modulo mcm_inj_core) in CrossPairProof.lean.
We repackage it in terms of the IsAPN predicate.
-/

/-
The collision-form APN predicate (`KasamiAPN.IsAPN`) implies the
count-form APN predicate (`WalshAB.IsAPN`): if every derivative collision
`f(x+a)+f(x) = f(y+a)+f(y)` forces `y ∈ {x, x+a}`, then each derivative fibre
has at most two points.
-/
lemma count_apn_of_collision_apn {f : F → F} (h : KasamiAPN.IsAPN f) :
    IsAPN f := by
  intro a ha b;
  contrapose! h;
  obtain ⟨ x₁, x₂, x₃, h₁, h₂, h₃ ⟩ := Fintype.two_lt_card_iff.mp h;
  simp_all +decide [ KasamiAPN.IsAPN ];
  grind

/-- Kasami is APN (reformulated using the count-form `IsAPN`), discharged via the
`sorry`-free Kasami-APN proof in `KasamiEvenK` (no dependence on the
`CrossPairProof`/Cohen–Matthews chain). -/
theorem kasami_is_apn_pred {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) : IsAPN (fun x : F => x ^ d k) := by
  apply count_apn_of_collision_apn
  show KasamiAPN.IsAPN (fun x : F => x ^ KasamiAPN.kasamiExp k)
  rcases eq_or_lt_of_le hk with hk1 | hk1
  · subst hk1; exact KasamiEvenK.kasami_one_is_apn hcard hcop
  · exact KasamiEvenK.kasami_is_apn_general hcard k hk1 hkn hnodd hcop

/-! ## Layer K3: Kasami d coprimality with |F| - 1

The Kasami exponent d(k) is coprime to 2^n - 1 under the Kasami conditions.
This was proved in CrossFormAnalysis.lean.
-/

/-- d(k) is coprime to |F| - 1. -/
theorem kasami_d_coprime {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : 0 < n) : Nat.Coprime (d k) (Fintype.card F - 1) :=
  d_coprime_card_sub_one hcard k hk hcop hnodd hn

/-! ## Layer K4: Assembly — Kasami is AB

Combining:
1. Kasami is APN (Layer K2)
2. Kasami is a permutation (Layer K1)
3. Nyberg's theorem: APN power perm + n odd ⟹ AB (WalshAB.lean)
-/

/-- **Kasami AB Theorem**: The Kasami power function x^d is Almost Bent.

The Walsh-divisibility input is the quadratic-substitution lemma
`KasamiWalshDiv.kasami_walsh_div` (divisibility holds for the Kasami exponent;
it is *not* true for arbitrary coprime exponents). -/
theorem kasami_is_ab {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) : IsAB hcard (fun x : F => x ^ d k) := by
  apply ab_from_moments hcard _ hnodd hn
  · exact fun a ha => parseval_perm hcard _ (kasami_bijective hcard k hk hcop hnodd hn) a ha
  · exact fun a ha => fourth_moment_apn hcard (d k)
      (kasami_bijective hcard k hk hcop hnodd hn)
      (kasami_is_apn_pred hcard k hk hkn hcop hnodd hn) a ha
  · exact fun a b => KasamiWalshDiv.kasami_walsh_div hcard k hk hcop hnodd hn a b

end KasamiAB
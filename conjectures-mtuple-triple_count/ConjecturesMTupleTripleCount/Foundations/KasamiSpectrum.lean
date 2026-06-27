import ConjecturesMTupleTripleCount.Foundations.ABSpectrum
import ConjecturesMTupleTripleCount.Core.KasamiAB

/-!
# Foundations, Layer 5 — the three-valued spectrum of the Kasami map

This module specializes the abstract Layer 5 results
(`ConjecturesMTupleTripleCount/Foundations/ABSpectrum.lean`) to the **Kasami power map**
`x ↦ x ^ d k`, completing the bridge promised by the roadmap
(`Docs/VanishFutureDirections.md`): "from `kasami_is_ab` (already proved) to a
usable spectrum".

Under the standing Kasami hypotheses (`1 ≤ k < n`, `gcd(k, n) = 1`, `n` odd),
the Kasami map is an AB permutation fixing `0`, so its Walsh spectrum at any
fixed nonzero `a` is three-valued with the full classical distribution:

* `kasami_walsh_three_valued` — `W(a,b) ∈ {0, ±2^{(n+1)/2}}`;
* `kasami_walsh_zero_count` — `#{b : W = 0} = 2^{n-1}`;
* `kasami_walsh_support_count` — `#{W = +} + #{W = -} = 2^{n-1}`;
* `kasami_walsh_signed_count` — `#{W = +} − #{W = -} = 2^{(n-1)/2}`.

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): no new mathematics here — these
are thin, single-responsibility specializations that *reuse* the abstract bridge
and the already-proved `KasamiAB.kasami_is_ab` / `KasamiAB.kasami_bijective`
(DRY).
-/

namespace Vanish.Foundations

open Finset BigOperators WalshAB CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
/-- The Kasami map fixes `0` (since the Kasami exponent `d k ≥ 1`). -/
theorem kasami_apply_zero (k : ℕ) : (fun x : F => x ^ d k) 0 = 0 := by
  have hd : d k ≠ 0 := by unfold CollisionAnalysis.d; omega
  simp [zero_pow hd]

variable {n k : ℕ} (hcard : Fintype.card F = 2 ^ n)
  (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n)

include hcard hk hkn hcop hnodd hn

/-- **Three-valued Kasami Walsh spectrum.**  For the Kasami map on `GF(2ⁿ)`
(`1 ≤ k < n`, `gcd(k,n)=1`, `n` odd) and any nonzero `a`,
`W(a,b) ∈ {0, 2^{(n+1)/2}, -2^{(n+1)/2}}`. -/
theorem kasami_walsh_three_valued (a : F) (ha : a ≠ 0) (b : F) :
    walsh (fun x : F => x ^ d k) a b = 0
      ∨ walsh (fun x : F => x ^ d k) a b = 2 ^ ((n + 1) / 2)
      ∨ walsh (fun x : F => x ^ d k) a b = -2 ^ ((n + 1) / 2) :=
  walsh_three_valued hcard hnodd
    (KasamiAB.kasami_is_ab hcard k hk hkn hcop hnodd hn) a ha b

/-- **Kasami zero count.**  `#{b : W(a,b) = 0} = 2^{n-1}`. -/
theorem kasami_walsh_zero_count (a : F) (ha : a ≠ 0) :
    ((univ.filter (fun b : F => walsh (fun x : F => x ^ d k) a b = 0)).card : ℤ)
      = 2 ^ (n - 1) :=
  walsh_zero_count hcard hnodd hn
    (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn)
    (KasamiAB.kasami_is_ab hcard k hk hkn hcop hnodd hn) a ha

/-- **Kasami support count.**  `#{W = 2^{(n+1)/2}} + #{W = -2^{(n+1)/2}} = 2^{n-1}`. -/
theorem kasami_walsh_support_count (a : F) (ha : a ≠ 0) :
    ((univ.filter
        (fun b : F => walsh (fun x : F => x ^ d k) a b = 2 ^ ((n + 1) / 2))).card : ℤ)
      + ((univ.filter
          (fun b : F => walsh (fun x : F => x ^ d k) a b = -2 ^ ((n + 1) / 2))).card : ℤ)
      = 2 ^ (n - 1) :=
  walsh_support_count hcard hnodd hn
    (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn)
    (KasamiAB.kasami_is_ab hcard k hk hkn hcop hnodd hn) a ha

/-- **Kasami signed count.**  `#{W = 2^{(n+1)/2}} − #{W = -2^{(n+1)/2}} = 2^{(n-1)/2}`. -/
theorem kasami_walsh_signed_count (a : F) (ha : a ≠ 0) :
    ((univ.filter
        (fun b : F => walsh (fun x : F => x ^ d k) a b = 2 ^ ((n + 1) / 2))).card : ℤ)
      - ((univ.filter
          (fun b : F => walsh (fun x : F => x ^ d k) a b = -2 ^ ((n + 1) / 2))).card : ℤ)
      = 2 ^ ((n - 1) / 2) :=
  walsh_signed_count hcard hnodd
    (KasamiAB.kasami_bijective hcard k hk hcop hnodd hn)
    (kasami_apply_zero k)
    (KasamiAB.kasami_is_ab hcard k hk hkn hcop hnodd hn) a ha

end Vanish.Foundations

import Mathlib
import RequestProject.Core.KasamiAPN
import RequestProject.Dobbertin1999.MCM

/-!
# Dobbertin (1999) — the MCM → APN chain

This module is the **MCM → APN** part of the transcription of Dobbertin (1999),
*"Kasami Power Functions, Permutation Polynomials and Cyclic Difference Sets"*.
It records the bridge, used in the proof of **Corollary 2**, from the
Müller–Cohen–Matthews permutation theorem (`Dobbertin1999.MCM`) to the
almost-perfect-nonlinearity of the Kasami power map.  Everything is proved by
*reusing* the project's Kasami development (`RequestProject/Core/KasamiAPN.lean`);
nothing is left as `sorry`.

## The paper's argument (proof of Corollary 2)

Fix the Kasami exponent `d = 2^{2k} − 2^k + 1`.  Dobbertin proves the Kasami
power function `x ↦ x^d` is APN by the chain:

1. **Key identity.**  With `q = 2^k`, for every `x`,
   ```
   ((x+1)^d + x^d + 1) · (x² + x)^{2^k}  =  (x^{2^k} + x)^{2^k + 1}.       (key)
   ```
   This is a routine but essential computation linking the Kasami *derivative*
   `(x+1)^d + x^d + 1` to the truncated trace applied to `x² + x`
   (Artin–Schreier: `L_k(x² + x) = x^{2^k} + x`).

2. **Gold permutation.**  The map `y ↦ y^{2^k + 1}` is a bijection of `𝔽_{2ⁿ}`
   when `gcd(k, n) = 1` and `n` is odd (`gcd(2^k+1, 2ⁿ−1) = 1`).

3. **MCM permutation.**  With `q = qα` chosen a permutation polynomial
   (Theorem 1 / the MCM engine `Dobbertin1999.MCM.mcm_permutation_ktransfer`),
   one has `p(t) = 1/q(t^{2^k} + t)`, and the composite

   > (MCM permutation `L_k(·)·(·)^{k'}`) ∘ (Gold permutation `y^{2^k+1}`)

   is a bijection.  Feeding the key identity through this bijection shows the
   Kasami derivative is injective on the fibres of `u ↦ u^2 + u`.

4. **Two-to-one collapse.**  Since `t ↦ t^{2^k} + t` is two-to-one
   (`gcd(k, n) = 1`), a collision of the Kasami derivative forces `x² + x = y² + y`,
   i.e. `y ∈ {x, x+1}` for the normalized derivative — which is the APN property.

## Contents

* `kasamiExp` — the Kasami exponent `d = 2^{2k} − 2^k + 1` (re-exported).
* `truncTrace_artin_schreier` — `L_k(x² + x) = x^{2^k} + x`.
* `kasami_key_identity` — the identity `(key)` above.
* `gold_permutation` — `y ↦ y^{2^k+1}` is a bijection (the Gold step).
* `mcm_injective_bridge` — the composite MCM ∘ Gold injectivity that transports
  the MCM permutation property to the Kasami derivative.
* `kasami_collision_forces_equal_u` — a Kasami derivative collision forces
  `x² + x = y² + y`, the heart of the MCM → APN reduction.
-/

namespace Dobbertin1999.MCMtoAPN

open DempwolffMueller

/-- The **Kasami exponent** `d = 2^{2k} − 2^k + 1`.  Re-exported from
`KasamiAPN.kasamiExp`. -/
abbrev kasamiExp (k : ℕ) : ℕ := KasamiAPN.kasamiExp k

/-- **Artin–Schreier telescoping** (`L_k(x² + x) = x^{2^k} + x`).

The truncated trace applied to `x² + x` telescopes to `x^{2^k} + x`; this is the
identity that ties the Kasami derivative to the linearized trace.  Reuses
`KasamiAPN.truncTrace_artin_schreier`. -/
theorem truncTrace_artin_schreier {F : Type*} [CommRing F] [CharP F 2]
    (k : ℕ) (x : F) :
    DempwolffMueller.truncTrace k (x ^ 2 + x) = x ^ (2 ^ k) + x :=
  KasamiAPN.truncTrace_artin_schreier k x

/-- **The key identity (Dobbertin 1999, Corollary 2 proof).**

With `q = 2^k`, for every `x ∈ 𝔽_{2ⁿ}` (`0 < k < n`),
```
   ((x+1)^d + x^d + 1) · (x² + x)^{2^k}  =  (x^{2^k} + x)^{2^k + 1},
```
where `d = 2^{2k} − 2^k + 1`.  This links the Kasami derivative to the Gold
exponent `2^k + 1` applied to `x^{2^k} + x = L_k(x² + x)`.  Reuses
`KasamiAPN.kasami_key_identity`. -/
theorem kasami_key_identity {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hkn : k < n) (x : F) :
    ((x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1) * (x ^ 2 + x) ^ (2 ^ k) =
    (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) :=
  KasamiAPN.kasami_key_identity hn k hk hkn x

/-- **The Gold permutation.**

`y ↦ y^{2^k + 1}` is a bijection of `𝔽_{2ⁿ}` when `0 < k`, `n` is odd and
`gcd(k, n) = 1` (equivalently `gcd(2^k + 1, 2ⁿ − 1) = 1`).  This is the second
factor of the MCM ∘ Gold composite.  Reuses `KasamiAPN.gold_pow_bijective`. -/
theorem gold_permutation {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hn_pos : 0 < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    Function.Bijective (fun y : F => y ^ (2 ^ k + 1)) :=
  KasamiAPN.gold_pow_bijective hn k hk hn_pos hcop hn_odd

/-- **MCM ∘ Gold injectivity bridge.**

The core transport step: on nonzero `u, v`, the equality
```
   L_k(u)^{2^k+1} · v^{2^k}  =  L_k(v)^{2^k+1} · u^{2^k}
```
forces `u = v`.  This is exactly where the MCM permutation theorem
(`Dobbertin1999.MCM`) enters: writing the left-hand map as the composite of the
Gold permutation `y ↦ y^{2^k+1}` with the MCM permutation `x ↦ L_k(x)·x^{k'}`
(both bijective), injectivity follows.  Reuses `KasamiAPN.phi_injective_on_units`. -/
theorem mcm_injective_bridge {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (heq : DempwolffMueller.truncTrace k u ^ (2 ^ k + 1) * v ^ (2 ^ k) =
           DempwolffMueller.truncTrace k v ^ (2 ^ k + 1) * u ^ (2 ^ k)) :
    u = v :=
  KasamiAPN.phi_injective_on_units hn k hk hk_odd hkn hn_odd hcop hu hv heq

/-- **Collision ⟹ equal fibre (the MCM → APN reduction).**

If the normalized Kasami derivatives at `x` and `y` agree,
```
   (x+1)^d + x^d  =  (y+1)^d + y^d,
```
then `x² + x = y² + y`.  Combined with the fact that `u ↦ u² + u` is two-to-one
in characteristic two, this yields `y ∈ {x, x+1}`, i.e. the APN property of
Corollary 2.  Reuses `KasamiAPN.kasami_collision_forces_equal_u`. -/
theorem kasami_collision_forces_equal_u {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    {x y : F}
    (hdiff : (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) =
             (y + 1) ^ (kasamiExp k) + y ^ (kasamiExp k)) :
    x ^ 2 + x = y ^ 2 + y :=
  KasamiAPN.kasami_collision_forces_equal_u hn k hk hk_odd hkn hn_odd hcop hdiff

end Dobbertin1999.MCMtoAPN

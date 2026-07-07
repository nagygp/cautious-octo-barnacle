import RequestProject.MTuple.VanishCriterion
import RequestProject.Foundations.KasamiA1PreCount4Disproof
import RequestProject.Core.KasamiAB

/-!
# A fully unconditional, end-to-end m-tuple count instance (no hypotheses)

This module demonstrates that the m-tuple count proof path is *complete* — it can
be discharged end-to-end with **no** literature hypothesis (`hWK`, `hsign`,
three-valuedness, `2q³`, `FlatSpectrum`, …) and **no** `sorry` — by combining:

* the genuine, computable admissibility criterion
  `MTuple.imgCount_of_preCount` (from `VanishCriterion.lean`), and
* a direct `native_decide` evaluation of the (decidable) preimage count over a
  concrete field.

We take `F = GF(8)` (the computable model built in
`RequestProject/Foundations/KasamiA1PreCount4Disproof.lean`), the Gold/Kasami
cube map `f = x³ = x^{d 1}` (APN via the project's `kasami_is_apn_pred`), shift
`a = 1`, and the admissible coefficient triple `c = (1, 2, 3)` (as elements of
`GF(8) = Fin 8`).  Everything is verified by kernel/`native_decide`:

* `preCount_eq_pow`  — the preimage triple count is generic, `preCount = 2^{(3-1)·3} = 64`;
* `imgCount_eq`      — hence the image triple count is `2^{2·3-3} = 8`,

with **no hypotheses** and **no `sorry`**.  This is the bottom-up completion of the
count for a concrete Kasami instance: the derivative autocorrelation's value set is
never invoked; the count follows purely from the (green) Fourier-inversion identity
and a decidable preimage count.
-/

namespace MTuple.VanishInstance

open Kasami.PreCount4Disproof MTuple WalshAB

/-- The admissible coefficient triple `c = (1, 2, 3)` over `GF(8) = Fin 8`. -/
def c3 : Fin 3 → GF8 := ![(⟨1, by decide⟩ : GF8), ⟨2, by decide⟩, ⟨3, by decide⟩]

/-- A computable mirror of the (noncomputable) `preCount` for this instance. -/
def preCount3Comp : ℕ :=
  (Finset.univ.filter (fun x : Fin 3 → GF8 =>
    ∑ i, c3 i * MTuple.deriv (fun x : GF8 => x ^ 3) 1 (x i) = 0)).card

/-- The Gold/Kasami cube map `x ↦ x³` is APN over `GF(8)` (from the project's
`kasami_is_apn_pred`, `k = 1`, `d 1 = 3`). -/
theorem cube_apn : IsAPN (fun x : GF8 => x ^ 3) :=
  KasamiAB.kasami_is_apn_pred (F := GF8) GF8.card_eq 1 (le_refl 1)
    (by norm_num) (by decide) (by decide) (by norm_num)

/-- **The preimage triple count is generic** (`= 2^{(3-1)·3} = 64`), verified by
`native_decide` over the `8³` tuples.  Equivalently, the admissibility criterion
`Vanish` holds for `c = (1,2,3)` — with no spectral input. -/
theorem preCount_eq_pow :
    MTuple.preCount 3 (fun x : GF8 => x ^ 3) 1 c3 = 2 ^ ((3 - 1) * 3) := by
  show preCount3Comp = 2 ^ ((3 - 1) * 3)
  native_decide

/-- **The unconditional Kasami triple count over `GF(8)`.**  With no hypotheses at
all, the image triple count of the cube map's derivative at the admissible triple
`c = (1,2,3)` is `2^{2·3-3} = 8`.  Assembled from the computable criterion
`imgCount_of_preCount` and the decidable `preCount_eq_pow`. -/
theorem imgCount_eq :
    MTuple.imgCount 3 (fun x : GF8 => x ^ 3) 1 c3 = 2 ^ (2 * 3 - 3) := by
  have h := MTuple.imgCount_of_preCount 3 3 (by norm_num) (by norm_num)
    (fun x : GF8 => x ^ 3) cube_apn 1 (by decide) c3 preCount_eq_pow
  simpa using h

end MTuple.VanishInstance

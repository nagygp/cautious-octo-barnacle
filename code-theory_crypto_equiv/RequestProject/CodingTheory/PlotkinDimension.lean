import Mathlib
import RequestProject.CodingTheory.PlotkinConstruction

/-!
# Dimension of the `(u | u+v)` (Plotkin) construction

This module is the coding-theory (Track 3) next step, complementing the minimum
distance computation of `PlotkinConstruction.lean` with the **dimension** of the
`(u | u+v)` code. Since the encoding map `uuvMap (u, v) = (u | u+v)` is injective,
the `(u | u+v)` code is linearly isomorphic to `C₁ × C₂`, and therefore

```
dim (uuvCode C₁ C₂) = dim C₁ + dim C₂.
```

Together with `minWeight_uuvCode` this gives the full `[2n, k₁ + k₂,
min(2d₁, d₂)]` parameter set of the Plotkin construction — exactly the recursion
`RM(r, m)` from `RM(r, m−1)` and `RM(r−1, m−1)` behind the Reed–Muller family.

## Main results

* `uuvMap_injective` — the encoding map `(u, v) ↦ (u | u+v)` is injective.
* `finrank_uuvCode` — `dim (uuvCode C₁ C₂) = dim C₁ + dim C₂`.
-/

open Finset BigOperators
open scoped Classical

namespace CodingTheory
namespace Plotkin

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

omit [Fintype ι] in
/-- The `(u | u+v)` encoding map is injective. -/
theorem uuvMap_injective : Function.Injective (uuvMap : (ι → F) × (ι → F) →ₗ[F] _) := by
  intro p q h;
  ext i;
  · replace h := congr_fun h ( Sum.inl i ) ; simp_all +decide [ uuvMap, uuv ] ;
  · have := congr_fun h ( Sum.inr i ) ; have := congr_fun h ( Sum.inl i ) ; simp_all +decide [ uuvMap, uuv ] ;

/-- **Dimension of the `(u | u+v)` construction.** For linear codes
`C₁, C₂ ⊆ Fⁿ`, the `(u | u+v)` code has dimension `dim C₁ + dim C₂`. -/
theorem finrank_uuvCode (C₁ C₂ : Submodule F (ι → F)) :
    Module.finrank F (uuvCode C₁ C₂)
      = Module.finrank F C₁ + Module.finrank F C₂ := by
  -- Apply `Submodule.equivMapOfInjective` to get an equivalence between `C₁ × C₂` and `uuvCode C₁ C₂`.
  have h_equiv : Nonempty (↥(C₁.prod C₂) ≃ₗ[F] ↥(uuvCode C₁ C₂)) := by
    exact ⟨ ( Submodule.equivMapOfInjective _ uuvMap_injective _ ) ⟩;
  obtain ⟨ e ⟩ := h_equiv;
  rw [ ← e.finrank_eq, ← Submodule.finrank_sup_add_finrank_inf_eq, add_comm ];
  convert Submodule.finrank_sup_add_finrank_inf_eq C₁ C₂ |> Eq.symm using 1;
  · rw [ ← Module.finrank_prod ];
    refine' LinearEquiv.finrank_eq _;
    refine' { Equiv.ofBijective ( fun x => ⟨ ⟨ x.val.1, x.2.1 ⟩, ⟨ x.val.2, x.2.2 ⟩ ⟩ ) ⟨ fun x y h => _, fun x => _ ⟩ with .. } <;> aesop;
  · grind

end Plotkin
end CodingTheory
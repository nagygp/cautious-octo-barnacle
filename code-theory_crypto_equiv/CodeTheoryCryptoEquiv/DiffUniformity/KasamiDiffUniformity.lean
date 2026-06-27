import CodeTheoryCryptoEquiv.DiffUniformity.DifferentialUniformity
import CodeTheoryCryptoEquiv.Core.KasamiAB

/-!
# Kasami functions as instances of the differential-uniformity foundation

This module is the bridge between the *abstract*, characteristic-free
differential-uniformity foundation
(`CodeTheoryCryptoEquiv/DiffUniformity/DifferentialUniformity.lean`) and the two *concrete*
APN predicates used in the Kasami development:

* `WalshAB.IsAPN` — the cardinality (count) form, `#{x | D_a f x = b} ≤ 2`;
* `KasamiAPN.IsAPN` — the collision form, `D_a f x = D_a f y → y ∈ {x, x+a}`.

Both are shown to be exactly `differentialUniformity f ≤ 2`
(`walshIsAPN_iff_diffUnif_le_two`, `kasamiIsAPN_iff_diffUnif_le_two`), so the
abstract `APNLib.IsAPN` (`differentialUniformity f = 2`) is a single common
generalization.  The Kasami APN headline then reappears as the corollary
`kasami_isAPN_diffUnif`: the Kasami power map has differential uniformity
exactly two.
-/

namespace APNLib

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-
In characteristic two the count-form predicate `WalshAB.IsAPN` is exactly
"differential uniformity at most two".
-/
theorem walshIsAPN_iff_diffUnif_le_two (f : F → F) :
    WalshAB.IsAPN f ↔ differentialUniformity f ≤ 2 := by
  -- By definition of fiberCard, we have:
  have h_fiberCard : ∀ a b, fiberCard f a b = Fintype.card { x : F // f (x + a) + f x = b } := by
    intro a b; rw [ Fintype.card_subtype ] ; simp +decide [ fiberCard, derivMap ] ;
    simp +decide [ sub_eq_add_neg, CharTwo.neg_eq ];
  rw [ APNLib.diffUnif_le_iff ];
  aesop

/-
In characteristic two the collision-form predicate `KasamiAPN.IsAPN` is
exactly "differential uniformity at most two".
-/
theorem kasamiIsAPN_iff_diffUnif_le_two (f : F → F) :
    KasamiAPN.IsAPN f ↔ differentialUniformity f ≤ 2 := by
  constructor;
  · intro h;
    apply APNLib.diffUnif_le_iff f 2 |>.2;
    intro a ha b;
    have h_card : ∀ x ∈ Finset.univ.filter (fun x => derivMap f a x = b), ∀ y ∈ Finset.univ.filter (fun x => derivMap f a x = b), x = y ∨ x = y + a := by
      intro x hx y hy; have := h a ha x y; simp_all +decide [ derivMap ] ;
      grind +suggestions;
    by_cases h : ∃ x, derivMap f a x = b <;> simp_all +decide [ fiberCard ];
    obtain ⟨ x, hx ⟩ := h; exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun y => derivMap f a y = b ) Finset.univ ⊆ { x, x + a } from fun y hy => by simpa using h_card _ ( Finset.mem_filter.mp hy |>.2 ) _ hx ) ) ( Finset.card_insert_le _ _ ) ;
  · intro h a ha x y hxy
    convert atMostTwoToOne_charTwo_collision f h a ha x y _ using 1;
    grind +suggestions

/-
**Kasami APN, as an instance of the abstract foundation.**

The Kasami power map `x ↦ x ^ d(k)` has differential uniformity exactly two,
i.e. it satisfies the abstract `APNLib.IsAPN`.  This is a specialization of the
first-principles headline `KasamiAB.kasami_is_apn_pred`.
-/
theorem kasami_isAPN_diffUnif {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : k ≥ 1) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n)
    (hn : n ≥ 1) : IsAPN (fun x : F => x ^ CollisionAnalysis.d k) := by
  -- To prove `IsAPN`, it suffices to show `differentialUniformity f ≤ 2`.
  suffices h : differentialUniformity (fun x : F => x ^ CollisionAnalysis.d k) ≤ 2 by exact le_antisymm h (APNLib.two_le_diffUnif_charTwo _);
  have := KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd hn;
  convert walshIsAPN_iff_diffUnif_le_two _ |>.1 this using 1

end APNLib
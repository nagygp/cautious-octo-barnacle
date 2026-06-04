import RequestProject.MTupleCount
import RequestProject.KasamiAPN
import RequestProject.KasamiEvenK
import RequestProject.KasamiAB

/-!
# Kasami Triple Count — Bridge Module

Connects the Kasami APN/AB theorems to the m-tuple count framework,
showing that the Kasami derivative image satisfies the triple count
formula `κ₃ = 2^{2n−3}` for `m = 3`.

## Main results
- `kasami_is_mtuple_apn`:  Kasami satisfies `MTupleCount.APN`
- `kasami_triple_count`:   `κ₃(Δ_a(x^d)) = 2^{2n−3}` under flat spectrum
-/

set_option maxHeartbeats 800000

namespace KasamiTripleCount

open Fintype MTupleCount KasamiAPN KasamiEvenK

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

/-- The Kasami function satisfies the MTupleCount APN predicate.

`KasamiAPN.IsAPN` says: each fiber `{x | D_a f(x) = b}` has ≤ 2 elements
(via the collision characterisation). `MTupleCount.APN` says the same thing
directly as a cardinality bound. -/
theorem kasami_is_mtuple_apn {n : ℕ} (hcard : card 𝔽 = 2 ^ n)
    (k : ℕ) (hk : 1 < k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    MTupleCount.APN (fun x : 𝔽 => x ^ kasamiExp k) := by
  set f := fun x : 𝔽 => x ^ kasamiExp k with hf_def
  have hapn := kasami_is_apn_general hcard k hk hkn hn_odd hcop
  intro a ha b
  -- Bound: the fiber {x | D f a x = b} ⊆ {x₀, x₀ + a} for any x₀ in it
  by_contra h_gt; push_neg at h_gt
  obtain ⟨x₁, hx₁m, x₂, hx₂m, x₃, hx₃m, h12, h13, h23⟩ :=
    Finset.two_lt_card.mp h_gt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MTupleCount.D] at hx₁m hx₂m hx₃m
  have heq12 : f (x₁ + a) + f x₁ = f (x₂ + a) + f x₂ := by
    simp only [CharTwo.sub_eq_add] at hx₁m hx₂m; rw [hx₁m, hx₂m]
  have heq13 : f (x₁ + a) + f x₁ = f (x₃ + a) + f x₃ := by
    simp only [CharTwo.sub_eq_add] at hx₁m hx₃m; rw [hx₁m, hx₃m]
  rcases hapn a ha x₁ x₂ heq12 with rfl | rfl
  · exact h12 rfl
  · rcases hapn a ha x₁ x₃ heq13 with rfl | rfl
    · exact h13 rfl
    · exact h23 rfl

/-- **Kasami triple count.** For APN Kasami over `GF(2ⁿ)` with `n ≥ 3`,
under flat spectrum on the derivative image, `κ₃ = 2^{2n−3}`. -/
theorem kasami_triple_count {n : ℕ} (hn : 3 ≤ n) (hcard : card 𝔽 = 2 ^ n)
    (k : ℕ) (hk : 1 < k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    (a : 𝔽) (ha : a ≠ 0) (χ : Chi 𝔽)
    (c : Fin 3 → 𝔽) (hc : ∀ i, c i ≠ 0)
    (hflat : FlatSpectrum χ (Δ (fun x => x ^ kasamiExp k) a)) :
    κ 3 (Δ (fun x => x ^ kasamiExp k) a) c = 2 ^ (2 * n - 3) :=
  triple_count n hn hcard (fun x => x ^ kasamiExp k) a ha χ
    (kasami_is_mtuple_apn hcard k hk hkn hn_odd hcop) c hflat hc

end KasamiTripleCount

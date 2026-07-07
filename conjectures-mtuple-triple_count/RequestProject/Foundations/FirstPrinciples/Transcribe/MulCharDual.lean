import Mathlib

/-!
# Transcription — Leaf L1, module 2: dual orthogonality on the cyclic group `Fˣ`

This module supplies the **dual orthogonality** ingredient that the monomial →
Gauss-sum expansion (`MonomialGaussExpansion.monomial_addCharSum_eq_gaussSum_sum`,
leaf **L1**) needs: for a multiplicative character `χ₁` of order exactly
`d = gcd(m, q−1)`, the sum of its first `d` powers evaluated at `y ∈ Fˣ` counts the
`m`-th-power fibre of `y`:

`∑_{j < d} χ₁ʲ(y) = #{x ∈ Fˣ | xᵐ = y}`.

Following the project's bottom-up style, this is split into two atomic sub-leaves
plus real assembly:

* `mthRoot_fibre_card` — the fibre count `#{x | xᵐ = y} = (if ∃x, xᵐ=y then d else 0)`,
  from the cyclic kernel-size lemma `IsCyclic.card_powMonoidHom_ker` and a coset
  bijection;
* `mulChar_eq_one_iff_isMthPow` — the kernel = range bridge
  `χ₁(y) = 1 ↔ ∃ x : Fˣ, xᵐ = y` (the unique-index-`d`-subgroup identity on `Fˣ`);
* `mulChar_pow_sum_eq_fibreCard` — the assembled dual orthogonality, **real wiring**
  combining the geometric sum with the two sub-leaves.

## Sources

* Lidl–Niederreiter, *Finite Fields*, Ch. 5 (character orthogonality on `Fˣ`).
* Ireland–Rosen, Ch. 8.
* Mathlib: `IsCyclic.card_powMonoidHom_ker`, `IsCyclic.card_powMonoidHom_range`.
-/

namespace Vanish.Foundations.FirstPrinciples.Transcribe

open scoped BigOperators
open MulChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-
**The `m`-th-power fibre count on `Fˣ`.**  The number of `m`-th roots of `y` in
`Fˣ` is `gcd(m, q−1)` if `y` is an `m`-th power and `0` otherwise.  Proof: the fibre
is empty or a coset of `(powMonoidHom m).ker`, whose size is `gcd(q−1, m)` by
`IsCyclic.card_powMonoidHom_ker`.
-/
theorem mthRoot_fibre_card (m : ℕ) (y : Fˣ) :
    (Finset.univ.filter (fun x : Fˣ => x ^ m = y)).card
      = if (∃ x : Fˣ, x ^ m = y) then Nat.gcd m (Fintype.card F - 1) else 0 := by
  by_cases h : ∃ x : Fˣ, x ^ m = y <;> simp_all +decide [ Fintype.card_subtype ];
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fˣ, x₀ ^ m = y := h
  have h_fibre : Finset.filter (fun x => x^m = y) (Finset.univ : Finset Fˣ) = Finset.image (fun x => x * x₀) (Finset.filter (fun x => x^m = 1) (Finset.univ : Finset Fˣ)) := by
    ext x; simp +decide [ ← hx₀, mul_pow ] ;
    rw [ mul_inv_eq_one ];
  rw [ h_fibre, Finset.card_image_of_injective _ fun x y hxy => mul_right_cancel hxy ];
  have h_kernel : Nat.card (MonoidHom.ker (powMonoidHom m : Fˣ →* Fˣ)) = Nat.gcd m (Fintype.card Fˣ) := by
    convert IsCyclic.card_powMonoidHom_ker ( G := Fˣ ) m using 1;
    rw [ Nat.gcd_comm, Nat.card_eq_fintype_card ];
  simp_all +decide [ Fintype.card_units ];
  rw [ ← h_kernel, Fintype.card_subtype ]

/-
**Kernel = range bridge (the unique index-`d` subgroup of `Fˣ`).**  For `χ₁` of
order `d = gcd(m, q−1)`, the kernel `{y | χ₁(y) = 1}` and the `m`-th powers coincide:
`χ₁(y) = 1 ↔ ∃ x : Fˣ, xᵐ = y`.  Both are the unique subgroup of `Fˣ` of order
`(q−1)/d` (`IsCyclic.card_powMonoidHom_range` for the right side, the image of `χ₁`
having order `d` for the left).
-/
theorem mulChar_eq_one_iff_isMthPow (m : ℕ) (hm : 1 ≤ m) (χ₁ : MulChar F ℂ)
    (hord : orderOf χ₁ = Nat.gcd m (Fintype.card F - 1)) (y : Fˣ) :
    χ₁ (y : F) = 1 ↔ ∃ x : Fˣ, x ^ m = y := by
  constructor;
  · -- Let $g$ be a generator of $F^\times$.
    obtain ⟨g, hg⟩ : ∃ g : Fˣ, ∀ x : Fˣ, ∃ k : ℕ, x = g^k := by
      have := IsCyclic.exists_monoid_generator ( α := Fˣ );
      exact ⟨ this.choose, fun x => by obtain ⟨ k, rfl ⟩ := this.choose_spec x; exact ⟨ k, rfl ⟩ ⟩;
    -- Since $χ₁(g)$ is a primitive $d$-th root of unity, we have $χ₁(g)^k = 1$ if and only if $d \mid k$.
    have h_primitive : ∀ k : ℕ, χ₁ (g ^ k) = 1 ↔ Nat.gcd m (Fintype.card F - 1) ∣ k := by
      intro k
      have h_order : χ₁ (g ^ k) = 1 ↔ (χ₁ g) ^ k = 1 := by
        simp +decide [ ← map_pow ];
      rw [ h_order, ← hord, orderOf_dvd_iff_pow_eq_one ];
      simp +decide [ funext_iff, MulChar.ext_iff ];
      constructor <;> intro h <;> simp_all +decide [ pow_mul, MulChar.pow_apply_coe ];
      intro a; obtain ⟨ k', rfl ⟩ := hg a; simp_all +decide [ pow_mul, MulChar.pow_apply_coe ] ;
      rw [ pow_right_comm, h, one_pow ];
    obtain ⟨ k, rfl ⟩ := hg y;
    intro hk
    obtain ⟨ t, ht ⟩ : ∃ t : ℕ, m * t ≡ k [MOD (Fintype.card F - 1)] := by
      have h_bezout : ∃ t u : ℤ, m * t + (Fintype.card F - 1) * u = k := by
        have h_bezout : ∃ t u : ℤ, m * t + (Fintype.card F - 1) * u = Nat.gcd m (Fintype.card F - 1) := by
          have := Nat.gcd_eq_gcd_ab m ( Fintype.card F - 1 );
          exact ⟨ Nat.gcdA m ( Fintype.card F - 1 ), Nat.gcdB m ( Fintype.card F - 1 ), by rw [ this, Nat.cast_pred ( Fintype.card_pos ) ] ⟩;
        obtain ⟨ t, u, h ⟩ := h_bezout;
        obtain ⟨ v, hv ⟩ := h_primitive k |>.1 ( by simpa using hk );
        exact ⟨ t * v, u * v, by push_cast [ hv ] ; linear_combination' h * v ⟩;
      obtain ⟨ t, u, h ⟩ := h_bezout; use Int.toNat ( t % ( Fintype.card F - 1 ) ) ; simp +decide [ ← Int.natCast_modEq_iff, ← h, Int.ModEq, Int.add_emod, Int.mul_emod ] ;
      simp +decide [ ← Int.mul_emod, ← Int.add_emod, Int.emod_nonneg _ ( show ( Fintype.card F - 1 : ℤ ) ≠ 0 from sub_ne_zero_of_ne <| mod_cast ne_of_gt <| Fintype.one_lt_card ) ];
      simp +decide [ Int.add_emod, Int.mul_emod, Nat.cast_sub ( show 1 ≤ Fintype.card F from Fintype.card_pos ) ];
    use g^t;
    rw [ ← pow_mul, mul_comm, ← Nat.mod_add_div ( m * t ) ( Fintype.card F - 1 ), ht ];
    rw [ ← Nat.mod_add_div k ( Fintype.card F - 1 ) ] ; simp +decide [ pow_add, pow_mul, pow_orderOf_eq_one ] ;
    rw [ ← Fintype.card_units, pow_card_eq_one ] ; aesop;
  · rintro ⟨ x, rfl ⟩;
    have := pow_orderOf_eq_one χ₁;
    replace this := congr_arg ( fun f => f x ) this ; simp_all +decide [ pow_mul, pow_orderOf_eq_one ];
    rw [ ← Nat.mul_div_cancel' ( Nat.gcd_dvd_left m ( Fintype.card F - 1 ) ), pow_mul, show χ₁ x ^ Nat.gcd m ( Fintype.card F - 1 ) = 1 from by simpa [ MulChar.pow_apply_coe ] using this ] ; simp +decide

/-- **Dual orthogonality / fibre count (Lidl–Niederreiter Ch. 5).**  For `χ₁` of
order `d = gcd(m, q−1)` and `y ∈ Fˣ`, the sum of the first `d` powers of `χ₁` at `y`
equals the number of `m`-th roots of `y` in `Fˣ`.  Real wiring: the geometric sum
(via `geom_sum_eq`) over the `d`-th root of unity `χ₁(y)`, combined with the fibre
count `mthRoot_fibre_card` and the bridge `mulChar_eq_one_iff_isMthPow`. -/
theorem mulChar_pow_sum_eq_fibreCard (m : ℕ) (hm : 1 ≤ m) (χ₁ : MulChar F ℂ)
    (hord : orderOf χ₁ = Nat.gcd m (Fintype.card F - 1)) (y : Fˣ) :
    ∑ j ∈ Finset.range (orderOf χ₁), (χ₁ ^ j) (y : F)
      = ((Finset.univ.filter (fun x : Fˣ => x ^ m = y)).card : ℂ) := by
  have hroot : (χ₁ (y : F)) ^ orderOf χ₁ = 1 := by
    have h1 : (χ₁ ^ orderOf χ₁) (y : F) = 1 := by
      rw [pow_orderOf_eq_one, MulChar.one_apply_coe]
    rwa [MulChar.pow_apply_coe] at h1
  have hsum : ∑ j ∈ Finset.range (orderOf χ₁), (χ₁ ^ j) (y : F)
      = ∑ j ∈ Finset.range (orderOf χ₁), (χ₁ (y : F)) ^ j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MulChar.pow_apply_coe]
  rw [hsum, mthRoot_fibre_card m y]
  by_cases hy : χ₁ (y : F) = 1
  · have hex : (∃ x : Fˣ, x ^ m = y) := (mulChar_eq_one_iff_isMthPow m hm χ₁ hord y).mp hy
    simp only [hy, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hex,
      if_true, hord]
  · have hnex : ¬ (∃ x : Fˣ, x ^ m = y) := fun h =>
      hy ((mulChar_eq_one_iff_isMthPow m hm χ₁ hord y).mpr h)
    have hd : 1 ≤ orderOf χ₁ := χ₁.orderOf_pos
    rw [geom_sum_eq hy, hroot, sub_self, zero_div]
    simp [hnex]

end Vanish.Foundations.FirstPrinciples.Transcribe
import Mathlib

/-!
# Gauss's generalization of Wilson's theorem (product of units mod a prime power)

This module proves the value of the product of all units of `ZMod (p ^ M)`, which is
the genuine analytic input behind Morita's `p`-adic Γ convergence (the Wilson
"block product" congruence).  Specifically:

* `prod_units_zmod_prime_pow_odd` — for `p` an odd prime and `M ≥ 1`,
  `∏ x : (ZMod (p ^ M))ˣ, x = -1`.
* `prod_units_zmod_two_pow` — for `M ≥ 3`, `∏ x : (ZMod (2 ^ M))ˣ, x = 1`.

These are Gauss's theorem (the prime-power generalization of Wilson's theorem),
absent from Mathlib.
-/

set_option maxHeartbeats 1600000

open scoped BigOperators
open Finset

namespace Vanish.Foundations.FirstPrinciples.Decomp

/-
**Product of all elements of a finite commutative group equals the product of
its involutions** (elements that are their own inverse).  Pairing `x` with `x⁻¹`
cancels all non-involutions.
-/
theorem prod_univ_eq_prod_self_inv {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ univ.filter (fun g : G => g⁻¹ = g), x := by
  -- Split the product into two parts: one over the involutions and one over the non-involutions.
  have h_split : ∏ x : G, x = (∏ x ∈ Finset.univ.filter (fun x : G => x⁻¹ = x), x) * (∏ x ∈ Finset.univ.filter (fun x : G => x⁻¹ ≠ x), x) := by
    rw [ Finset.prod_filter_mul_prod_filter_not ];
  -- Since the product over the non-involutions is 1, we can simplify the expression.
  have h_noninvol : ∏ x ∈ Finset.univ.filter (fun x : G => x⁻¹ ≠ x), x = 1 := by
    have h_pair : ∃ S : Finset (Finset G), (∀ s ∈ S, s.card = 2) ∧ (∀ s ∈ S, ∀ x ∈ s, x⁻¹ ∈ s) ∧ (∀ x ∈ Finset.univ.filter (fun x : G => x⁻¹ ≠ x), ∃ s ∈ S, x ∈ s) ∧ (∀ s ∈ S, ∏ x ∈ s, x = 1) ∧ (Finset.univ.filter (fun x : G => x⁻¹ ≠ x) = Finset.biUnion S id) := by
      refine' ⟨ Finset.image ( fun x => { x, x⁻¹ } ) ( Finset.univ.filter ( fun x : G => x⁻¹ ≠ x ) ), _, _, _, _, _ ⟩ <;> simp +decide [ Finset.subset_iff ];
      · exact fun x hx => Finset.card_pair ( Ne.symm hx );
      · exact fun x hx => ⟨ x, hx, Or.inl rfl ⟩;
      · intro a ha; rw [ Finset.prod_pair ] <;> simp +decide [ ha ] ;
        exact Ne.symm ha;
      · ext x; simp [Finset.mem_biUnion, Finset.mem_image];
        exact ⟨ fun hx => ⟨ x, hx, Or.inl rfl ⟩, fun ⟨ a, ha, hx ⟩ => by cases hx <;> simp_all +decide [ inv_eq_iff_eq_inv ] ⟩;
    obtain ⟨ S, hS₁, hS₂, hS₃, hS₄, hS₅ ⟩ := h_pair; rw [ hS₅, Finset.prod_biUnion ] ; aesop;
    intro s hs t ht hst; simp_all +decide [ Finset.disjoint_left ] ;
    intro x hx hx'; have := Finset.card_eq_two.mp ( hS₁ s hs ) ; have := Finset.card_eq_two.mp ( hS₁ t ht ) ; simp_all +decide [ Finset.ext_iff ] ;
    grind +ring;
  rw [ h_split, h_noninvol, mul_one ]

/-
**Gauss / Wilson for odd prime powers.**  For an odd prime `p` and `M ≥ 1`, the
product of all units of `ZMod (p ^ M)` is `-1`.
-/
theorem prod_units_zmod_prime_pow_odd (p M : ℕ) [Fact (Nat.Prime p)]
    (hp : Odd p) (hM : 1 ≤ M) :
    ∏ x : (ZMod (p ^ M))ˣ, (x : ZMod (p ^ M)) = -1 := by
  have h_inv : (∏ x : (ZMod (p ^ M))ˣ, (x : ZMod (p ^ M))) = ∏ x ∈ Finset.filter (fun g : (ZMod (p ^ M))ˣ => g⁻¹ = g) (Finset.univ : Finset (ZMod (p ^ M))ˣ), (x : ZMod (p ^ M)) := by
    have h_inv : ∀ {G : Type} [CommGroup G] [Fintype G] [DecidableEq G], (∏ x : G, x) = ∏ x ∈ Finset.filter (fun g : G => g⁻¹ = g) (Finset.univ : Finset G), x := by
      grind +suggestions;
    convert congr_arg ( fun x : ( ZMod ( p ^ M ) ) ˣ => ( x : ZMod ( p ^ M ) ) ) ( h_inv ) using 1;
    · induction' ( Finset.univ : Finset ( ZMod ( p ^ M ) ) ˣ ) using Finset.induction <;> aesop;
    · induction' ( Finset.filter ( fun x : ( ZMod ( p ^ M ) ) ˣ => x⁻¹ = x ) Finset.univ ) using Finset.induction <;> aesop;
  -- In a finite cyclic group of even order, there are exactly two elements of order 2: 1 and -1.
  have h_order_two : ∀ x : (ZMod (p ^ M))ˣ, x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
    intro x
    have h_order_two : ∀ x : (ZMod (p ^ M))ˣ, x ^ 2 = 1 → x = 1 ∨ x = -1 := by
      intro x hx
      have h_order_two : ∀ x : (ZMod (p ^ M)), x ^ 2 = 1 → x = 1 ∨ x = -1 := by
        intro x hx
        have h_order_two : ∀ x : ℤ, x ^ 2 ≡ 1 [ZMOD p ^ M] → x ≡ 1 [ZMOD p ^ M] ∨ x ≡ -1 [ZMOD p ^ M] := by
          intro x hx
          have h_order_two : (x - 1) * (x + 1) ≡ 0 [ZMOD p ^ M] := by
            convert hx.sub_right 1 using 1 ; ring;
          -- Since $p$ is odd, $p^M$ divides either $x - 1$ or $x + 1$.
          have h_div : (p ^ M : ℤ) ∣ (x - 1) ∨ (p ^ M : ℤ) ∣ (x + 1) := by
            have h_div : Nat.gcd (p ^ M) (Int.natAbs (x - 1)) = 1 ∨ Nat.gcd (p ^ M) (Int.natAbs (x + 1)) = 1 := by
              by_cases h_div : (p : ℤ) ∣ (x - 1);
              · refine Or.inr <| Nat.Coprime.pow_left _ <| Nat.Prime.coprime_iff_not_dvd ( Fact.out : Nat.Prime p ) |>.2 ?_;
                intro H; haveI := Fact.mk ( Fact.out : Nat.Prime p ) ; simp_all +decide [ ← Int.natCast_dvd_natCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_iff_eq_add ] ;
              · exact Or.inl <| Nat.Coprime.pow_left _ <| Nat.Prime.coprime_iff_not_dvd ( Fact.out : Nat.Prime p ) |>.2 fun h => h_div <| Int.natCast_dvd.2 h;
            cases h_div <;> [ exact Or.inr ( Int.dvd_of_dvd_mul_right_of_gcd_one ( Int.dvd_of_emod_eq_zero h_order_two ) <| by simpa [ Int.gcd, Int.natAbs_pow ] using ‹Nat.gcd ( p ^ M ) ( Int.natAbs ( x - 1 ) ) = 1› ) ; exact Or.inl ( Int.dvd_of_dvd_mul_left_of_gcd_one ( Int.dvd_of_emod_eq_zero h_order_two ) <| by simpa [ Int.gcd, Int.natAbs_pow ] using ‹Nat.gcd ( p ^ M ) ( Int.natAbs ( x + 1 ) ) = 1› ) ];
          exact Or.imp ( fun h => Int.ModEq.symm <| Int.modEq_of_dvd h ) ( fun h => Int.ModEq.symm <| Int.modEq_of_dvd h ) h_div;
        specialize h_order_two ( x.val : ℤ ) ; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
        convert h_order_two _;
        · erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
        · erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
        · erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
      simpa only [ Units.ext_iff ] using h_order_two x ( by simpa [ ← Units.val_inj ] using hx );
    exact ⟨ h_order_two x, by rintro ( rfl | rfl ) <;> norm_num ⟩;
  -- Therefore, the set of elements of order 2 in $(ZMod (p ^ M))ˣ$ is exactly $\{1, -1\}$.
  have h_set_order_two : Finset.filter (fun g : (ZMod (p ^ M))ˣ => g⁻¹ = g) (Finset.univ : Finset (ZMod (p ^ M))ˣ) = {1, -1} := by
    ext x; specialize h_order_two x; simp_all +decide [ sq, inv_eq_iff_mul_eq_one ] ;
  simp_all +decide [ Finset.prod_pair ]

/-
**Gauss / Wilson for `2`-power moduli `≥ 8`.**  For `M ≥ 3`, the product of all
units of `ZMod (2 ^ M)` is `1`.
-/
theorem prod_units_zmod_two_pow (M : ℕ) (hM : 3 ≤ M) :
    ∏ x : (ZMod (2 ^ M))ˣ, (x : ZMod (2 ^ M)) = 1 := by
  -- The 2-torsion of (ZMod (2^M))ˣ is the Klein four-group.
  have h_klein : (Finset.filter (fun x : (Units (ZMod (2 ^ M))) => x ^ 2 = 1) Finset.univ).card = 4 := by
    -- Let's count the number of solutions to $x^2 \equiv 1 \pmod{2^M}$.
    have h_solutions : Finset.card (Finset.filter (fun x : ZMod (2 ^ M) => x ^ 2 = 1) (Finset.univ : Finset (ZMod (2 ^ M)))) = 4 := by
      -- We'll use that $x^2 \equiv 1 \pmod{2^M}$ has exactly four solutions: $1, -1, 2^{M-1}+1, 2^{M-1}-1$.
      have h_solutions : ∀ x : ℕ, x < 2 ^ M → (x ^ 2 ≡ 1 [MOD 2 ^ M]) → x = 1 ∨ x = 2 ^ M - 1 ∨ x = 2 ^ (M - 1) + 1 ∨ x = 2 ^ (M - 1) - 1 := by
        intro x hx hx'
        have h_div : 2 ^ M ∣ (x - 1) * (x + 1) := by
          rw [ mul_comm, ← Nat.sq_sub_sq ];
          rw [ ← Nat.mod_add_div ( x ^ 2 ) ( 2 ^ M ), hx'.of_dvd <| dvd_refl _ ] ; norm_num [ Nat.mod_eq_of_lt hx ];
          rcases M with ( _ | _ | M ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        -- Since $x$ is odd, we can write $x = 2k + 1$ for some integer $k$.
        obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := by
          rcases Nat.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> replace hx' := congr_arg Even hx'.symm.dvd.choose_spec <;> simp_all +decide [ parity_simps ];
          replace := congr_arg ( · % 2 ) ‹ ( 2 * k ) ^ 2 % 2 ^ M = 1 % 2 ^ M › ; norm_num [ Nat.pow_mod, Nat.mul_mod, show M ≠ 0 by linarith ] at this;
        -- Since $2^M \mid 4k(k + 1)$, we have $2^{M-2} \mid k(k + 1)$.
        have h_div_k : 2 ^ (M - 2) ∣ k * (k + 1) := by
          rcases M with ( _ | _ | M ) <;> simp_all +decide [ pow_succ' ];
          exact Exists.elim h_div fun x hx => ⟨ x, by linarith ⟩;
        -- Since $k$ and $k + 1$ are coprime, one of them must be divisible by $2^{M-2}$.
        have h_div_k_or_k1 : 2 ^ (M - 2) ∣ k ∨ 2 ^ (M - 2) ∣ k + 1 := by
          have h_coprime : Nat.gcd (2 ^ (M - 2)) k = 1 ∨ Nat.gcd (2 ^ (M - 2)) (k + 1) = 1 := by
            rcases M with ( _ | _ | _ | M ) <;> simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ];
            grind +extAll;
          cases h_coprime <;> [ exact Or.inr ( Nat.Coprime.dvd_of_dvd_mul_left ‹_› h_div_k ) ; exact Or.inl ( Nat.Coprime.dvd_of_dvd_mul_right ‹_› h_div_k ) ];
        rcases M with ( _ | _ | M ) <;> simp_all +decide [ pow_succ' ];
        rcases h_div_k_or_k1 with ( h | h ) <;> obtain ⟨ c, hc ⟩ := h <;> rcases c with ( _ | _ | c ) <;> simp_all! +arith +decide [ Nat.pow_succ' ];
        · grind;
        · exact Or.inr <| Or.inr <| Or.inr <| eq_tsub_of_add_eq <| by linarith;
        · exact Or.inr <| Or.inl <| eq_tsub_of_add_eq <| by nlinarith;
      have h_solutions_set : Finset.filter (fun x : ℕ => x < 2 ^ M ∧ x ^ 2 ≡ 1 [MOD 2 ^ M]) (Finset.range (2 ^ M)) = {1, 2 ^ M - 1, 2 ^ (M - 1) + 1, 2 ^ (M - 1) - 1} := by
        ext x;
        constructor <;> intro hx <;> specialize h_solutions x <;> rcases M with ( _ | _ | M ) <;> simp_all +decide [ Nat.ModEq, Nat.pow_succ' ];
        rcases hx with ( rfl | rfl | rfl | rfl ) <;> norm_num [ Nat.mod_eq_of_lt ];
        · grind +splitIndPred;
        · refine Nat.modEq_of_dvd ?_;
          norm_num ; ring_nf;
          exact ⟨ 2 - 2 ^ M * 4, by rw [ pow_mul ] ; ring ⟩;
        · norm_num [ show ( 2 * 2 ^ M + 1 ) * ( 2 * 2 ^ M + 1 ) = 2 * ( 2 * 2 ^ M ) * ( 2 ^ M + 1 ) + 1 by ring ];
          linarith [ pow_pos ( by decide : 0 < 2 ) M ];
        · zify;
          norm_num ; ring_nf;
          norm_num [ pow_mul, Int.emod_eq_emod_iff_emod_sub_eq_zero ];
          exact ⟨ -1 + 2 ^ M, by ring ⟩;
      convert congr_arg Finset.card h_solutions_set using 1;
      · refine' Finset.card_bij ( fun x hx => x.val ) _ _ _ <;> simp +decide [ ← ZMod.natCast_eq_natCast_iff ];
        · exact fun a ha => ⟨ a.val_lt, ha ⟩;
        · exact fun a₁ ha₁ a₂ ha₂ h => by simpa [ ZMod.natCast_zmod_val ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod ( 2 ^ M ) ) h;
        · exact fun b hb hb' => ⟨ b, by simpa [ ← ZMod.natCast_eq_natCast_iff ] using hb', by rw [ ZMod.val_cast_of_lt hb ] ⟩;
      · rcases M with ( _ | _ | _ | M ) <;> simp_all +decide [ Nat.pow_succ' ];
        grind;
    convert h_solutions using 1;
    convert rfl;
    fapply Finset.card_bij;
    use fun a ha => Units.mkOfMulEqOne a ( a ) ( by simpa [ sq ] using ha );
    · simp +decide [ sq, Units.ext_iff ];
    · simp +contextual [ Units.ext_iff ];
    · simp +decide [ Units.ext_iff ];
  -- The product of all elements in a finite abelian group is equal to the product of its elements of order 2.
  have h_prod_eq : (∏ x : (Units (ZMod (2 ^ M))), (x : (ZMod (2 ^ M)))) = (∏ x ∈ Finset.filter (fun x : (Units (ZMod (2 ^ M))) => x ^ 2 = 1) Finset.univ, (x : (ZMod (2 ^ M)))) := by
    have h_prod_eq : ∀ (G : Type) [CommGroup G] [Fintype G] [DecidableEq G], (∏ x : G, x) = (∏ x ∈ Finset.filter (fun x : G => x ^ 2 = 1) Finset.univ, x) := by
      intros G _ _ _; exact (by
      convert prod_univ_eq_prod_self_inv using 1;
      exact Finset.prod_congr ( by ext; simp +decide [ sq, inv_eq_iff_mul_eq_one ] ) fun _ _ => rfl;
      infer_instance);
    convert congr_arg ( fun x : ( Units ( ZMod ( 2 ^ M ) ) ) => ( x : ZMod ( 2 ^ M ) ) ) ( h_prod_eq ( Units ( ZMod ( 2 ^ M ) ) ) ) using 1;
    · induction' ( Finset.univ : Finset ( Units ( ZMod ( 2 ^ M ) ) ) ) using Finset.induction <;> aesop;
    · induction' ( Finset.filter ( fun x : ( Units ( ZMod ( 2 ^ M ) ) ) => x ^ 2 = 1 ) Finset.univ ) using Finset.induction <;> aesop;
  -- Let's denote the set of elements of order 2 in $(\mathbb{Z} / 2^M \mathbb{Z})^\times$ by $S$.
  set S : Finset (Units (ZMod (2 ^ M))) := Finset.filter (fun x : (Units (ZMod (2 ^ M))) => x ^ 2 = 1) Finset.univ;
  -- Since $S$ is a subgroup of $(\mathbb{Z} / 2^M \mathbb{Z})^\times$, it is isomorphic to the Klein four-group.
  have h_iso : ∃ (a b : Units (ZMod (2 ^ M))), a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ (a * b) ^ 2 = 1 ∧ S = {1, a, b, a * b} := by
    -- Let's choose any two distinct elements $a$ and $b$ from $S$.
    obtain ⟨a, ha⟩ : ∃ a : Units (ZMod (2 ^ M)), a ≠ 1 ∧ a ^ 2 = 1 := by
      contrapose! h_klein;
      rw [ show S = { 1 } from Finset.eq_singleton_iff_unique_mem.mpr ⟨ by aesop, fun x hx => Classical.not_not.1 fun hx' => h_klein x hx' <| Finset.mem_filter.mp hx |>.2 ⟩ ] ; norm_num
    obtain ⟨b, hb⟩ : ∃ b : Units (ZMod (2 ^ M)), b ≠ 1 ∧ b ≠ a ∧ b ^ 2 = 1 := by
      contrapose! h_klein;
      rw [ show S = { 1, a } by ext x; by_cases hx : x = 1 <;> by_cases hx' : x = a <;> aesop ] ; rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
    refine' ⟨ a, b, ha.1, hb.1, _, ha.2, hb.2.2, _, _ ⟩ <;> simp_all +decide [ mul_pow ];
    · tauto;
    · rw [ Finset.eq_of_subset_of_card_le ( show { 1, a, b, a * b } ⊆ S from ?_ ) ] <;> simp_all +decide [ Finset.subset_iff ];
      · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide [ *, mul_eq_one_iff_inv_eq ];
        · tauto;
        · simp_all +decide [ eq_comm, mul_eq_one_iff_inv_eq ];
          intro h; simp_all +decide [ sq, mul_eq_one_iff_inv_eq ] ;
      · simp +zetaDelta at *;
        simp_all +decide [ mul_pow ];
  obtain ⟨ a, b, ha, hb, hab, ha', hb', hab', hS ⟩ := h_iso; simp_all +decide [ Finset.prod_pair, mul_assoc ] ;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, pow_two ];
  norm_cast ; simp_all +decide [ ← mul_assoc ]

end Vanish.Foundations.FirstPrinciples.Decomp
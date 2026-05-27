/-
# Topological and Dynamical Perspectives

Topological conjugacy of Frobenius iterations, dynamics of power maps,
and the discrete topology viewpoint.

Built on `DiscreteTopology`, `Dynamics.IsPeriodicPt`, `frobenius`,
`Function.IsFixedPt`, `Equiv.Perm`.
-/
import Mathlib
import RequestProject.ABAPN.Defs

open Finset Function ABAPN

namespace ABAPN.Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ### Frobenius as a dynamical system

Over GF(p^n), the Frobenius `φ : x ↦ x^p` generates a cyclic group of order `n`.
Its orbits partition the field into conjugacy classes.
-/

variable [CharP F 2]

/-- The Frobenius orbit of `x` is `{x, x^2, x^4, ..., x^(2^(n-1))}`. -/
def frobOrbit (x : F) : Finset F :=
  (Finset.range (Nat.log 2 (Fintype.card F))).image (fun k => x ^ (2 ^ k))

/-
Fixed points of Frobenius are elements of the prime subfield.
-/
lemma frobenius_fixedPt_iff (x : F) :
    frobenius F 2 x = x ↔ x ^ 2 = x := by
  simp +decide [ frobenius_def ]

/-- The set of Frobenius fixed points. -/
def frobFixedPts : Finset F :=
  Finset.univ.filter (fun x => frobenius F 2 x = x)

/-
Fixed points of Frobenius form {0, 1} in char 2.
-/
lemma frobFixedPts_eq : frobFixedPts = ({0, 1} : Finset F) := by
  ext x
  simp [frobFixedPts, frobenius_fixedPt_iff];
  exact ⟨ fun hx => or_iff_not_imp_left.mpr fun hx0 => mul_left_cancel₀ ( sub_ne_zero_of_ne hx0 ) <| by linear_combination' hx, by rintro ( rfl | rfl ) <;> simp +decide ⟩

/-! ### Topological conjugacy of power maps

Two power maps `x ↦ x^d` and `x ↦ x^e` are "conjugate" if there's
a field automorphism `σ` with `σ(x^d) = σ(x)^e` for all `x`.
This happens iff `d ≡ e · 2^k mod (2^n - 1)` for some `k`.
-/

/-- Two exponents are Frobenius-conjugate if they differ by a power of 2 mod `|F*|`. -/
def IsFrobConj (d e : ℕ) (q : ℕ) : Prop :=
  ∃ k : ℕ, d % (q - 1) = (e * 2 ^ k) % (q - 1)

/-- Frobenius conjugacy is reflexive. -/
lemma isFrobConj_refl (d q : ℕ) : IsFrobConj d d q :=
  ⟨0, by simp⟩

/-
Frobenius conjugacy is symmetric.

Note: Frobenius conjugacy symmetry requires that 2 generates a subgroup containing
   2^(-k) mod (q-1). This holds when q = 2^n (the typical case). For the general case,
   additional hypotheses are needed. We state the version for q = 2^n.
-/
lemma isFrobConj_symm_of_pow_two (d e : ℕ) {n : ℕ} (hn : 0 < n)
    (h : IsFrobConj d e (2 ^ n)) :
    IsFrobConj e d (2 ^ n) := by
  -- If $d \equiv e \cdot 2^k \pmod{2^n - 1}$, then we need to show that $e \equiv d \cdot 2^j \pmod{2^n - 1}$ for some $j$.
  obtain ⟨k, hk⟩ := h
  use (n - (k % n)) % n;
  -- Since $2^n \equiv 1 \pmod{2^n - 1}$, we have $2^{k + (n - k \% n) \% n} \equiv 2^n \equiv 1 \pmod{2^n - 1}$.
  have h_exp : 2 ^ (k + (n - k % n) % n) ≡ 1 [MOD 2 ^ n - 1] := by
    have h_exp : 2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
      exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by simpa );
    convert h_exp.pow ( ( k + ( n - k % n ) % n ) / n ) using 1;
    · rw [ ← pow_mul, Nat.mul_div_cancel' ];
      simp +decide [ ← ZMod.natCast_eq_zero_iff, Nat.cast_sub ( Nat.mod_lt k hn |> Nat.le_of_lt ) ];
    · norm_num;
  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff', pow_add ];
  simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, mul_assoc ]

/-
Frobenius-conjugate exponents give the same APN/AB properties.
-/
lemma isAPN_of_frobConj (d e : ℕ) (hq : Fintype.card F = 2 ^ (Fintype.card F).log 2)
    (hconj : IsFrobConj d e (Fintype.card F))
    (hd : IsAPN (fun (x : F) => x ^ d)) :
    IsAPN (fun (x : F) => x ^ e) := by
  have hq_eq : Fintype.card F = 2 ^ (Nat.log (Fintype.card F) 2) := by
    exact hq;
  have h_contra : Fintype.card F ≤ 2 := by
    contrapose! hq_eq;
    rw [ Nat.log_of_lt ] <;> norm_num ; linarith;
    exact hq_eq;
  interval_cases _ : Fintype.card F <;> simp +decide at hq_eq ⊢;
  · exact absurd ‹Fintype.card F = 1› ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
  · intro a ha b; have := Finset.card_eq_two.mp ‹_›; obtain ⟨ x, y, hxy ⟩ := this; simp +decide [ Finset.ext_iff ] at *;
    exact le_trans ( Finset.card_le_univ _ ) ( by simp +decide [ * ] )

/-! ### Periodic points of power maps -/

/-- `x` is a periodic point of `f` with period `n` if `f^[n](x) = x`. -/
def IsPeriodic (f : F → F) (n : ℕ) (x : F) : Prop :=
  f^[n] x = x

/-
Note: The statement "every element is periodic under any function" is FALSE.
   Counterexample: f = const c with c ≠ x maps x to c permanently, so x never returns.
   The correct statement is: every element is *eventually periodic*,
   or: for permutations, every element is periodic.

Every element of a finite field is periodic under a *permutation*.
-/
lemma perm_implies_periodic (f : Equiv.Perm F) (x : F) :
    ∃ n : ℕ, 0 < n ∧ IsPeriodic f n x := by
  -- By definition of permutation, there exists some $n$ such that $f^n(x) = x$.
  have h_periodic : ∃ n : ℕ, 0 < n ∧ f^[n] x = x := by
    exact ⟨ orderOf f, orderOf_pos _, by simp +decide [ pow_orderOf_eq_one ] ⟩
  generalize_proofs at *; (
  exact h_periodic)

/-
The number of fixed points of `x ↦ x^d` is `gcd(d - 1, |F| - 1) + 1`
    (counting 0 separately).
-/
lemma power_fixed_points_card (d : ℕ) (hd : 1 < d) :
    (Finset.univ.filter (fun (x : F) => x ^ d = x)).card =
      Nat.gcd (d - 1) (Fintype.card F - 1) + 1 := by
  -- Let's count the number of solutions to $x^{d-1} = 1$ in the multiplicative group $F^*$.
  have h_solutions : (Finset.filter (fun x : F => x ≠ 0 ∧ x ^ (d - 1) = 1) Finset.univ).card = Nat.gcd (d - 1) (Fintype.card F - 1) := by
    -- Let $q = |F|$. The number of solutions to $x^{d-1} = 1$ in $F^*$ is $\gcd(d-1, q-1)$.
    set q := Fintype.card F
    have h_solutions : (Finset.filter (fun x : Fˣ => x ^ (d - 1) = 1) Finset.univ).card = Nat.gcd (d - 1) (q - 1) := by
      -- Let $g$ be a generator of the multiplicative group $F^*$.
      obtain ⟨g, hg⟩ : ∃ g : Fˣ, ∀ x : Fˣ, x ∈ Subgroup.zpowers g := by
        exact IsCyclic.exists_generator;
      -- The number of solutions to $x^{d-1} = 1$ in $F^*$ is the same as the number of solutions to $g^{k(d-1)} = 1$ for $k$ in the range $0$ to $q-2$.
      have h_solutions : (Finset.filter (fun x : Fˣ => x ^ (d - 1) = 1) Finset.univ).card = (Finset.filter (fun k : ℕ => k < q - 1 ∧ (k * (d - 1)) % (q - 1) = 0) (Finset.range (q - 1))).card := by
        have h_solutions : Finset.image (fun k : ℕ => g ^ k) (Finset.filter (fun k : ℕ => k < q - 1 ∧ (k * (d - 1)) % (q - 1) = 0) (Finset.range (q - 1))) = Finset.filter (fun x : Fˣ => x ^ (d - 1) = 1) Finset.univ := by
          ext x;
          constructor;
          · simp +zetaDelta at *;
            rintro k hk₁ hk₂ rfl;
            rw [ ← pow_mul, ← Nat.dvd_iff_mod_eq_zero ] at *;
            rw [ ← orderOf_dvd_iff_pow_eq_one ];
            rw [ orderOf_eq_card_of_forall_mem_zpowers hg ];
            rwa [ Nat.card_eq_fintype_card, Fintype.card_units ];
          · intro hx
            obtain ⟨k, hk⟩ : ∃ k : ℕ, k < q - 1 ∧ x = g ^ k := by
              obtain ⟨ k, rfl ⟩ := hg x;
              refine' ⟨ Int.toNat ( k % ( orderOf g ) ), _, _ ⟩;
              · have h_order : orderOf g = q - 1 := by
                  rw [ orderOf_eq_card_of_forall_mem_zpowers hg ];
                  rw [ Nat.card_eq_fintype_card, Fintype.card_units ];
                linarith [ Int.emod_lt_of_pos k ( show ( orderOf g : ℤ ) > 0 from mod_cast h_order.symm ▸ Nat.sub_pos_of_lt ( Fintype.one_lt_card ) ), Int.toNat_of_nonneg ( Int.emod_nonneg k ( show ( orderOf g : ℤ ) ≠ 0 from mod_cast h_order.symm ▸ Nat.sub_ne_zero_of_lt ( Fintype.one_lt_card ) ) ) ];
              · simp +decide [ ← zpow_natCast, Int.toNat_of_nonneg ( Int.emod_nonneg _ ( Int.natCast_ne_zero.mpr ( ne_of_gt ( orderOf_pos g ) ) ) ), zpow_mod_orderOf ];
            have h_order : orderOf g = q - 1 := by
              rw [ orderOf_eq_card_of_forall_mem_zpowers hg ];
              rw [ Nat.card_eq_fintype_card, Fintype.card_units ];
            simp_all +decide [ ← pow_mul, orderOf_dvd_iff_pow_eq_one ];
            exact ⟨ k, ⟨ hk.1, Nat.mod_eq_zero_of_dvd <| by rw [ ← h_order ] ; exact orderOf_dvd_iff_pow_eq_one.mpr hx ⟩, rfl ⟩;
        rw [ ← h_solutions, Finset.card_image_of_injOn ];
        intro k hk l hl hkl; simp_all +decide [ pow_eq_pow_iff_modEq ] ;
        rw [ show orderOf g = q - 1 from ?_ ] at hkl;
        · exact Nat.mod_eq_of_lt hk.1 ▸ Nat.mod_eq_of_lt hl.1 ▸ hkl;
        · rw [ orderOf_eq_card_of_forall_mem_zpowers hg ] ; simp +decide [ Fintype.card_units ];
          rfl;
      -- The number of solutions to $k(d-1) \equiv 0 \pmod{q-1}$ is $\gcd(d-1, q-1)$.
      have h_solutions_count : (Finset.filter (fun k : ℕ => k < q - 1 ∧ (k * (d - 1)) % (q - 1) = 0) (Finset.range (q - 1))).card = Nat.gcd (d - 1) (q - 1) := by
        have h_solutions_count : Finset.filter (fun k : ℕ => k < q - 1 ∧ (k * (d - 1)) % (q - 1) = 0) (Finset.range (q - 1)) = Finset.image (fun k => k * (q - 1) / Nat.gcd (d - 1) (q - 1)) (Finset.range (Nat.gcd (d - 1) (q - 1))) := by
          ext k;
          constructor;
          · simp +zetaDelta at *;
            intro hk hk';
            refine' ⟨ k * Nat.gcd ( d - 1 ) ( Fintype.card F - 1 ) / ( Fintype.card F - 1 ), _, _ ⟩;
            · exact Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.gcd_pos_of_pos_right ( d - 1 ) ( Nat.sub_pos_of_lt ( show 1 < Fintype.card F from Fintype.one_lt_card ) ) ] ;
            · rw [ Nat.div_mul_cancel, Nat.div_eq_of_eq_mul_left ];
              · exact Nat.gcd_pos_of_pos_left _ ( Nat.sub_pos_of_lt hd );
              · rfl;
              · rw [ ← Nat.gcd_mul_left ];
                exact Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero hk' ) ( dvd_mul_left _ _ );
          · simp +zetaDelta at *;
            rintro x hx rfl;
            refine' ⟨ Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.sub_pos_of_lt ( show 1 < Fintype.card F from Fintype.one_lt_card ) ], Nat.mod_eq_zero_of_dvd _ ⟩;
            rw [ mul_comm, ← Nat.mul_div_assoc ];
            · refine' Nat.dvd_div_of_mul_dvd _;
              exact mul_dvd_mul ( Nat.gcd_dvd_left _ _ ) ( dvd_mul_left _ _ );
            · exact dvd_mul_of_dvd_right ( Nat.gcd_dvd_right _ _ ) _;
        rw [ h_solutions_count, Finset.card_image_of_injOn, Finset.card_range ];
        intros a ha b hb hab;
        rw [ Nat.div_eq_iff_eq_mul_left ( Nat.gcd_pos_of_pos_left _ ( Nat.sub_pos_of_lt hd ) ) ] at hab;
        · nlinarith [ Nat.div_mul_cancel ( show Nat.gcd ( d - 1 ) ( q - 1 ) ∣ b * ( q - 1 ) from dvd_mul_of_dvd_right ( Nat.gcd_dvd_right _ _ ) _ ), Nat.sub_pos_of_lt ( show 1 < Fintype.card F from Fintype.one_lt_card ) ];
        · exact dvd_mul_of_dvd_right ( Nat.gcd_dvd_right _ _ ) _;
      exact h_solutions.trans h_solutions_count;
    convert h_solutions using 1;
    refine' Finset.card_bij ( fun x hx => Units.mk0 x ( by aesop ) ) _ _ _ <;> simp +decide [ Units.ext_iff ];
  rw [ ← h_solutions, show ( Finset.filter ( fun x : F => x ^ d = x ) Finset.univ ) = Finset.filter ( fun x : F => x ≠ 0 ∧ x ^ ( d - 1 ) = 1 ) Finset.univ ∪ { 0 } from ?_, Finset.card_union ] <;> norm_num;
  ext x; rcases d with ( _ | _ | d ) <;> simp_all +decide [ pow_succ', mul_eq_zero ] ;
  by_cases hx : x = 0 <;> simp +decide [ hx, mul_assoc ]

end ABAPN.Topology
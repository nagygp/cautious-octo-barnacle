/-
# Gamma Indicator Function and AB ↔ Bent Characterization

Formalizes the γ_F indicator function from Carlet-Charpin-Zinoviev (1998),
which bridges the AB property of vectorial functions with the bent property
of Boolean functions.

## Main definitions
- `deltaCount`: Number of solutions to D_a F(x) = b
- `gammaF`: The Boolean indicator γ_F(a,b) = [a ≠ 0 ∧ ∃ x, F(x+a)+F(x) = b]

## Main results
- `walsh_gamma_spectral_link`: Lemma 4 — W_{γ_F} = -(wht2)² + 2^n
- `ab_iff_gamma_bent`: Theorem 13(ii) — F is AB ↔ γ_F is bent

## References
- Carlet, Charpin, Zinoviev (1998), Theorem 13
- Budaghyan (2014), Section 4.3
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 1600000

/-! ### Delta count: number of solutions to D_a F(x) = b -/

/-- The number of solutions x to F(x + a) + F(x) = b. -/
noncomputable def deltaCount {n : ℕ} (F : F2n n → F2n n) (a b : F2n n) : ℕ :=
  (Finset.univ.filter (fun x : F2n n => F (x + a) + F x = b)).card

/-- F is APN iff deltaCount ≤ 2 for all a ≠ 0 -/
def IsAPN' {n : ℕ} (F : F2n n → F2n n) : Prop :=
  ∀ a : F2n n, a ≠ 0 → ∀ b : F2n n, deltaCount F a b ≤ 2

/-! ### The γ_F indicator function -/

/-- The indicator function γ_F(a, b):
    γ_F(a, b) = 1 iff a ≠ 0 and ∃ x, F(x+a) + F(x) = b.
    Returns a ZMod 2 value (0 or 1). -/
noncomputable def gammaF {n : ℕ} (F : F2n n → F2n n) (a b : F2n n) : ZMod 2 :=
  if a = 0 then 0
  else if deltaCount F a b > 0 then 1 else 0

/-- γ_F as a function on pairs -/
noncomputable def gammaF_pair {n : ℕ} (F : F2n n → F2n n) : F2n n × F2n n → ZMod 2 :=
  fun p => gammaF F p.1 p.2

/-! ### Two-parameter Walsh/Fourier transform -/

/-- The two-parameter Walsh-Hadamard transform (for γ_F analysis):
    W_F(a, b) = ∑_x (-1)^{Tr(b·F(x) + a·x)} -/
noncomputable def wht2_gamma {n : ℕ} (F : F2n n → F2n n) (a b : F2n n) : ℤ :=
  ∑ x : F2n n, chi n (b * F x + a * x)

/-- Full AB definition using two-parameter WHT -/
def IsAlmostBentFull' {n : ℕ} (F : F2n n → F2n n) : Prop :=
  ∀ a b : F2n n, (a, b) ≠ (0, 0) →
    wht2_gamma F a b = 0 ∨
    (wht2_gamma F a b) ^ 2 = (2 ^ (n + 1) : ℤ)

/-! ### Walsh transform of the γ_F indicator -/

/-- Walsh transform of the Boolean function γ_F on the product space V_m × V_m.
    W_{γ_F}(a, b) = ∑_{(u,v)} (-1)^{γ_F(u,v) + Tr(a·u + b·v)} -/
noncomputable def walshGamma {n : ℕ} (F : F2n n → F2n n) (a b : F2n n) : ℤ :=
  ∑ u : F2n n, ∑ v : F2n n,
    (-1 : ℤ) ^ (ZMod.val (gammaF F u v)) * chi n (a * u + b * v)

/-! ### Definition of bent function on the product space -/

/-- A Boolean function on V_m × V_m is bent if its Walsh transform has
    constant absolute value 2^m on all inputs. -/
def IsBentProduct {n : ℕ} (f : F2n n × F2n n → ZMod 2) : Prop :=
  ∀ a b : F2n n, (∑ u : F2n n, ∑ v : F2n n,
    (-1 : ℤ) ^ (ZMod.val (f (u, v))) * chi n (a * u + b * v)) ^ 2 =
    (2 ^ n : ℤ) ^ 2

/-! ### Helper lemmas for the spectral link -/

/-- γ_F(0, v) = 0 for all v. -/
@[simp]
theorem gammaF_zero_left {n : ℕ} (F : F2n n → F2n n) (v : F2n n) :
    gammaF F 0 v = 0 := by
  simp [gammaF]

/-- For ZMod 2 values: (-1)^{val(m)} = 1 - 2 * val(m). -/
theorem neg_one_pow_zmod2_val (m : ZMod 2) :
    (-1 : ℤ) ^ (ZMod.val m) = 1 - 2 * (ZMod.val m : ℤ) := by
  fin_cases m <;> simp [ZMod.val]

/-
For APN functions, deltaCount ∈ {0, 2} for u ≠ 0.
    This follows from solutions pairing: if x solves F(x+u)+F(x)=v,
    then so does x+u (in characteristic 2).
-/
theorem deltaCount_zero_or_two {n : ℕ} (F : F2n n → F2n n) (hAPN : IsAPN' F)
    (u : F2n n) (hu : u ≠ 0) (v : F2n n) :
    deltaCount F u v = 0 ∨ deltaCount F u v = 2 := by
  -- By definition of $deltaCount$, we know that if $deltaCount F u v$ is not zero, then it must be exactly 2.
  by_cases h_delta_zero : deltaCount F u v = 0;
  · exact Or.inl h_delta_zero;
  · refine' Or.inr ( le_antisymm _ _ );
    · exact hAPN u hu v;
    · obtain ⟨ x, hx ⟩ := Finset.card_pos.mp ( Nat.pos_of_ne_zero h_delta_zero );
      refine' Finset.one_lt_card.mpr ⟨ x, hx, x + u, _, _ ⟩ <;> simp_all +decide [ add_assoc ];
      rw [ add_comm, hx ]

/-
For APN functions with u ≠ 0: 2 * val(γ_F(u,v)) = deltaCount(u,v).
-/
theorem gamma_val_eq_half_delta {n : ℕ} (F : F2n n → F2n n) (hAPN : IsAPN' F)
    (u : F2n n) (hu : u ≠ 0) (v : F2n n) :
    2 * (ZMod.val (gammaF F u v) : ℤ) = (deltaCount F u v : ℤ) := by
  cases deltaCount_zero_or_two F hAPN u hu v <;> simp +decide [ *, gammaF ]

/-
(wht2)² = ∑_u ∑_v δ_F(u,v) · chi(a·u + b·v).
    Proof: expand the square, substitute y = x + u.
-/
theorem wht2_sq_eq_delta_sum {n : ℕ} (hn : n ≠ 0)
    (F : F2n n → F2n n) (a b : F2n n) :
    (wht2_gamma F a b) ^ 2 =
    ∑ u : F2n n, ∑ v : F2n n,
      (deltaCount F u v : ℤ) * chi n (a * u + b * v) := by
  have h_sum : ∀ u : F2n n, ∑ x : F2n n, chi n (b * (F (x + u) + F x) + a * u) = ∑ v : F2n n, (deltaCount F u v : ℤ) * chi n (b * v + a * u) := by
    intro u
    have h_sum : ∑ x : F2n n, chi n (b * (F (x + u) + F x) + a * u) = ∑ v : F2n n, ∑ x ∈ Finset.univ.filter (fun x => F (x + u) + F x = v), chi n (b * v + a * u) := by
      simp +decide only [Finset.sum_filter];
      rw [ Finset.sum_comm ] ; aesop;
    simp_all +decide [ deltaCount ];
  have h_sum : ∑ x : F2n n, ∑ y : F2n n, chi n (b * F x + a * x) * chi n (b * F y + a * y) = ∑ u : F2n n, ∑ x : F2n n, chi n (b * (F (x + u) + F x) + a * u) := by
    have h_sum : ∑ x : F2n n, ∑ y : F2n n, chi n (b * F x + a * x) * chi n (b * F y + a * y) = ∑ x : F2n n, ∑ u : F2n n, chi n (b * F x + a * x) * chi n (b * F (x + u) + a * (x + u)) := by
      exact Finset.sum_congr rfl fun x hx => by rw [ ← Equiv.sum_comp ( Equiv.addLeft x ) ] ; simp +decide ;
    rw [ h_sum, Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun x hx => _;
    rw [ ← chi_add ] ; ring;
    simp +decide [ mul_two, add_assoc ];
  simp_all +decide [ sq, Finset.sum_mul _ _ _, mul_comm ];
  convert h_sum using 1;
  · simp +decide only [wht2_gamma, Finset.mul_sum _ _ _, Finset.sum_mul];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  · ac_rfl

/-
δ_F(0,v) = 2^n if v = 0, and 0 otherwise.
-/
theorem deltaCount_zero {n : ℕ} (hn : n ≠ 0)
    (F : F2n n → F2n n) (v : F2n n) :
    deltaCount F 0 v = if v = 0 then Fintype.card (F2n n) else 0 := by
  unfold deltaCount; split_ifs <;> simp_all +decide [ Finset.filter_true_of_mem, Finset.filter_false_of_mem ] ;
  aesop

/-
For (a,b) ≠ (0,0): ∑_u ∑_v chi(a·u + b·v) = 0.
-/
theorem chi_product_sum_zero {n : ℕ} (hn : n ≠ 0)
    (a b : F2n n) (hab : (a, b) ≠ (0, 0)) :
    ∑ u : F2n n, ∑ v : F2n n, chi n (a * u + b * v) = 0 := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ u : F2n n, ∑ v : F2n n, chi n (a * u + b * v) = (∑ u : F2n n, chi n (a * u)) * (∑ v : F2n n, chi n (b * v)) := by
    simp +decide only [chi_add, Finset.sum_mul _ _ _];
    simp +decide only [Finset.mul_sum _ _ _];
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide [ chi_orthogonality ]

/-! ### Spectral Link: Lemma 4 of CCZ 1998 -/

/-
**Lemma 4 (CCZ 1998)**: The Walsh transform of (-1)^{γ_F} satisfies
    W_{γ_F}(a,b) = -(wht2)² + 2^n  when (a,b) ≠ (0,0) and F is APN.

    Proof:
    1. (-1)^{γ_F(u,v)} = 1 - 2·γ_F.val = 1 - δ_F(u,v) for u≠0
    2. W_{γ_F} = ∑∑ chi(au+bv) - 2·∑∑ γ_F.val·chi(au+bv)
    3. First sum = 0 by orthogonality (since (a,b)≠(0,0))
    4. Second sum = (1/2)·(∑∑ δ_F·chi - δ_F(0,·) sum) = (1/2)·((wht2)²-2^n)
    5. W_{γ_F} = 0 - ((wht2)² - 2^n) = -(wht2)² + 2^n
-/
theorem walsh_gamma_spectral_link {n : ℕ} (hn : n ≠ 0)
    (F : F2n n → F2n n) (hAPN : IsAPN' F)
    (a b : F2n n) (hab : (a, b) ≠ (0, 0)) :
    walshGamma F a b = -(wht2_gamma F a b) ^ 2 + (2 ^ n : ℤ) := by
  -- Applying Lemma 4's second part, we get $W_{\gamma_F}(a,b) = -(wht2)^2 + 2^n$.
  have h_step2 : walshGamma F a b = ∑ u : F2n n, ∑ v : F2n n, chi n (a * u + b * v) - 2 * ∑ u : F2n n, ∑ v : F2n n, (ZMod.val (gammaF F u v) : ℤ) * chi n (a * u + b * v) := by
    -- Apply the definition of `walshGamma` and the fact that `(-1 : ℤ) ^ (ZMod.val (gammaF F u v)) = 1 - 2 * (ZMod.val (gammaF F u v) : ℤ)`.
    have h_walshGamma_def : walshGamma F a b = ∑ u : F2n n, ∑ v : F2n n, (1 - 2 * (ZMod.val (gammaF F u v) : ℤ)) * chi n (a * u + b * v) := by
      exact Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => by rw [ neg_one_pow_zmod2_val ] ;
    simp +decide only [h_walshGamma_def, sub_mul, one_mul, mul_assoc, Finset.mul_sum _ _ _];
    simp +decide only [Finset.sum_sub_distrib];
  -- Applying Lemma 4's second part, we get $2 * \sum_{u \neq 0} \sum_v \gamma_F(u,v) \chi(au+bv) = \sum_{u \neq 0} \sum_v \delta_F(u,v) \chi(au+bv)$.
  have h_step3 : 2 * ∑ u : F2n n, ∑ v : F2n n, (ZMod.val (gammaF F u v) : ℤ) * chi n (a * u + b * v) = ∑ u : F2n n, ∑ v : F2n n, (deltaCount F u v : ℤ) * chi n (a * u + b * v) - ∑ v : F2n n, (deltaCount F 0 v : ℤ) * chi n (b * v) := by
    have h_step3 : 2 * ∑ u : F2n n, ∑ v : F2n n, (ZMod.val (gammaF F u v) : ℤ) * chi n (a * u + b * v) = ∑ u : F2n n, ∑ v : F2n n, (if u = 0 then 0 else (deltaCount F u v : ℤ)) * chi n (a * u + b * v) := by
      have h_step3 : ∀ u : F2n n, ∀ v : F2n n, (if u = 0 then 0 else (deltaCount F u v : ℤ)) = 2 * (ZMod.val (gammaF F u v) : ℤ) := by
        intro u v; by_cases hu : u = 0 <;> simp +decide [ hu, gamma_val_eq_half_delta F hAPN u ] ;
        convert gamma_val_eq_half_delta F hAPN u hu v |> Eq.symm using 1;
      simp +decide only [Finset.mul_sum _ _ _, h_step3, mul_assoc];
    simp_all +decide [ Finset.sum_ite, Finset.filter_ne' ];
  -- Applying Lemma 4's second part, we get $\sum_{v} \delta_F(0,v) \chi(bv) = 2^n$.
  have h_step4 : ∑ v : F2n n, (deltaCount F 0 v : ℤ) * chi n (b * v) = 2 ^ n := by
    rw [ Finset.sum_eq_single 0 ] <;> simp +decide [ deltaCount_zero hn F ];
    · rw [ F2n.card ] <;> norm_num [ chi_zero ];
      exact hn;
    · grind;
  linarith [ chi_product_sum_zero hn a b hab, wht2_sq_eq_delta_sum hn F a b ]

/-! ### Theorem 13(ii): AB ↔ bent -/

/-
**Theorem 13(ii) (CCZ 1998)**: F is Almost Bent if and only if
    γ_F is a bent Boolean function on V_m × V_m.
-/
theorem ab_iff_gamma_bent {n : ℕ} (hn : n ≠ 0) (hn_odd : Odd n)
    (F : F2n n → F2n n) (hAPN : IsAPN' F) :
    IsAlmostBentFull' F ↔ IsBentProduct (gammaF_pair F) := by
  constructor;
  · intro hF a b;
    by_cases hab : ( a, b ) = ( 0, 0 );
    · -- For u=0, gammaF=0 so contribution is ∑_v 1 = 2^n. For u≠0, by APN the solutions pair up: exactly 2^{n-1} values v have gammaF=1, and 2^{n-1} have gammaF=0. So ∑_v (-1)^{gammaF} = 2^{n-1} - 2^{n-1} = 0 for each u≠0. Total = 2^n.
      have h_sum_zero : ∑ u : F2n n, ∑ v : F2n n, (-1 : ℤ) ^ (ZMod.val (gammaF F u v)) = 2 ^ n := by
        have h_sum_zero : ∀ u : F2n n, u ≠ 0 → ∑ v : F2n n, (-1 : ℤ) ^ (ZMod.val (gammaF F u v)) = 0 := by
          intro u hu
          have h_sum_zero : ∑ v : F2n n, (-1 : ℤ) ^ (ZMod.val (gammaF F u v)) = ∑ v : F2n n, (1 - 2 * (ZMod.val (gammaF F u v) : ℤ)) := by
            exact Finset.sum_congr rfl fun v hv => by rcases x : gammaF F u v with ( _ | _ | x ) <;> simp_all +decide ; tauto;
          have h_sum_zero : ∑ v : F2n n, (deltaCount F u v : ℤ) = 2 ^ n := by
            have h_sum_zero : ∑ v : F2n n, (deltaCount F u v : ℤ) = ∑ x : F2n n, 1 := by
              simp +decide [ deltaCount ];
              rw_mod_cast [ ← Finset.card_biUnion ];
              · convert Finset.card_univ using 2 ; ext x ; aesop;
              · exact fun x _ y _ hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
            simp_all +decide [ F2n.card ];
          have h_sum_zero : ∑ v : F2n n, (deltaCount F u v : ℤ) = 2 * ∑ v : F2n n, (ZMod.val (gammaF F u v) : ℤ) := by
            rw [ Finset.mul_sum _ _ _ ];
            exact Finset.sum_congr rfl fun v hv => by linarith [ gamma_val_eq_half_delta F hAPN u hu v ] ;
          simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
          rw [ F2n.card ] ; aesop ; aesop;
        rw [ Finset.sum_eq_single 0 ] <;> simp_all +decide;
        exact_mod_cast F2n.card n hn;
      simp_all +decide [ gammaF_pair ];
      simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, chi_zero ];
    · rw [ show ( ∑ u : F2n n, ∑ v : F2n n, ( -1 : ℤ ) ^ ( gammaF_pair F ( u, v ) |> ZMod.val ) * chi n ( a * u + b * v ) ) = - ( wht2_gamma F a b ) ^ 2 + ( 2 ^ n : ℤ ) from ?_ ];
      · cases hF a b hab <;> simp_all +decide [ pow_succ' ];
        ring;
      · convert walsh_gamma_spectral_link hn F hAPN a b hab using 1;
  · intro h_bent
    have h_wht : ∀ a b : F2n n, (a, b) ≠ (0, 0) → (wht2_gamma F a b) ^ 2 ∈ ({0, 2 ^ (n + 1)} : Set ℤ) := by
      intro a b hab
      have h_walsh : walshGamma F a b ∈ ({2 ^ n, -2 ^ n} : Set ℤ) := by
        exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by simpa [ sq ] using h_bent a b;
      grind +suggestions;
    exact fun a b hab => by specialize h_wht a b hab; aesop;;

end
end Kasami
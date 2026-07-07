import RequestProject.Weil.ArtinSchreier
import RequestProject.Weil.Frobenius

/-!
# The absolute trace, additive orthogonality, and the Artin–Schreier dictionary

This module supplies the trace/orthogonality groundwork that the bridge identity `exists_bridge`
(in `Weil.WeilBound`) rests on.  The point is to express the size of an Artin–Schreier fibre
`#{y : ℘(y) = c}` as a character sum over the prime subfield.

The organising object is the **absolute trace** `Tr_{𝔽_q/𝔽_p} : 𝔽_q → 𝔽_p`, here realised
concretely (avoiding `Algebra (ZMod p) F` instance issues) as the Frobenius power sum
`Tr(c) = ∑_{i<n} c^{pⁱ}` where `q = pⁿ`.  Its key properties:

* it is additive and lands in the prime subfield `𝔽_p` (`absTrace_pow_char_eq_self`);
* **additive Hilbert 90 / Artin–Schreier:** `c` is in the image of `℘` iff `Tr(c) = 0`
  (`asOp_solvable_iff_absTrace_zero`);
* combined with `asOp_fiber_card`, each fibre has size `p·[Tr c = 0]` (`card_asOp_fiber_eq`);
* **additive orthogonality:** there is a standard nontrivial character `ψ₀` with
  `∑_{t∈𝔽_p} ψ₀(t·c) = p·[Tr c = 0]` (`exists_standard_char`).

Chaining these gives exactly the pointwise identity behind `exists_bridge`.

## Main statements (skeletons)
* `Weil.absTrace` — the absolute trace `∑_{i<n} c^{pⁱ}`.
* `Weil.absTrace_add`, `Weil.absTrace_pow_char_eq_self`, `Weil.absTrace_mem_primeField`.
* `Weil.asOp_solvable_iff_absTrace_zero` — additive Hilbert 90.
* `Weil.card_asOp_fiber_eq` — fibre size `= p·[Tr c = 0]`.
* `Weil.exists_standard_char` — additive orthogonality over `𝔽_p`.
* `Weil.bridge_pointwise` — the pointwise identity feeding `exists_bridge`.
-/

open scoped BigOperators
open Polynomial
open Classical

namespace Weil

variable {F : Type*} [Field F] [Fintype F]

/-- The **absolute trace** `Tr_{𝔽_q/𝔽_p}(c) = ∑_{i<n} c^{pⁱ}`, where `q = pⁿ`.  This is the standard
Frobenius power sum; it is additive and takes values in the prime subfield `𝔽_p`. -/
noncomputable def absTrace (c : F) : F :=
  ∑ i ∈ Finset.range ((Fintype.card F).factorization (ringChar F)), c ^ (ringChar F ^ i)

/-
The absolute trace is additive.
-/
lemma absTrace_add (a b : F) : absTrace (a + b) = absTrace a + absTrace b := by
  unfold absTrace; simp +decide [ ← Finset.sum_add_distrib ] ;
  exact Finset.sum_congr rfl fun _ _ => Weil.Frobenius.frobenius_pow_iterate_add _ _ _

/-
The absolute trace is fixed by Frobenius, hence lands in the prime subfield `𝔽_p`.
-/
lemma absTrace_pow_char_eq_self (c : F) : (absTrace c) ^ (ringChar F) = absTrace c := by
  -- By definition of absolute trace, we have `absTrace c = ∑ i ∈ Finset.range n, c ^ (ringChar F ^ i)`.
  set n := (Fintype.card F).factorization (ringChar F) with hn
  have h_n : Fintype.card F = (ringChar F) ^ n := by
    have := FiniteField.card F ( ringChar F );
    aesop;
  have h_telescope : ∑ i ∈ Finset.range n, c ^ (ringChar F ^ (i + 1)) = ∑ i ∈ Finset.range n, c ^ (ringChar F ^ i) - c + c ^ (ringChar F ^ n) := by
    exact Nat.recOn n ( by norm_num ) fun n ih => by simp +decide [ Finset.sum_range_succ, pow_succ, pow_mul ] at * ; linear_combination ih;
  -- By definition of absolute trace, we have `absTrace c = ∑ i ∈ Finset.range n, c ^ (ringChar F ^ i)`. Raising both sides to the power of `ringChar F`, we get `(absTrace c) ^ ringChar F = (∑ i ∈ Finset.range n, c ^ (ringChar F ^ i)) ^ ringChar F`.
  have h_absTrace_pow : (absTrace c) ^ ringChar F = ∑ i ∈ Finset.range n, c ^ (ringChar F ^ (i + 1)) := by
    have h_absTrace_pow : ∀ (s : Finset ℕ) (f : ℕ → F), (∑ i ∈ s, f i) ^ ringChar F = ∑ i ∈ s, f i ^ ringChar F := by
      intro s f; induction s using Finset.induction <;> simp +decide [ *, add_pow_char ] ;
      · intro h; simp_all +singlePass ;
        have := FiniteField.card F ( ringChar F ) ; simp_all +decide ;
      · grind +suggestions;
    convert h_absTrace_pow ( Finset.range n ) ( fun i => c ^ ringChar F ^ i ) using 1 ; simp +decide [ pow_succ, pow_mul ];
  rw [ h_absTrace_pow, h_telescope, ← h_n, Weil.Frobenius.pow_card_eq_self ] ; simp +decide [ absTrace ];
  rfl

/-- The absolute trace takes values in the prime subfield. -/
lemma absTrace_mem_primeField (c : F) : absTrace c ∈ primeField F := by
  simp only [primeField, Finset.mem_filter, Finset.mem_univ, true_and]
  exact absTrace_pow_char_eq_self c

/-
The absolute trace is fixed under the Frobenius `x ↦ x^p`: `absTrace (c^p) = absTrace c`.
-/
lemma absTrace_pow_char (c : F) : absTrace (c ^ (ringChar F)) = absTrace c := by
  have h_absTrace : ∀ c : F, absTrace (c ^ ringChar F) = absTrace c := by
    intro c
    have h_card : Fintype.card F = (ringChar F) ^ ((Fintype.card F).factorization (ringChar F)) := by
      have := FiniteField.card F ( ringChar F );
      aesop;
    have h_absTrace : absTrace (c ^ ringChar F) = ∑ i ∈ Finset.range ((Fintype.card F).factorization (ringChar F)), c ^ (ringChar F ^ (i + 1)) := by
      exact Finset.sum_congr rfl fun _ _ => by ring;
    have h_absTrace : ∑ i ∈ Finset.range ((Fintype.card F).factorization (ringChar F)), c ^ (ringChar F ^ (i + 1)) = ∑ i ∈ Finset.range ((Fintype.card F).factorization (ringChar F)), c ^ (ringChar F ^ i) - c + c ^ (ringChar F ^ ((Fintype.card F).factorization (ringChar F))) := by
      have := Finset.sum_range_sub ( fun i => c ^ ringChar F ^ i ) ( ( Fintype.card F ).factorization ( ringChar F ) ) ; simp +decide [ pow_succ, pow_mul ] at this ⊢; linear_combination' this;
    rw [ ← h_card, Weil.Frobenius.pow_card_eq_self ] at * ; simp_all +singlePass [ absTrace ];
  rw [ h_absTrace ]

/-
**Forward direction.**  Every Artin–Schreier value `℘(y) = y^p - y` has vanishing trace.
-/
lemma absTrace_asOp (y : F) : absTrace (asOp y) = 0 := by
  -- Apply the additivity of the absolute trace to split the sum into two parts.
  have h_split : absTrace (y ^ (ringChar F) - y) = absTrace (y ^ (ringChar F)) - absTrace y := by
    have h_absTrace_add : ∀ (a b : F), absTrace (a - b) = absTrace a - absTrace b := by
      intro a b; have := absTrace_add ( a - b ) b; aesop;
    exact h_absTrace_add _ _;
  exact h_split.trans ( sub_eq_zero.mpr ( Weil.absTrace_pow_char y ) )

/-
The prime subfield `𝔽_p` has exactly `p` elements.
-/
lemma primeField_card : (primeField F).card = ringChar F := by
  refine' le_antisymm _ _;
  · have h_primeField_card : (primeField F).card ≤ (Polynomial.X ^ (ringChar F) - Polynomial.X : F[X]).roots.toFinset.card := by
      refine Finset.card_le_card ?_;
      simp +decide [ Finset.subset_iff, primeField ];
      exact fun x hx => ⟨ sub_ne_zero_of_ne <| ne_of_apply_ne Polynomial.natDegree <| by rw [ Polynomial.natDegree_X_pow, Polynomial.natDegree_X ] ; linarith [ show ringChar F > 1 from Nat.Prime.one_lt <| CharP.char_is_prime F <| ringChar F ], sub_eq_zero.mpr hx ⟩;
    refine' le_trans h_primeField_card ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
    rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num [ Polynomial.natDegree_X_pow, show ringChar F > 1 from CharP.char_is_prime F _ |> Nat.Prime.one_lt ];
  · have h_subset : Finset.image (fun m : ℕ => (m : F)) (Finset.range (ringChar F)) ⊆ primeField F := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx;
      have h_frobenius : ∀ (m : ℕ), (m : F) ^ (ringChar F) = m := by
        intro m; induction m <;> simp_all +decide [ pow_succ' ] ;
        · grind +extAll;
        · haveI := Fact.mk ( show Nat.Prime ( ringChar F ) from by
                              exact CharP.char_is_prime F ( ringChar F ) ) ; simp_all +decide [ add_pow_char ] ;
      exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_frobenius m ⟩;
    refine' le_trans _ ( Finset.card_mono h_subset );
    rw [ Finset.card_image_of_injOn, Finset.card_range ];
    intro m hm n hn hmn; simp_all +decide [ CharP.cast_eq_zero_iff F ( ringChar F ) ] ;
    have := ringChar.spec F;
    specialize this ( m - n ) ; cases le_total m n <;> simp_all +decide [ Nat.cast_sub ];
    · have := ringChar.spec F ( n - m ) ; simp_all +decide [ Nat.cast_sub ‹_› ] ;
      exact le_antisymm ‹_› ( Nat.le_of_not_lt fun h => by have := Nat.le_of_dvd ( Nat.sub_pos_of_lt h ) this; omega );
    · exact le_antisymm ( Nat.le_of_not_lt fun h => by have := Nat.le_of_dvd ( Nat.sub_pos_of_lt h ) this; omega ) ‹_›

/-
The absolute trace is not identically zero.
-/
lemma absTrace_exists_ne_zero : ∃ c : F, absTrace c ≠ 0 := by
  by_contra! h;
  -- Let $n$ be the degree of the field extension $F/\mathbb{F}_p$, so $q = p^n$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ n ∧ Fintype.card F = (ringChar F) ^ n := Weil.Frobenius.card_eq_char_pow (F := F);
  -- Consider the polynomial $Q := \sum_{i=0}^{n-1} X^{p^i}$.
  set Q : Polynomial F := Finset.sum (Finset.range n) (fun i => Polynomial.X ^ (ringChar F ^ i));
  -- Then $Q.eval x = absTrace x = 0$ for all $x : F$, so every element of $F$ is a root of $Q$.
  have hQ_roots : ∀ x : F, Q.eval x = 0 := by
    simp +zetaDelta at *;
    simp_all +decide [ Polynomial.eval_finset_sum, absTrace ];
    convert h using 3;
    rw [ Nat.Prime.factorization ( CharP.char_is_prime F ( ringChar F ) ) ] ; aesop;
  -- But $Q$ is a nonzero polynomial of degree $p^{n-1}$, so it cannot have all $Fintype.card F$ elements as roots.
  have hQ_nonzero : Q ≠ 0 := by
    refine' ne_of_apply_ne ( fun p => p.coeff ( ringChar F ^ 0 ) ) _ ; simp +decide [ Q ];
    rw [ Finset.card_eq_one.mpr ] <;> norm_num;
    use 0; ext x; simp +decide [ eq_comm ] ;
    exact ⟨ fun hx => hx.2.resolve_left ( by exact not_subsingleton _ ), fun hx => ⟨ hx.symm ▸ hn.1, Or.inr hx ⟩ ⟩
  have hQ_deg : Q.natDegree < Fintype.card F := by
    rw [ Polynomial.natDegree_sum_eq_of_disjoint ];
    · rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
      rw [ Finset.range_add_one, Finset.sup_insert ];
      rcases k : ringChar F with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
      · exact absurd hn ( Nat.ne_of_gt ( Fintype.one_lt_card ) );
      · exact fun i hi => lt_of_le_of_lt ( pow_le_pow_right₀ ( by linarith ) hi.le ) ( lt_mul_of_one_lt_left ( by positivity ) ( by linarith ) );
    · intro i hi j hj hij; simp_all +decide [ Polynomial.X_pow_eq_monomial ] ;
      exact fun h => hij ( Nat.pow_right_injective ( show 1 < ringChar F from Nat.Prime.one_lt ( by have := CharP.char_is_prime F ( ringChar F ) ; aesop ) ) h );
  exact absurd ( Finset.card_le_card ( show Finset.univ ⊆ Q.roots.toFinset from fun x _ => by aesop ) ) ( by rw [ Finset.card_univ ] ; exact not_le_of_gt ( lt_of_le_of_lt ( Multiset.toFinset_card_le _ ) ( lt_of_le_of_lt ( Polynomial.card_roots' _ ) hQ_deg ) ) )

/-
**Additive Hilbert 90 / Artin–Schreier.**  `c` lies in the image of `℘(y) = y^p - y` iff its
absolute trace vanishes.  This identifies the image of `℘` with the kernel of the trace, the
index-`p` subgroup `{Tr = 0}`.
-/
lemma asOp_solvable_iff_absTrace_zero (c : F) :
    (∃ y : F, asOp y = c) ↔ absTrace c = 0 := by
  refine' ⟨ fun ⟨ y, hy ⟩ => by rw [ ← hy, absTrace_asOp ], fun h => _ ⟩;
  -- Let `p = ringChar F` and `q = Fintype.card F`, with `haveI : Fact (Nat.Prime p) := ⟨CharP.char_is_prime F p⟩`.
  set p := ringChar F
  set q := Fintype.card F
  have h_prime : Nat.Prime p := by
    exact CharP.char_is_prime F p
  have h_card : q = p ^ (Nat.factorization q p) := by
    have := FiniteField.card F p; aesop;
  have h_card_pos : 1 ≤ Nat.factorization q p := by
    contrapose! h_card; simp_all +singlePass ;
    exact ne_of_gt ( Fintype.one_lt_card );
  -- Let `P := AddMonoidHom.mk' asOp asOp_add : F →+ F` and `T := AddMonoidHom.mk' absTrace absTrace_add : F →+ F`.
  set P : F →+ F := AddMonoidHom.mk' asOp asOp_add
  set T : F →+ F := AddMonoidHom.mk' absTrace absTrace_add
  have hP : Nat.card P.ker = p := by
    have hP_ker_card : Nat.card P.ker = ringChar F := by
      have hP_ker_card : Nat.card P.ker = Nat.card {y : F | asOp y = 0} := by
        simp +decide [ P, AddMonoidHom.mem_ker ]
      have hP_ker_card : Nat.card {y : F | asOp y = 0} = ringChar F := by
        have hP_ker_card : Nat.card {y : F | asOp y = 0} = Nat.card (primeField F) := by
          congr with x ; simp +decide [ asOp, primeField ];
          rw [ sub_eq_zero ]
        convert primeField_card using 1;
        convert hP_ker_card using 1;
        convert Nat.card_eq_fintype_card;
        any_goals exact { x : F // x ∈ primeField F };
        all_goals try infer_instance;
        · rw [ Nat.card_eq_fintype_card, Fintype.card_coe ];
        · rw [ Nat.card_eq_fintype_card ];
      grind;
    exact hP_ker_card
  have hP_range : Nat.card P.range * p = q := by
    have := AddSubgroup.card_mul_index P.ker;
    rw [ AddSubgroup.index_ker ] at this;
    rw [ mul_comm, ← hP, this, Nat.card_eq_fintype_card ]
  have hT_range : Nat.card T.range = p := by
    have hT_range_div : Nat.card T.range ∣ q := by
      convert Subgroup.card_subgroup_dvd_card ( AddSubgroup.toSubgroup ( AddMonoidHom.range T ) ) using 1;
      simp +decide [ q ]
    have hT_range_gt_one : 1 < Nat.card T.range := by
      obtain ⟨ c₀, hc₀ ⟩ := absTrace_exists_ne_zero ( F := F );
      rw [ Nat.card_eq_fintype_card ];
      refine' Fintype.one_lt_card_iff_nontrivial.mpr _;
      exact ⟨ ⟨ _, ⟨ c₀, rfl ⟩ ⟩, ⟨ _, ⟨ 0, rfl ⟩ ⟩, by simpa using hc₀ ⟩
    have hT_range_le_p : Nat.card T.range ≤ p := by
      have hT_range_le_p : (T.range : Set F) ⊆ primeField F := by
        exact fun x hx => by obtain ⟨ y, rfl ⟩ := hx; exact Weil.absTrace_mem_primeField y;
      have hT_range_le_p : Nat.card T.range ≤ (primeField F).card := by
        rw [ ← Nat.card_eq_finsetCard ] ; exact Set.ncard_le_ncard hT_range_le_p;
      exact hT_range_le_p.trans ( by rw [ primeField_card ] )
    have hT_range_eq_p : Nat.card T.range = p := by
      rw [ h_card ] at hT_range_div;
      rw [ Nat.dvd_prime_pow h_prime ] at hT_range_div;
      rcases hT_range_div with ⟨ k, hk₁, hk₂ ⟩ ; rcases k with ( _ | _ | k ) <;> simp +decide [ hk₂ ] at *;
      · grind;
      · exact hk₂;
      · exact absurd hT_range_le_p ( by rw [ hk₂ ] ; exact not_le_of_gt ( lt_self_pow₀ h_prime.one_lt ( by linarith ) ) )
    exact hT_range_eq_p
  have hT_ker : Nat.card T.ker * p = q := by
    have := AddSubgroup.card_mul_index T.ker; simp +decide [ hT_range ] at this ⊢;
    convert this using 2;
    rw [ ← hT_range, AddSubgroup.index_ker ]
  have hP_range_eq_T_ker : P.range = T.ker := by
    have hP_range_subset_T_ker : P.range ≤ T.ker := by
      rintro _ ⟨ y, rfl ⟩ ; exact absTrace_asOp y;
    have hP_range_eq_T_ker : Nat.card P.range = Nat.card T.ker := by
      nlinarith [ h_prime.two_le ];
    exact SetLike.ext' ( Set.eq_of_subset_of_ncard_le hP_range_subset_T_ker hP_range_eq_T_ker.ge )
  generalize_proofs at *;
  exact SetLike.ext_iff.mp hP_range_eq_T_ker c |>.2 h

/-
The exact fibre count of `℘`: a fibre over `c` has `p` points if `Tr c = 0` and is empty
otherwise.  (Refines `asOp_fiber_card` using `asOp_solvable_iff_absTrace_zero`.)
-/
lemma card_asOp_fiber_eq (c : F) :
    Nat.card {y : F // asOp y = c} = if absTrace c = 0 then ringChar F else 0 := by
  convert asOp_fiber_card c using 1;
  split_ifs <;> simp_all +decide [ Fintype.card_subtype ];
  · exact fun h => False.elim ( h ( Classical.choose_spec ( asOp_solvable_iff_absTrace_zero c |>.2 ‹_› ) ) );
  · intro h x hx; have := asOp_solvable_iff_absTrace_zero c; simp_all +decide [ sub_eq_iff_eq_add ] ;

/-
The absolute trace is `𝔽_p`-semilinear: for `t` in the prime subfield (`t^p = t`),
`absTrace (t * c) = t * absTrace c`.
-/
lemma absTrace_smul (t c : F) (ht : t ^ (ringChar F) = t) :
    absTrace (t * c) = t * absTrace c := by
  unfold absTrace;
  rw [ Finset.mul_sum _ _ _ ];
  refine' Finset.sum_congr rfl fun i hi => _;
  induction i <;> simp_all +decide [ pow_succ, pow_mul ];
  rename_i k hk; rw [ hk ( Nat.lt_of_succ_lt hi ) ] ; simp +decide [ mul_pow, ht ] ;

/-
**The trace as an additive hom to `ZMod p`.**  There is a surjective additive homomorphism
`T : F →+ ZMod p` whose composite with the canonical embedding `ZMod p → F` recovers `absTrace`.
-/
lemma exists_traceHom :
    ∃ T : F →+ ZMod (ringChar F), Function.Surjective T ∧
      ∀ c : F, (ZMod.castHom (dvd_refl (ringChar F)) F) (T c) = absTrace c := by
  have hT : ∃ T : F →+ (ZMod (ringChar F)), ∀ c : F, (ZMod.castHom (dvd_refl (ringChar F)) F) (T c) = absTrace c := by
    have h_range : ∀ c : F, absTrace c ∈ Set.range (ZMod.castHom (dvd_refl (ringChar F)) F) := by
      intro c
      have h_absTrace_mem_primeField : absTrace c ∈ primeField F := by
        exact?
      generalize_proofs at *;
      haveI := Fact.mk ( CharP.char_is_prime F ( ringChar F ) ) ; simp_all +decide [ primeField ] ;
      have h_poly : Polynomial.X ^ ringChar F - Polynomial.X = ∏ x : ZMod (ringChar F), (Polynomial.X - Polynomial.C x) := by
        refine' Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq _ _ _;
        exact Finset.univ;
        · convert Polynomial.degree_sub_lt _ _ _ <;> norm_num [ Polynomial.degree_prod, Polynomial.degree_X_pow_sub_C ];
          · rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num [ this.1.one_lt ];
          · rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> norm_num [ this.1.one_lt ];
          · exact ne_of_apply_ne Polynomial.natDegree ( by rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num <;> linarith [ this.1.two_le ] );
          · rw [ Polynomial.leadingCoeff_prod ];
            rw [ Polynomial.leadingCoeff_sub_of_degree_lt ] <;> norm_num [ this.1.one_lt ];
        · simp +decide [ Polynomial.eval_prod ];
          exact fun x => Eq.symm ( Finset.prod_eq_zero ( Finset.mem_univ x ) ( sub_self x ) );
      replace h_poly := congr_arg ( Polynomial.map ( ZMod.castHom ( dvd_refl ( ringChar F ) ) F ) ) h_poly ; simp_all +decide [ Polynomial.map_prod ] ;
      replace h_poly := congr_arg ( Polynomial.eval ( absTrace c ) ) h_poly ; simp_all +decide [ Polynomial.eval_prod ] ;
      exact Exists.elim ( Finset.prod_eq_zero_iff.mp h_poly.symm ) fun x hx => ⟨ x, sub_eq_zero.mp hx.2 |> Eq.symm ⟩;
    choose T hT using h_range;
    have hT_add : ∀ a b : F, T (a + b) = T a + T b := by
      intro a b;
      have hT_add : (ZMod.castHom (dvd_refl (ringChar F)) F) (T (a + b)) = (ZMod.castHom (dvd_refl (ringChar F)) F) (T a + T b) := by
        simp +decide [ hT, absTrace_add ];
        exact hT a ▸ hT b ▸ rfl;
      have hT_inj : Function.Injective (ZMod.castHom (dvd_refl (ringChar F)) F) := by
        haveI := Fact.mk ( CharP.char_is_prime F ( ringChar F ) ) ; exact RingHom.injective _;
      exact hT_inj hT_add;
    exact ⟨ AddMonoidHom.mk' T hT_add, hT ⟩;
  cases' hT with T hT;
  -- Since $T$ is surjective, we are done.
  use T;
  have h_surjective : Function.Surjective T := by
    have h_nontrivial : ∃ c : F, T c ≠ 0 := by
      obtain ⟨ c, hc ⟩ := absTrace_exists_ne_zero ( F := F );
      exact ⟨ c, fun h => hc <| hT c ▸ by simp +decide [ h ] ⟩
    have h_prime_order : ∀ (H : AddSubgroup (ZMod (ringChar F))), H ≠ ⊥ → H = ⊤ := by
      have h_prime_order : Nat.Prime (ringChar F) := by
        exact CharP.char_is_prime F _;
      haveI := Fact.mk h_prime_order; simp +decide [ AddSubgroup.eq_bot_iff_forall, AddSubgroup.eq_top_iff' ] ;
      intro H x hx hx' y; have := AddSubgroup.card_mul_index H; simp_all +decide [ Nat.Prime.ne_zero ] ;
      have := Nat.dvd_of_mod_eq_zero ( Nat.mod_eq_zero_of_dvd <| dvd_of_mul_right_eq _ this ) ; simp_all +decide [ Nat.dvd_prime h_prime_order ] ;
      cases this <;> simp_all +decide [ Fintype.card_eq_one_iff ];
      · obtain ⟨ a, ha, ha' ⟩ := ‹_›; have := ha' 0 ( H.zero_mem ) ; have := ha' x hx; aesop;
      · have := AddSubgroup.card_mul_index H; simp_all +decide [ Nat.Prime.ne_zero ] ;
    specialize h_prime_order ( AddMonoidHom.range T ) ; simp_all +decide [ AddSubgroup.eq_bot_iff_forall, AddSubgroup.eq_top_iff' ] ;
    exact h_prime_order;
  exact ⟨ h_surjective, hT ⟩

/-
**Additive orthogonality with the standard character.**  There is a nontrivial additive
character `ψ₀` (the standard one `e ∘ Tr`) such that for every `c`,
`∑_{t ∈ 𝔽_p} ψ₀(t·c) = p·[Tr c = 0]`.  This is the character-theoretic incarnation of the fibre
count.
-/
lemma exists_standard_char :
    ∃ ψ₀ : AddChar F ℂ, ψ₀ ≠ 1 ∧
      ∀ c : F, (∑ t ∈ primeField F, ψ₀ (t * c))
        = (if absTrace c = 0 then (ringChar F : ℂ) else 0) := by
  -- Let `p = ringChar F`, `haveI : Fact (Nat.Prime p) := ⟨CharP.char_is_prime F p⟩`, `haveI : CharP F p := ringChar.charP F`, `ι := ZMod.castHom (dvd_refl p) F`.
  set p := ringChar F
  haveI hp_prime : Fact (Nat.Prime p) := ⟨CharP.char_is_prime F p⟩
  haveI hp_char : CharP F p := ringChar.charP F
  set ι : ZMod p →+* F := ZMod.castHom (dvd_refl p) F;
  obtain ⟨T, hT⟩ := exists_traceHom (F := F);
  -- Let `pp := p.toPNat (Fact.out (p := p.Prime)).pos`.
  set pp : ℕ+ := ⟨p, Nat.Prime.pos hp_prime.1⟩
  obtain ⟨e, he⟩ : ∃ e : AddChar (ZMod p) ℂ, e.IsPrimitive := by
    have h_nontrivial : ∃ e : AddChar (ZMod p) ℂ, e ≠ 1 := by
      by_contra! h;
      have h_card : Nat.card (AddChar (ZMod p) ℂ) = p := by
        simp +decide [ Nat.card_eq_fintype_card ];
      rw [ Nat.card_eq_one_iff_unique.mpr ] at h_card <;> norm_num at h_card ⊢ ; linarith [ hp_prime.1.two_le ] ;
      exact ⟨ ⟨ fun e f => h e ▸ h f ▸ rfl ⟩, ⟨ 1 ⟩ ⟩
    generalize_proofs at *; (
    obtain ⟨ e, he ⟩ := h_nontrivial
    generalize_proofs at *; (
    exact ⟨ e, fun b => by
      intro hb h; have := h; simp_all +decide [ AddChar.ext_iff ] ;
      obtain ⟨ x, hx ⟩ := he; specialize this ( x / b ) ; simp_all +decide [ mul_div_cancel₀ ] ; ⟩))
  set ψ₀ : AddChar F ℂ := e.compAddMonoidHom T
  use ψ₀
  constructor
  ·
    intro hψ₀;
    obtain ⟨u, hu⟩ : ∃ u : ZMod p, e u ≠ 1 := by
      contrapose! he;
      simp +decide [ AddChar.IsPrimitive, he ];
      exact ⟨ 1, one_ne_zero, by ext; simp +decide [ he ] ⟩;
    obtain ⟨ c, hc ⟩ := hT.1 u; specialize hψ₀; replace hψ₀ := congr_arg ( fun f => f c ) hψ₀; aesop;
  ·
    intro c
    have h_sum : ∑ t ∈ Finset.image (fun u : ZMod p => ι u) Finset.univ, ψ₀ (t * c) = ∑ u : ZMod p, e (u * T c) := by
      have h_sum : ∀ u : ZMod p, T (ι u * c) = u * T c := by
        intro u
        have h_sum : absTrace (ι u * c) = ι u * absTrace c := by
          convert absTrace_smul ( ι u ) c _ using 1;
          exact map_pow ι u p ▸ by simp +decide [ ZMod.pow_card ] ;
        exact ( ZMod.castHom ( dvd_refl p ) F ).injective ( by aesop );
      rw [ Finset.sum_image ];
      · aesop;
      · exact fun x _ y _ hxy => by simpa using RingHom.injective ι hxy;
    convert h_sum using 1;
    · refine' Finset.sum_subset _ _ <;> intro t ht <;> simp_all +decide [ primeField ];
      · have h_card : Finset.card (Finset.image (fun u : ZMod p => ι u) Finset.univ) = p := by
          rw [ Finset.card_image_of_injective _ fun x y hxy => _, Finset.card_univ ] ; aesop;
          exact RingHom.injective _;
        have h_card : Finset.image (fun u : ZMod p => ι u) Finset.univ = Finset.filter (fun t : F => t ^ p = t) Finset.univ := by
          refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
          · obtain ⟨ u, hu, rfl ⟩ := Finset.mem_image.mp hx; simp +decide [ ← map_pow, ZMod.pow_card ] ;
          · convert Weil.primeField_card.le using 1;
        replace h_card := Finset.ext_iff.mp h_card t; aesop;
      · obtain ⟨ u, rfl ⟩ := ht; simp +decide [ ← map_pow, ZMod.pow_card ] ;
        rw [ ZMod.pow_card ] ; aesop;
    · split_ifs with h;
      · have h_sum_zero : T c = 0 := by
          exact ( ι.injective <| by aesop );
        simp +decide [ h_sum_zero ];
      · have := AddChar.sum_mulShift ( T c ) he;
        grind +suggestions

/-
**Pointwise bridge identity.**  For the standard character `ψ₀`, the size of the fibre of `℘`
over `c` equals the character sum `∑_{t∈𝔽_p} (ψ₀.mulShift t) c`.  Summing this over `c = f(x)` and
using `asPointCount_eq_sum` yields `exists_bridge`.
-/
lemma bridge_pointwise :
    ∃ ψ₀ : AddChar F ℂ, ψ₀ ≠ 1 ∧
      ∀ c : F, (Nat.card {y : F // asOp y = c} : ℂ)
        = ∑ t ∈ primeField F, (ψ₀.mulShift t) c := by
  obtain ⟨ψ₀, hψ₀, hsum⟩ := exists_standard_char (F := F);
  refine' ⟨ ψ₀, hψ₀, fun c => _ ⟩;
  convert hsum c using 1;
  · rw [ hsum, card_asOp_fiber_eq ] ; aesop;
  · convert hsum c using 1

end Weil
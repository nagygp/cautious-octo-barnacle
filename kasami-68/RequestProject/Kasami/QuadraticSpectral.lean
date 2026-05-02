/-
# Phase 3: The Spectral Bridge (Quadratic Forms over 𝔽₂)

A general-purpose spectral library for quadratic forms over 𝔽₂.
This module does NOT reference Kasami, Gold, or any specific function —
it provides the abstract spectral theorem.

## Main Results

- `walsh_quadratic_sq` : |W_Q(a)|² ∈ {0, 2^(n+s)} for quadratic Q with radical of dim s
- `walsh_balanced` : Q balanced ⟹ W_Q(0) = 0
- `parseval_walsh` : ∑_a W_g(a)² = 2^(2n)

## Mathematical Background

For a quadratic form Q : 𝔽₂ⁿ → 𝔽₂ with radical V₀ of dimension s,
the Walsh sum ∑_x χ(Q(x)) decomposes as:
  (∑_{v ∈ V₀} χ(Q(v))) · (∑_{w ∈ W} χ(Q̄(w)))
where W ≅ V/V₀ and Q̄ is non-degenerate on W (dim n-s, necessarily even).

For non-degenerate Q̄ on an even-dimensional space: ∑ χ(Q̄) = ±2^((n-s)/2).
-/
import RequestProject.Kasami.Defs

open scoped Classical
set_option maxHeartbeats 800000

open Finset BigOperators

namespace KasamiData

variable (K : KasamiData)

/-! ## Parseval's Identity -/

/-
Parseval's identity for the Walsh transform:
    ∑_a W_g(a)² = |F|² = 2^(2n).

    This is the orthogonality of the character sum.
-/
theorem parseval_walsh (g : K.F → ZMod 2) :
    ∑ a : K.F, K.walsh g a ^ 2 = (2 : ℤ) ^ (2 * K.n) := by
  -- Expand W_g(a)^2 using the definition of W_g(a).
  have h_expand : ∑ a : K.F, (K.walsh g a) ^ 2 = ∑ a : K.F, ∑ x : K.F, ∑ y : K.F, traceChar (g x + K.Tr (a * x)) * traceChar (g y + K.Tr (a * y)) := by
    unfold KasamiData.walsh;
    simp +decide only [sq, ← mul_sum, ← sum_mul];
  -- By orthogonality of the trace character, $\sum_a \chi(\text{Tr}(az)) = 2^n \cdot [z=0]$.
  have h_ortho : ∀ z : K.F, ∑ a : K.F, traceChar (K.Tr (a * z)) = if z = 0 then 2 ^ K.n else 0 := by
    intro z
    by_cases hz : z = 0;
    · simp +decide [ hz, traceChar ];
      exact mod_cast K.card_F;
    · -- Since $z \neq 0$, the map $a \mapsto \text{Tr}(az)$ is surjective.
      have h_surjective : Function.Surjective (fun a : K.F => K.Tr (a * z)) := by
        have h_surjective : Function.Surjective (fun a : K.F => K.Tr a) := by
          have h_surjective : LinearMap.range (Algebra.trace (ZMod 2) K.F) = ⊤ := by
            refine' Submodule.eq_top_of_finrank_eq _;
            have h_surjective : Function.Surjective (Algebra.trace (ZMod 2) K.F) := by
              convert ( Algebra.trace_surjective ( ZMod 2 ) K.F );
            rw [ LinearMap.range_eq_top.mpr h_surjective ] ; norm_num;
          exact LinearMap.range_eq_top.mp h_surjective;
        exact fun x => by obtain ⟨ a, ha ⟩ := h_surjective x; exact ⟨ a / z, by simpa [ hz, div_mul_cancel₀ ] using ha ⟩ ;
      -- Since the map $a \mapsto \text{Tr}(az)$ is surjective, the sum $\sum_a \chi(\text{Tr}(az))$ is equal to $\sum_{t \in \mathbb{F}_2} \chi(t)$.
      have h_sum_eq : ∑ a : K.F, traceChar (K.Tr (a * z)) = ∑ t : ZMod 2, traceChar t * (Finset.card (Finset.filter (fun a : K.F => K.Tr (a * z) = t) Finset.univ)) := by
        have h_sum_eq : ∑ a : K.F, traceChar (K.Tr (a * z)) = ∑ t : ZMod 2, ∑ a ∈ Finset.filter (fun a : K.F => K.Tr (a * z) = t) Finset.univ, traceChar t := by
          simp +decide only [sum_filter];
          rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
        simp_all +decide [ mul_comm ];
      -- Since the map $a \mapsto \text{Tr}(az)$ is surjective, the number of elements in each fiber is the same.
      have h_fiber_card : ∀ t : ZMod 2, Finset.card (Finset.filter (fun a : K.F => K.Tr (a * z) = t) Finset.univ) = Finset.card (Finset.filter (fun a : K.F => K.Tr (a * z) = 0) Finset.univ) := by
        intro t
        obtain ⟨a₀, ha₀⟩ : ∃ a₀ : K.F, K.Tr (a₀ * z) = t := h_surjective t
        have h_fiber_card_eq : Finset.filter (fun a : K.F => K.Tr (a * z) = t) Finset.univ = Finset.image (fun a : K.F => a + a₀) (Finset.filter (fun a : K.F => K.Tr (a * z) = 0) Finset.univ) := by
          ext a; simp [ha₀];
          simp +decide [ ← ha₀, add_mul, sub_eq_add_neg ];
          grind;
        rw [ h_fiber_card_eq, Finset.card_image_of_injective _ ( add_left_injective a₀ ) ];
      simp_all +decide [ Finset.sum_add_distrib, mul_add ];
      rw [ ← Finset.sum_mul _ _ _ ] ; simp +decide [ traceChar ] ;
  -- Apply the orthogonality relation to each term in the double sum.
  have h_apply_ortho : ∀ x y : K.F, ∑ a : K.F, traceChar (g x + K.Tr (a * x)) * traceChar (g y + K.Tr (a * y)) = if x = y then 2 ^ K.n else 0 := by
    intros x y
    have h_apply_ortho_step : ∑ a : K.F, traceChar (g x + K.Tr (a * x)) * traceChar (g y + K.Tr (a * y)) = ∑ a : K.F, traceChar (g x + g y + K.Tr (a * (x + y))) := by
      refine' Finset.sum_congr rfl fun a _ => _;
      rw [ ← traceChar_add ] ; ring;
      rw [ map_add ] ; ring;
    simp_all +decide [ traceChar_add ];
    split_ifs <;> simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    · simp_all +decide [ ← two_mul, CharTwo.two_eq_zero ];
      cases Fin.exists_fin_two.mp ⟨ g y, rfl ⟩ <;> simp +decide [ * ];
    · grind;
  rw [ h_expand, Finset.sum_comm ];
  rw [ Finset.sum_congr rfl fun y hy => Finset.sum_comm ];
  simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
  rw [ show Fintype.card K.F = 2 ^ K.n from K.card_F ] ; ring;
  norm_cast ; ring

/-! ## First Moment (Inversion) -/

/-
The Walsh transform at a = 0 counts the "bias" of g:
    W_g(0) = |{x : g(x) = 0}| - |{x : g(x) = 1}|.
-/
theorem walsh_zero_bias (g : K.F → ZMod 2) :
    K.walsh g 0 = ↑(Finset.card (Finset.univ.filter fun x => g x = 0)) -
                  ↑(Finset.card (Finset.univ.filter fun x => g x = 1)) := by
  have h_split : ∑ x : K.F, traceChar (g x) = ∑ x ∈ Finset.univ.filter (fun x => g x = 0), traceChar 0 + ∑ x ∈ Finset.univ.filter (fun x => g x = 1), traceChar 1 := by
    rw [ Finset.sum_filter, Finset.sum_filter ];
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun x _ => by rcases g x with ( _ | _ | g ) <;> trivial;
  unfold KasamiData.walsh; aesop;

/-! ## Gold Function: Balanced Property -/

/-
The Gold Boolean function g(x) = Tr(x^(2^k+1)) is balanced:
    exactly half the inputs map to 0 and half to 1.
    Equivalently: W_g(0) = 0.

    Proof sketch: The radical of Q_1 contains 1 (since n is odd,
    Tr(1) = 1 ≠ 0), so the sum over the radical is 1 + (-1) = 0,
    which forces the entire Walsh sum to vanish.
-/
theorem goldWalsh_zero : K.goldWalsh 0 = 0 := by
  convert walsh_zero_bias K ( fun x => K.goldBool x ) using 1;
  -- By definition of $goldBool$, we know that $goldBool(x) = 0$ if and only if $Tr(x^{2^k + 1}) = 0$.
  have h_goldBool_zero : Finset.filter (fun x => K.goldBool x = 0) Finset.univ = Finset.filter (fun x => K.goldBool (x + 1) = 1) Finset.univ := by
    ext x; simp +decide [ KasamiData.goldBool ] ;
    have h_trace : K.Tr ((x + 1) ^ K.goldExp) = K.Tr (x ^ K.goldExp) + K.Tr (x ^ (2 ^ K.k)) + K.Tr x + K.Tr 1 := by
      have h_trace : (x + 1) ^ K.goldExp = x ^ K.goldExp + x ^ (2 ^ K.k) + x + 1 := by
        unfold KasamiData.goldExp; ring;
        rw [ add_pow_char_pow ] ; ring;
      rw [ h_trace, map_add, map_add, map_add ];
    have h_trace : K.Tr (x ^ (2 ^ K.k)) = K.Tr x := by
      have h_trace : ∀ x : K.F, K.Tr (x ^ 2) = K.Tr x := by
        intro x; exact (by
        convert ( Algebra.trace_eq_of_algEquiv ( show K.F ≃ₐ[ZMod 2] K.F from ?_ ) ) x using 1;
        swap;
        constructor;
        rotate_left;
        rotate_left;
        rotate_left;
        exact Equiv.ofBijective ( fun x => x ^ 2 ) ⟨ fun x y hxy => by
          grind, fun x => by
          have h_frobenius : Function.Bijective (fun x : K.F => x ^ 2) := by
            have h_frobenius : Function.Injective (fun x : K.F => x ^ 2) := by
              intro x y hxy;
              grind;
            exact ⟨ h_frobenius, Finite.injective_iff_surjective.mp h_frobenius ⟩;
          exact h_frobenius.surjective x ⟩;
        all_goals norm_num [ sq, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm ];
        · rfl;
        · grind +splitImp;
        · exact fun r => by rw [ ← map_mul ] ; fin_cases r <;> rfl;);
      refine' Nat.recOn K.k _ _ <;> simp_all +decide [ pow_succ, pow_mul ];
    have h_trace : K.Tr 1 = 1 := by
      have h_trace : K.Tr 1 = (Module.finrank (ZMod 2) K.F : ZMod 2) := by
        simp +decide [ KasamiData.Tr ];
        simp +decide [ Algebra.trace ];
        convert LinearMap.trace_one ( ZMod 2 ) K.F;
        ext; simp +decide [ LinearMap.mul ];
      have h_finrank : Module.finrank (ZMod 2) K.F = K.n := by
        haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; erw [ GaloisField.finrank ] ;
        exact ne_of_gt K.n_pos;
      cases Nat.mod_two_eq_zero_or_one K.n <;> simp_all +decide [ Nat.even_iff ];
      · exact absurd ( K.hn_odd ) ( by simp +decide [ *, Nat.dvd_iff_mod_eq_zero ] );
      · rw [ ← Nat.mod_add_div K.n 2, ‹K.n % 2 = _› ] ; norm_num;
        exact Or.inl rfl;
    grind +ring;
  rw [ h_goldBool_zero, eq_comm ];
  rw [ sub_eq_zero, Finset.card_filter, Finset.card_filter ];
  exact_mod_cast Equiv.sum_comp ( Equiv.addRight 1 ) fun x => if K.goldBool x = 1 then 1 else 0

/-! ## Spectral Theorem for Quadratic Forms -/

/-! ## Key Lemma: Tr(x^(2^k)) = Tr(x) -/

/-
The Frobenius trace identity: Tr(x^(2^k)) = Tr(x).
    Since Tr(z) = Tr(z^2) (the Frobenius just permutes the Galois conjugates),
    iterating gives Tr(z^(2^k)) = Tr(z).
-/
theorem trace_frob (x : K.F) : K.Tr (K.frob x) = K.Tr x := by
  have h_frob : ∀ x : K.F, K.Tr (x ^ 2) = K.Tr x := by
    intro x
    have h_tr_inv : ∀ (σ : K.F ≃ₐ[ZMod 2] K.F), ∀ x : K.F, K.Tr (σ x) = K.Tr x := by
      intro σ x; exact (by
      convert Algebra.trace_eq_of_algEquiv σ x using 1);
    convert h_tr_inv _ x using 1;
    swap;
    constructor;
    rotate_left;
    rotate_left;
    rotate_left;
    exact Equiv.ofBijective ( fun x => x ^ 2 ) ⟨ fun x y hxy => by
      grind, fun x => by
      have h_frobenius : Function.Bijective (fun x : K.F => x ^ 2) := by
        have h_frobenius : Function.Injective (fun x : K.F => x ^ 2) := by
          intro x y hxy;
          grind;
        exact ⟨ h_frobenius, Finite.injective_iff_surjective.mp h_frobenius ⟩;
      exact h_frobenius.surjective x ⟩;
    all_goals norm_num [ sq ];
    · exact fun x y => by ring;
    · grind;
    · exact fun r => by rw [ ← map_mul ] ; fin_cases r <;> rfl;
  have h_frob_iter : ∀ j : ℕ, K.Tr (x ^ (2 ^ j)) = K.Tr x := by
    intro j; induction j <;> simp_all +decide [ pow_succ, pow_mul ] ;
  exact h_frob_iter _

/-
Tr(1) = 1 when n is odd.
    Since Tr(1) = n (as an element of 𝔽₂), and n is odd, Tr(1) = 1.
-/
theorem trace_one : K.Tr 1 = 1 := by
  -- The trace of the identity map on a finite-dimensional vector space over a field is the dimension of the space.
  have h_trace_id : Algebra.trace (ZMod 2) K.F 1 = Module.finrank (ZMod 2) K.F := by
    simp +decide [ Algebra.trace ];
    convert LinearMap.trace_one ( ZMod 2 ) K.F;
    exact LinearMap.ext fun x => by simp +decide ;
  have h_finrank : Module.finrank (ZMod 2) K.F = K.n := by
    haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; rw [ GaloisField.finrank ] ;
    exact K.n_ne_zero;
  convert h_trace_id;
  exact h_finrank.symm ▸ by have := K.hn_odd; rcases Nat.even_or_odd' K.n with ⟨ c, d | d ⟩ <;> simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;

/-! ## Substitution Lemma -/

/-
The substitution x → x + 1 in the Walsh sum gives:
    goldWalsh(a) = χ(Tr(1 + a)) · goldWalsh(a).

    This follows from:
    - g(x+1) = g(x) + Tr(x^(2^k)) + Tr(x) + Tr(1) = g(x) + Tr(1) (since Tr(x^(2^k))=Tr(x))
    - Tr(a(x+1)) = Tr(ax) + Tr(a)
    - So g(x+1) + Tr(a(x+1)) = g(x) + Tr(ax) + Tr(1+a)
-/
theorem goldWalsh_subst_one (a : K.F) :
    K.goldWalsh a = traceChar (K.Tr (1 + a)) * K.goldWalsh a := by
  have h_trace_frob : ∀ x : K.F, K.goldBool (x + 1) = K.goldBool x + K.Tr 1 := by
    intro x
    unfold KasamiData.goldBool
    have h_expand : (x + 1) ^ (2 ^ K.k + 1) = x ^ (2 ^ K.k + 1) + x ^ (2 ^ K.k) + x + 1 := by
      haveI := Fact.mk ( show Nat.Prime 2 by decide ) ; ring;
      rw [ add_pow_char_pow ] ; ring;
    have h_trace_frob : K.Tr (x ^ (2 ^ K.k)) = K.Tr x := by
      convert trace_frob K x using 1;
    simp_all +decide [ KasamiData.goldExp ];
    grind;
  -- By definition of the Walsh transform, we can rewrite the sum.
  have h_walsh_def : K.goldWalsh a = ∑ x : K.F, traceChar (K.goldBool (x + 1) + K.Tr (a * (x + 1))) := by
    exact Eq.symm ( Equiv.sum_comp ( Equiv.addRight 1 ) fun x => traceChar ( K.goldBool x + K.Tr ( a * x ) ) );
  -- Substitute h_trace_frob into the sum.
  have h_subst : K.goldWalsh a = ∑ x : K.F, traceChar (K.goldBool x + K.Tr 1 + K.Tr (a * x) + K.Tr a) := by
    simp_all +decide [ mul_add, add_assoc ];
  -- Using the property of the trace character, we can factor out the constant term.
  have h_factor : ∑ x : K.F, traceChar (K.goldBool x + K.Tr 1 + K.Tr (a * x) + K.Tr a) = traceChar (K.Tr 1 + K.Tr a) * ∑ x : K.F, traceChar (K.goldBool x + K.Tr (a * x)) := by
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext x ; simp +decide [ traceChar_add ] ; ring;
  convert h_subst.trans h_factor using 2;
  rw [ map_add ]

/-- **Core spectral lemma**: goldWalsh(a) = 0 when Tr(a) = 0.

    Proof: By goldWalsh_subst_one, W(a) = χ(Tr(1+a)) · W(a).
    When Tr(a) = 0: Tr(1+a) = Tr(1) + Tr(a) = 1 + 0 = 1.
    So W(a) = χ(1) · W(a) = (-1) · W(a), hence 2W(a) = 0,
    and since W(a) ∈ ℤ, W(a) = 0. -/
theorem goldWalsh_zero_of_trace_zero (a : K.F) (ha : K.Tr a = 0) :
    K.goldWalsh a = 0 := by
  have hsub := K.goldWalsh_subst_one a
  have htr : K.Tr (1 + a) = 1 := by rw [map_add, K.trace_one, ha]; simp
  rw [htr] at hsub
  simp [traceChar] at hsub
  linarith

/-
Cardinality of the trace-1 fiber: |{a : Tr(a) = 1}| = 2^(n-1).
-/
theorem card_trace_one :
    Finset.card (Finset.univ.filter fun a : K.F => K.Tr a = 1) =
    2 ^ (K.n - 1) := by
  -- The trace map is surjective, so there exists some $b \in F$ such that $\text{Tr}(b) = 1$.
  obtain ⟨b, hb⟩ : ∃ b : K.F, K.Tr b = 1 := by
    exact ⟨ 1, K.trace_one ⟩;
  -- The set {a | Tr(a) = 1} is in bijection with the set {a | Tr(a) = 0} via the map a ↦ a + b.
  have h_bij : (Finset.univ.filter fun a : K.F => K.Tr a = 1) = Finset.image (fun a => a + b) (Finset.univ.filter fun a : K.F => K.Tr a = 0) := by
    simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    grind;
  have h_card : Finset.card (Finset.univ.filter fun a : K.F => K.Tr a = 0) + Finset.card (Finset.univ.filter fun a : K.F => K.Tr a = 1) = 2 ^ K.n := by
    rw [ ← Finset.card_union_of_disjoint ];
    · rw [ show ( Finset.univ.filter fun a : K.F => K.Tr a = 0 ) ∪ ( Finset.univ.filter fun a : K.F => K.Tr a = 1 ) = Finset.univ from Finset.eq_univ_of_forall fun x => by have := Fin.exists_fin_two.mp ⟨ K.Tr x, rfl ⟩ ; aesop ] ; simp +decide [ K.card_F ];
    · exact Finset.disjoint_filter.mpr ( by aesop );
  rw [ h_bij, Finset.card_image_of_injective _ ( add_left_injective b ) ] at *;
  cases n : K.n <;> simp_all +decide [ pow_succ' ] ; linarith;
  linarith

/-- The bilinear form linearization: T(c) = c^(2^k) + c^(2^(n-k)).
    This is the correct map for the Walsh substitution identity. -/
noncomputable def bilinLin (c : K.F) : K.F := K.frob c + K.frobConj c

/-
Tr(T(c)) = 0: the image of bilinLin lies in ker(Tr).
-/
theorem bilinLin_trace (c : K.F) : K.Tr (K.bilinLin c) = 0 := by
  have h_trace_frobConj : ∀ x : K.F, K.Tr (x ^ (2 ^ (K.n - K.k))) = K.Tr x := by
    have h_trace_frobConj : ∀ x : K.F, K.Tr (x ^ 2) = K.Tr x := by
      unfold KasamiData.Tr;
      intro x;
      have h_trace_frob : ∀ x : K.F, (Algebra.trace (ZMod 2) K.F) (x ^ 2) = (Algebra.trace (ZMod 2) K.F) x := by
        intro x
        have h_trace_frob : ∀ σ : K.F →ₐ[ZMod 2] K.F, (Algebra.trace (ZMod 2) K.F) (σ x) = (Algebra.trace (ZMod 2) K.F) x := by
          have h_trace_frob : ∀ σ : K.F ≃ₐ[ZMod 2] K.F, (Algebra.trace (ZMod 2) K.F) (σ x) = (Algebra.trace (ZMod 2) K.F) x := by
            grind +suggestions;
          intro σ;
          convert h_trace_frob ( AlgEquiv.ofBijective σ ?_ ) using 1;
          exact σ.bijective
        convert h_trace_frob ( show K.F →ₐ[ZMod 2] K.F from { toFun := fun x => x ^ 2, map_one' := by
                                                                norm_num, map_mul' := by
                                                                exact fun x y => mul_pow x y 2, map_zero' := by
                                                                norm_num, map_add' := by
                                                                grind, commutes' := by
                                                                exact fun r => by fin_cases r <;> simp +decide ; } ) using 1;
      exact h_trace_frob x;
    induction' K.n - K.k with k hk <;> simp_all +decide [ pow_succ, pow_mul ];
  convert congr_arg₂ ( · + · ) ( K.trace_frob c ) ( h_trace_frobConj c ) using 1;
  · exact map_add _ _ _;
  · grind

/-
General substitution: substituting x → x + c in goldWalsh(a) gives
    goldWalsh(a) = ±goldWalsh(a + T(c)), so their squares are equal.
    Uses: Tr(c·frob(x)) = Tr(frobConj(c)·x) (the Frobenius adjoint identity).
-/
theorem goldWalsh_subst (a c : K.F) :
    K.goldWalsh a ^ 2 = K.goldWalsh (a + K.bilinLin c) ^ 2 := by
  have h_trace_frob : ∀ x : K.F, K.Tr (c * K.frob x) = K.Tr (K.frobConj c * x) := by
    intro x
    have h_trace_frob : K.Tr (c * x ^ (2 ^ K.k)) = K.Tr ((c ^ (2 ^ (K.n - K.k)) * x) ^ (2 ^ K.k)) := by
      have h_trace_frob : c ^ (2 ^ K.n) = c := by
        have h_card : Fintype.card K.F = 2 ^ K.n := by
          convert K.card_F;
        rw [ ← h_card, FiniteField.pow_card ];
      rw [ mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel ( show K.k ≤ K.n from K.hk_lt.le ) ] ; aesop;
    have h_trace_frob : ∀ z : K.F, K.Tr (z ^ (2 ^ K.k)) = K.Tr z := by
      apply trace_frob;
    aesop;
  have h_goldWalsh_subst : ∑ x : K.F, traceChar (K.goldBool (x + c) + K.Tr (a * (x + c))) = traceChar (K.goldBool c + K.Tr (a * c)) * ∑ x : K.F, traceChar (K.goldBool x + K.Tr ((a + K.bilinLin c) * x)) := by
    have h_goldWalsh_subst : ∀ x : K.F, K.goldBool (x + c) + K.Tr (a * (x + c)) = K.goldBool c + K.Tr (a * c) + (K.goldBool x + K.Tr ((a + K.bilinLin c) * x)) := by
      have h_goldWalsh_subst : ∀ x : K.F, K.goldBool (x + c) = K.goldBool x + K.goldBool c + K.Tr (K.frob x * c + x * K.frob c) := by
        intro x; unfold KasamiData.goldBool; simp +decide [ KasamiData.goldExp ] ; ring;
        simp +decide [ KasamiData.frob, add_pow_char_pow ] ; ring;
        rw [ map_add, map_add ] ; ring;
      simp_all +decide [ mul_add, add_mul, mul_comm, mul_left_comm, add_assoc, add_left_comm, add_comm, KasamiData.bilinLin ];
    simp +decide only [h_goldWalsh_subst, traceChar_add, Finset.mul_sum _ _ _];
  have h_goldWalsh_subst : K.goldWalsh a = traceChar (K.goldBool c + K.Tr (a * c)) * K.goldWalsh (a + K.bilinLin c) := by
    convert h_goldWalsh_subst using 1;
    exact Eq.symm ( Equiv.sum_comp ( Equiv.addRight c ) fun x => traceChar ( K.goldBool x + K.Tr ( a * x ) ) );
  rw [ h_goldWalsh_subst, mul_pow ];
  rw [ traceChar_sq ] ; norm_num

/-
The image of bilinLin covers ker(Tr).
    ker(bilinLin) = F_{2^gcd(2k,n)} = F_2 when gcd(k,n)=1 and n odd.
    So |im| = 2^n/2 = 2^(n-1) = |ker(Tr)|, and im ⊆ ker(Tr).
-/
theorem bilinLin_surj (b : K.F) (hb : K.Tr b = 0) :
    ∃ c : K.F, K.bilinLin c = b := by
  by_contra! h_contra;
  have h_image_card : Finset.card (Finset.image (fun c : K.F => K.bilinLin c) Finset.univ) = 2 ^ (K.n - 1) := by
    -- The kernel of bilinLin is the set of elements c such that c^(2^k) = c^(2^(n-k)).
    have h_kernel : Finset.card (Finset.filter (fun c : K.F => K.bilinLin c = 0) Finset.univ) = 2 := by
      -- Since $K$ is a finite field of characteristic 2, the equation $c^{2^k} = c^{2^{n-k}}$ has exactly two solutions: $c = 0$ and $c = 1$.
      have h_eq : ∀ c : K.F, K.bilinLin c = 0 ↔ c ^ (2 ^ K.k) = c ^ (2 ^ (K.n - K.k)) := by
        unfold KasamiData.bilinLin;
        unfold KasamiData.frob KasamiData.frobConj;
        grind;
      -- Since $c^{2^k} = c^{2^{n-k}}$ implies $c^{2^{2k}} = c$, and $c^{2^n} = c$ for all $c \in K.F$, we have $c^{2^{\gcd(2k,n)}} = c$.
      have h_gcd : ∀ c : K.F, c ^ (2 ^ K.k) = c ^ (2 ^ (K.n - K.k)) → c ^ (2 ^ Nat.gcd (2 * K.k) K.n) = c := by
        intro c hc
        have h_exp : c ^ (2 ^ (2 * K.k)) = c := by
          have h_exp : c ^ (2 ^ (K.n)) = c := by
            have h_exp : ∀ c : K.F, c ^ (2 ^ K.n) = c := by
              intro c
              have h_card : Fintype.card K.F = 2 ^ K.n := by
                convert K.card_F
              rw [ ← h_card, FiniteField.pow_card ];
            exact h_exp c;
          convert congr_arg ( · ^ 2 ^ K.k ) hc using 1 <;> ring;
          rw [ ← pow_add, Nat.sub_add_cancel ( show K.k ≤ K.n from K.hk_lt.le ), h_exp ];
        have h_exp : ∀ m n : ℕ, c ^ (2 ^ m) = c → c ^ (2 ^ n) = c → c ^ (2 ^ Nat.gcd m n) = c := by
          intros m n hm hn;
          have h_exp : ∀ m n : ℕ, c ^ (2 ^ m) = c → c ^ (2 ^ n) = c → c ^ (2 ^ (m % n)) = c := by
            intros m n hm hn
            have h_exp : c ^ (2 ^ m) = c ^ (2 ^ (m % n)) := by
              rw [ ← Nat.mod_add_div m n ] ; simp_all +decide [ pow_add, pow_mul ] ;
              induction m / n <;> simp_all +decide [ pow_succ, pow_mul ];
              rw [ ← pow_mul, mul_comm, pow_mul, hn ];
            grind;
          induction' n using Nat.strong_induction_on with n ih generalizing m;
          by_cases hn_zero : n = 0;
          · aesop;
          · rw [ Nat.gcd_comm, Nat.gcd_rec ];
            simpa [ Nat.gcd_comm ] using ih ( m % n ) ( Nat.mod_lt _ ( Nat.pos_of_ne_zero hn_zero ) ) n hn ( h_exp m n hm hn );
        apply h_exp;
        · assumption;
        · have h_exp : ∀ x : K.F, x ^ (2 ^ K.n) = x := by
            have h_exp : ∀ x : K.F, x ^ (Fintype.card K.F) = x := by
              exact fun x => FiniteField.pow_card x;
            convert h_exp using 1;
            rw [ card_F ];
          exact h_exp c;
      -- Since $\gcd(2k, n) = 1$, we have $c^{2^1} = c$, which simplifies to $c^2 = c$.
      have h_gcd_one : Nat.gcd (2 * K.k) K.n = 1 := by
        exact Nat.Coprime.mul_left ( Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by have := K.hn_odd; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ) K.hk;
      have h_solutions : ∀ c : K.F, c ^ 2 = c → c = 0 ∨ c = 1 := by
        exact fun c hc => or_iff_not_imp_left.mpr fun h => mul_left_cancel₀ h <| by linear_combination' hc;
      rw [ Finset.card_eq_two ];
      use 0, 1;
      simp_all +decide [ Finset.ext_iff ];
      exact fun c => ⟨ fun hc => h_solutions c ( h_gcd c hc ), fun hc => by rcases hc with ( rfl | rfl ) <;> simp +decide [ pow_succ' ] ⟩;
    have h_card_image : ∀ y ∈ Finset.image (fun c : K.F => K.bilinLin c) Finset.univ, Finset.card (Finset.filter (fun c : K.F => K.bilinLin c = y) Finset.univ) = 2 := by
      intros y hy
      obtain ⟨c, hc⟩ : ∃ c : K.F, K.bilinLin c = y := by
        aesop;
      have h_card_image : Finset.filter (fun c : K.F => K.bilinLin c = y) Finset.univ = Finset.image (fun d : K.F => d + c) (Finset.filter (fun d : K.F => K.bilinLin d = 0) Finset.univ) := by
        ext d; simp [hc];
        have h_add : K.bilinLin (d + -c) = K.bilinLin d + K.bilinLin (-c) := by
          unfold KasamiData.bilinLin; simp +decide [ add_comm, add_left_comm, add_assoc ] ;
          rw [ KasamiData.frob_add, KasamiData.frobConj_add ] ; ring;
        grind +splitImp;
      rw [ h_card_image, Finset.card_image_of_injective _ ( add_left_injective c ), h_kernel ];
    have h_card_image : Finset.card (Finset.univ : Finset K.F) = Finset.sum (Finset.image (fun c : K.F => K.bilinLin c) Finset.univ) (fun y => Finset.card (Finset.filter (fun c : K.F => K.bilinLin c = y) Finset.univ)) := by
      grind +suggestions;
    rw [ Finset.sum_congr rfl ‹_› ] at h_card_image ; simp_all +decide [ Finset.card_univ ];
    have := K.card_F; rcases n : K.n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ] ;
    · linarith [ K.hn ];
    · linarith;
  have h_image_subset : Finset.image (fun c : K.F => K.bilinLin c) Finset.univ ⊆ Finset.univ.filter (fun a : K.F => K.Tr a = 0) := by
    exact Finset.image_subset_iff.mpr fun c _ => by simp +decide [ bilinLin_trace ] ;
  have h_image_eq : Finset.image (fun c : K.F => K.bilinLin c) Finset.univ = Finset.univ.filter (fun a : K.F => K.Tr a = 0) := by
    refine' Finset.eq_of_subset_of_card_le h_image_subset _;
    have := K.card_trace_one;
    have h_card_filter : Finset.card (Finset.univ.filter (fun a : K.F => K.Tr a = 0)) + Finset.card (Finset.univ.filter (fun a : K.F => K.Tr a = 1)) = 2 ^ K.n := by
      rw [ ← K.card_F, Finset.card_filter, Finset.card_filter ];
      rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x hx => by rcases K.Tr x with ( _ | _ | n ) <;> trivial, Finset.sum_const, Finset.card_univ ] ; norm_num;
    cases n : K.n <;> simp_all +decide [ pow_succ' ] ; linarith;
  replace h_image_eq := Finset.ext_iff.mp h_image_eq b; aesop;

/-- All squared Walsh values for Tr(a) = 1 are equal. -/
theorem goldWalsh_sq_const (a a' : K.F) (ha : K.Tr a = 1) (ha' : K.Tr a' = 1) :
    K.goldWalsh a ^ 2 = K.goldWalsh a' ^ 2 := by
  have hd : K.Tr (a + a') = 0 := by rw [map_add, ha, ha']; decide
  obtain ⟨c, hc⟩ := K.bilinLin_surj (a + a') hd
  have hsub := K.goldWalsh_subst a' c
  have h2 : (2 : K.F) = 0 := CharP.cast_eq_zero K.F 2
  have hchar : a' + (a + a') = a := by
    have : a' + a' = 0 := by rw [← two_mul]; simp [h2]
    calc a' + (a + a') = a + (a' + a') := by ring
      _ = a + 0 := by rw [this]
      _ = a := by ring
  rw [show a' + K.bilinLin c = a from by rw [hc]; exact hchar] at hsub
  exact hsub.symm

/-
**Spectral Theorem**: W_g(a)² ∈ {0, 2^(n+1)}.

    Case Tr(a)=0: W(a) = 0 by goldWalsh_zero_of_trace_zero.
    Case Tr(a)=1: All W(a)² are equal (goldWalsh_sq_const),
    and Parseval + card_trace_one give the common value 2^(n+1).
-/
theorem goldWalsh_sq_values (a : K.F) :
    K.goldWalsh a ^ 2 = 0 ∨ K.goldWalsh a ^ 2 = (2 : ℤ) ^ (K.n + 1) := by
  by_cases ha : K.Tr a = 0;
  · exact Or.inl ( by rw [ goldWalsh_zero_of_trace_zero K a ha, zero_pow two_ne_zero ] );
  · have h_sum : ∑ a ∈ Finset.univ.filter (fun a : K.F => K.Tr a = 1), K.goldWalsh a ^ 2 = 2 ^ (2 * K.n) := by
      have h_sum : ∑ a, K.goldWalsh a ^ 2 = 2 ^ (2 * K.n) := by
        convert parseval_walsh K K.goldBool using 1;
      rw [ ← h_sum, Finset.sum_filter_of_ne ];
      exact fun x _ hx => Or.resolve_left ( Fin.exists_fin_two.mp ( by aesop ) ) fun hx' => hx <| by simp +decide [ hx', goldWalsh_zero_of_trace_zero K x ] ;
    -- Since all terms in the sum are equal, we can factor out $W(a)^2$.
    have h_factor : ∑ a ∈ Finset.univ.filter (fun a : K.F => K.Tr a = 1), K.goldWalsh a ^ 2 = (2 ^ (K.n - 1)) * K.goldWalsh a ^ 2 := by
      have h_factor : ∀ a' : K.F, K.Tr a' = 1 → K.goldWalsh a' ^ 2 = K.goldWalsh a ^ 2 := by
        exact fun a' ha' => K.goldWalsh_sq_const a' a ha' ( Or.resolve_left ( Fin.exists_fin_two.mp ( by aesop ) ) ha );
      rw [ Finset.sum_congr rfl fun x hx => h_factor x <| Finset.mem_filter.mp hx |>.2 ] ; norm_num [ card_trace_one ];
    rcases n : K.n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ', pow_mul' ];
    · linarith [ K.hn ];
    · exact Or.inr ( by nlinarith [ pow_pos ( zero_lt_two' ℤ ) ‹_› ] )

/-
W_g(a) ≠ 0 ↔ Tr(a) = 1.
-/
theorem goldWalsh_nonzero_iff (a : K.F) :
    K.goldWalsh a ≠ 0 ↔ K.Tr a = 1 := by
  constructor;
  · exact fun h => by have := K.goldWalsh_sq_values a; have := K.goldWalsh_zero_of_trace_zero a; have := K.trace_one; cases Fin.exists_fin_two.mp ⟨ K.Tr a, rfl ⟩ <;> aesop;
  · intro ha
    by_contra h_contra
    have h_all_zero : ∀ a' : K.F, K.Tr a' = 1 → K.goldWalsh a' = 0 := by
      intros a' ha'
      have := goldWalsh_sq_const K a a' ha ha'
      simp_all +decide [ sq ]
    have h_parseval : ∑ a : K.F, K.goldWalsh a ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro a' ha'
      by_cases ha'_trace : K.Tr a' = 1;
      · rw [ h_all_zero a' ha'_trace, zero_pow two_ne_zero ];
      · have := K.goldWalsh_zero_of_trace_zero a' ( by have := Fin.exists_fin_two.mp ⟨ K.Tr a', rfl ⟩ ; aesop ) ; aesop;
    have h_contradiction : (2 : ℤ) ^ (2 * K.n) = 0 := by
      convert h_parseval using 1;
      convert parseval_walsh K K.goldBool |> Eq.symm using 1
    norm_num at h_contradiction

/-
|{a : W_g(a) ≠ 0}| = 2^(n-1).
-/
theorem card_nonzero_walsh :
    Finset.card (Finset.univ.filter fun a : K.F => K.goldWalsh a ≠ 0) =
    2 ^ (K.n - 1) := by
  exact Eq.trans ( congr_arg _ ( by ext; simp +decide [ KasamiData.goldWalsh_nonzero_iff ] ) ) ( KasamiData.card_trace_one K )

end KasamiData
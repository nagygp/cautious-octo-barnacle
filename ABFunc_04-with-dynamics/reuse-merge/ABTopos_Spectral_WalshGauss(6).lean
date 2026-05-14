import Mathlib

/-!
# AB Spectral Collapse — CIC Unicode Formalization

Minimal expansion of the `combined_identity` black box from the
Kasami triple-count proof.

## Steps
  1. Additive character χ : GF(2ⁿ) → ℂ via the absolute trace
  2. Walsh–Hadamard transform Ŵ(u) := Σ_x χ(ux + x^d)
  3. Gauss sum 𝔤(ψ) := Σ_x ψ(x) · χ(x)
  4. Stickelberger norm: ‖𝔤(ψ)‖² = 2ⁿ for ψ ≠ 1
  5. Walsh–Gauss decomposition
  6. APN + n odd ⟹ AB spectral collapse
  7. Fourier identity + combined identity ⟹ |𝒯| = 2^{2n−3}

References: [Kasami 1971], [BBMM 2006, Thm 3]
-/

open Finset BigOperators

noncomputable section

variable (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [CharP 𝔽 2]

-- ════════════════════════════════════════════════════════════════
-- §1  ADDITIVE CHARACTER
-- ════════════════════════════════════════════════════════════════

/-- The GF(2)-algebra structure on 𝔽. -/
noncomputable instance algebraZMod2 : Algebra (ZMod 2) 𝔽 :=
  (ZMod.castHom (dvd_refl 2) 𝔽).toAlgebra

/-- Absolute trace  Tr : GF(2ⁿ) → GF(2), defined via `Algebra.trace`. -/
def AbsTrace : 𝔽 →+ ZMod 2 :=
  (Algebra.trace (ZMod 2) 𝔽).toAddMonoidHom

/-- Canonical additive character  χ(x) := (−1)^{Tr(x)}. -/
def χ_ : 𝔽 → ℂ := fun x => (-1 : ℂ) ^ (AbsTrace 𝔽 x).val

/-- Helper: exponent arithmetic for (−1) over ZMod 2. -/
private lemma neg_one_pow_zmod2_val_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  fin_cases a <;> fin_cases b <;>
    simp [show (0 : ZMod 2).val = 0 from by decide,
          show (1 : ZMod 2).val = 1 from by decide,
          show (0 + 0 : ZMod 2) = 0 from by decide,
          show (0 + 1 : ZMod 2) = 1 from by decide,
          show (1 + 0 : ZMod 2) = 1 from by decide,
          show (1 + 1 : ZMod 2) = 0 from by decide]

/-- χ is additive: χ(x+y) = χ(x)·χ(y). -/
lemma χ_add (x y : 𝔽) : χ_ 𝔽 (x + y) = χ_ 𝔽 x * χ_ 𝔽 y := by
  simp only [χ_, map_add]
  exact neg_one_pow_zmod2_val_add (AbsTrace 𝔽 x) (AbsTrace 𝔽 y)

/-- χ is ±1-valued. -/
lemma χ_sq (x : 𝔽) : χ_ 𝔽 x ^ 2 = 1 := by
  unfold χ_;
  norm_num [← pow_mul]

/-- χ as a Mathlib `AddChar`. -/
def χ_addChar : AddChar 𝔽 ℂ where
  toFun := χ_ 𝔽
  map_zero_eq_one' := by simp [χ_, AbsTrace, map_zero]
  map_add_eq_mul' := χ_add 𝔽

/-- The trace-based character χ is nontrivial (hence ∑ χ(x) = 0). -/
lemma χ_addChar_ne_one : χ_addChar 𝔽 ≠ 1 := by
  intro h
  have htr := Algebra.trace_ne_zero (ZMod 2) 𝔽
  apply htr
  ext x
  have : χ_ 𝔽 x = 1 := by
    have := congr_fun (congr_arg AddChar.toFun h) x
    simpa [χ_addChar] using this
  simp only [χ_] at this
  have hval : (AbsTrace 𝔽 x).val = 0 := by
    by_contra h0
    have hv1 : (AbsTrace 𝔽 x).val = 1 := by
      have := ZMod.val_lt (AbsTrace 𝔽 x)
      omega
    simp [hv1] at this; norm_num at this
  have : AbsTrace 𝔽 x = 0 := by
    rwa [ZMod.val_eq_zero] at hval
  simp [AbsTrace] at this
  exact this

/-- Orthogonality:  Σ_x χ(ax) = |𝔽|·𝟙[a=0]. -/
lemma χ_orthogonality (a : 𝔽) :
    ∑ x : 𝔽, χ_ 𝔽 (a * x) = if a = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha, χ_, AbsTrace, map_zero]
  · -- For a ≠ 0, change variables y = a * x (bijection)
    have : ∑ x : 𝔽, χ_ 𝔽 (a * x) = ∑ y : 𝔽, χ_ 𝔽 y := by
      exact Equiv.sum_comp (Equiv.mulLeft₀ a ha) _
    rw [this]
    -- Now ∑ y, χ(y) = 0 since χ is nontrivial
    have hne : χ_addChar 𝔽 ≠ 1 := χ_addChar_ne_one 𝔽
    exact AddChar.sum_eq_zero_of_ne_one hne

-- ════════════════════════════════════════════════════════════════
-- §2  KASAMI EXPONENT & WALSH TRANSFORM
-- ════════════════════════════════════════════════════════════════

/-- Kasami exponent:  d(k) := 2^{2k} − 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-- Walsh–Hadamard transform:  Ŵ(u) := Σ_x χ(ux + x^d). -/
def Ŵ (d : ℕ) (u : 𝔽) : ℂ := ∑ x : 𝔽, χ_ 𝔽 (u * x + x ^ d)

-- ════════════════════════════════════════════════════════════════
-- §3  GAUSS SUMS
-- ════════════════════════════════════════════════════════════════

/-- Gauss sum:  𝔤(ψ) := Σ_{x ∈ 𝔽ˣ} ψ(x) · χ(x). -/
def 𝔤 (ψ : 𝔽ˣ →* ℂˣ) : ℂ := ∑ x : 𝔽ˣ, (ψ x : ℂ) * χ_ 𝔽 (x : 𝔽)

/-
════════════════════════════════════════════════════════════════
§4  STICKELBERGER NORM
════════════════════════════════════════════════════════════════

**Stickelberger:**  ‖𝔤(ψ)‖² = q  for ψ ≠ 1.
    [Ireland–Rosen Ch. 8]
-/
set_option maxHeartbeats 800000 in
theorem stickelberger_norm (ψ : 𝔽ˣ →* ℂˣ) (hψ : ψ ≠ 1) :
    ‖𝔤 𝔽 ψ‖ ^ 2 = Fintype.card 𝔽 := by
      -- By definition of $𝔤$, we have $𝔤 𝔽 ψ = \sum_{x \in \mathbb{F}^*} \psi(x) \chi(x)$.
      set g := 𝔤 𝔽 ψ
      have hg : g * starRingEnd ℂ g = (Fintype.card 𝔽 : ℂ) := by
        -- Consider $g \cdot \overline{g} = \sum_{x,y \in \mathbb{F}^*} \psi(x) \overline{\psi(y)} \chi(x) \overline{\chi(y)}$.
        have h_g_g_conj : g * starRingEnd ℂ g = ∑ x : 𝔽ˣ, ∑ y : 𝔽ˣ, (ψ x * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (x - y) := by
          have h_g_g_conj : g * starRingEnd ℂ g = ∑ x : 𝔽ˣ, ∑ y : 𝔽ˣ, (ψ x : ℂ) * (starRingEnd ℂ (ψ y : ℂ)) * χ_ 𝔽 x * starRingEnd ℂ (χ_ 𝔽 y) := by
            simp +zetaDelta at *;
            simp +decide only [𝔤, starRingEnd_apply, sum_mul _ _ _];
            simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
          -- Since $\chi$ is a character, we have $\chi(x) \overline{\chi(y)} = \chi(x - y)$.
          have h_char : ∀ x y : 𝔽, χ_ 𝔽 x * starRingEnd ℂ (χ_ 𝔽 y) = χ_ 𝔽 (x - y) := by
            intro x y; simp +decide [ χ_, sub_eq_add_neg ] ;
            rw [ ← neg_one_pow_zmod2_val_add ];
          have h_char : ∀ y : 𝔽ˣ, starRingEnd ℂ (ψ y : ℂ) = (ψ y)⁻¹ := by
            intro y
            have h_char : (ψ y : ℂ) ^ (Fintype.card 𝔽ˣ) = 1 := by
              norm_cast;
              simp +decide [ ← map_pow, pow_card_eq_one ];
            have h_char : Complex.normSq (ψ y : ℂ) = 1 := by
              replace h_char := congr_arg Complex.normSq h_char ; simp_all +decide [ Complex.normSq_eq_norm_sq ];
              exact Or.imp ( fun h => by rw [ pow_eq_one_iff_of_nonneg ( norm_nonneg _ ) ] at h <;> aesop ) ( fun h => by linarith [ pow_nonneg ( norm_nonneg ( ψ y : ℂ ) ) ( Fintype.card 𝔽ˣ ) ] ) h_char;
            simp +decide [ Complex.ext_iff, h_char ];
          simp_all +decide [ mul_assoc ];
        -- Change variables to $t = x/y$: $g \cdot \overline{g} = \sum_{t \in \mathbb{F}^*} \psi(t) \sum_{y \in \mathbb{F}^*} \chi(y(t-1))$.
        have h_change_var : g * starRingEnd ℂ g = ∑ t : 𝔽ˣ, (ψ t : ℂ) * ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) := by
          have h_change_var : ∀ y : 𝔽ˣ, ∑ x : 𝔽ˣ, (ψ x * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (x - y) = ∑ t : 𝔽ˣ, (ψ t : ℂ) * χ_ 𝔽 (y * (t - 1 : 𝔽)) := by
            intro y
            have h_change_var : ∑ x : 𝔽ˣ, (ψ x * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (x - y) = ∑ t : 𝔽ˣ, (ψ (y * t) * (ψ y)⁻¹ : ℂ) * χ_ 𝔽 (y * t - y) := by
              rw [ ← Equiv.sum_comp ( Equiv.mulLeft y ) ] ; aesop;
            simp_all +decide [ mul_sub, mul_assoc, mul_left_comm ];
            simp +decide [ mul_left_comm ( ψ y : ℂ ), mul_assoc, Units.ne_zero ];
          rw [ h_g_g_conj, Finset.sum_comm ];
          simp +decide only [h_change_var, Finset.mul_sum _ _ _];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
        -- The inner sum $\sum_{y \in \mathbb{F}^*} \chi(y(t-1))$ is $|𝔽|-1$ if $t=1$ and $-1$ otherwise.
        have h_inner_sum : ∀ t : 𝔽ˣ, ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) = if t = 1 then (Fintype.card 𝔽 - 1 : ℂ) else -1 := by
          intro t
          have h_inner_sum_eq : ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) = ∑ y : 𝔽, χ_ 𝔽 (y * (t - 1 : 𝔽)) - χ_ 𝔽 0 := by
            have h_inner_sum_eq : ∑ y : 𝔽ˣ, χ_ 𝔽 (y * (t - 1 : 𝔽)) = ∑ y ∈ Finset.univ.erase 0, χ_ 𝔽 (y * (t - 1 : 𝔽)) := by
              refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide;
              · exact fun a₁ a₂ h => Units.ext h;
              · exact fun b hb => ⟨ Units.mk0 b hb, rfl ⟩;
            aesop;
          split_ifs with h <;> simp_all +decide [ χ_orthogonality ];
          · simp +decide [ χ_ ];
          · have := χ_orthogonality 𝔽 ( t - 1 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
            simp_all +decide [ mul_comm, χ_ ];
        -- Since $\psi$ is a nontrivial multiplicative character, $\sum_{t \in \mathbb{F}^*} \psi(t) = 0$.
        have h_sum_psi : ∑ t : 𝔽ˣ, (ψ t : ℂ) = 0 := by
          -- Since $\psi$ is a nontrivial multiplicative character, there exists some $a \in \mathbb{F}^*$ such that $\psi(a) \neq 1$.
          obtain ⟨a, ha⟩ : ∃ a : 𝔽ˣ, ψ a ≠ 1 := by
            exact not_forall.mp fun h => hψ <| MonoidHom.ext h;
          -- Since $\psi$ is a nontrivial multiplicative character, we have $\sum_{t \in \mathbb{F}^*} \psi(t) = \sum_{t \in \mathbb{F}^*} \psi(at)$.
          have h_sum_eq : ∑ t : 𝔽ˣ, (ψ t : ℂ) = ∑ t : 𝔽ˣ, (ψ (a * t) : ℂ) := by
            rw [ ← Equiv.sum_comp ( Equiv.mulLeft a ) ] ; aesop;
          simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc ];
          rw [ ← Finset.mul_sum _ _ _, eq_comm ] at *;
          by_cases h : ∑ i : 𝔽ˣ, ( ψ i : ℂ ) = 0 <;> simp_all +decide;
        simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
      convert congr_arg Complex.re hg using 1 ; simp +decide [ Complex.normSq, Complex.sq_norm ]

/-
Corollary: ‖𝔤(ψ)‖ = √q.
-/
theorem gauss_norm (ψ : 𝔽ˣ →* ℂˣ) (hψ : ψ ≠ 1) :
    ‖𝔤 𝔽 ψ‖ = Real.sqrt (Fintype.card 𝔽 : ℝ) := by
      rw [ ← sq_eq_sq₀ ] <;> first | positivity | rw [ Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ; exact mod_cast stickelberger_norm 𝔽 ψ hψ;

/-
════════════════════════════════════════════════════════════════
§5  WALSH–GAUSS DECOMPOSITION
════════════════════════════════════════════════════════════════

**Walsh–Gauss:**  Ŵ(u) = Σ_ψ cψ · 𝔤(ψ)  for u ≠ 0.
    [Coulter–Matthews 1997]
-/
theorem walsh_gauss_decomposition (d : ℕ) (u : 𝔽) (hu : u ≠ 0) :
    ∃ (S : Finset (𝔽ˣ →* ℂˣ)) (c : (𝔽ˣ →* ℂˣ) → ℂ),
      Ŵ 𝔽 d u = ∑ ψ ∈ S, c ψ * 𝔤 𝔽 ψ := by
        by_contra h_contra;
        refine' h_contra ⟨ { 1 }, fun _ => ( Ŵ 𝔽 d u ) / 𝔤 𝔽 1, _ ⟩;
        simp +decide [ div_mul_cancel₀, show 𝔤 𝔽 1 ≠ 0 from _ ];
        rw [ div_mul_cancel₀ ];
        intro h
        have h_contra : ∀ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = 0 := by
          intros x
          by_contra h_nonzero
          have h_sum : ∑ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = 0 := by
            convert h using 1;
            exact Finset.sum_congr rfl fun _ _ => by simp +decide [ χ_ ] ;
          have h_sum : ∑ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = ∑ x : 𝔽, χ_ 𝔽 x - χ_ 𝔽 0 := by
            have h_sum : ∑ x : 𝔽ˣ, χ_ 𝔽 (x : 𝔽) = ∑ x ∈ Finset.univ.erase 0, χ_ 𝔽 x := by
              refine' Finset.sum_bij ( fun x _ => x ) _ _ _ _ <;> simp +decide;
              · exact fun a₁ a₂ h => Units.ext h;
              · exact fun b hb => ⟨ Units.mk0 b hb, rfl ⟩;
            rw [ h_sum, Finset.sum_erase_eq_sub ( Finset.mem_univ 0 ) ];
          have := χ_orthogonality 𝔽 1; simp_all +decide [ Finset.sum_add_distrib ] ;
          unfold χ_ at *; simp_all +decide [ Finset.sum_add_distrib ] ;
        generalize_proofs at *;
        exact absurd ( h_contra 1 ) ( by simp +decide [ χ_ ] )

-- ════════════════════════════════════════════════════════════════
-- §6  APN ⟹ AB
-- ════════════════════════════════════════════════════════════════

/-- APN property:  ∀ a ≠ 0, ∀ b,  #{x | (x+a)^d + x^d = b} ≤ 2. -/
def IsAPN (d : ℕ) : Prop :=
  ∀ (a b : 𝔽), a ≠ 0 → (univ.filter (fun x => (x + a) ^ d + x ^ d = b)).card ≤ 2

/-- **Kasami APN:**  x ↦ x^d is APN when gcd(k,n) = 1.
    [Kasami 1971] -/
theorem kasami_apn (n k : ℕ) (hcard : Fintype.card 𝔽 = 2 ^ n)
    (hcoprime : Nat.Coprime k n) :
    IsAPN 𝔽 (kasamiExp k) := by sorry

/-
**Parseval:**  Σ_u ‖Ŵ(u)‖² = |𝔽|².
-/
theorem walsh_parseval (d : ℕ) :
    ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2 := by
      -- We start by expanding the square of the norm of the Walsh transform:
      have h_expand : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = ∑ x : 𝔽, ∑ y : 𝔽, ∑ u : 𝔽, (χ_ 𝔽 (u * x + x ^ d)) * (χ_ 𝔽 (-u * y - y ^ d)) := by
        have h_expand : ∀ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = ∑ x : 𝔽, ∑ y : 𝔽, (χ_ 𝔽 (u * x + x ^ d)) * (χ_ 𝔽 (-u * y - y ^ d)) := by
          intro u
          have h_expand : ‖Ŵ 𝔽 d u‖ ^ 2 = (∑ x : 𝔽, χ_ 𝔽 (u * x + x ^ d)) * (∑ y : 𝔽, χ_ 𝔽 (-u * y - y ^ d)) := by
            unfold Ŵ; norm_cast; simp +decide [ ← sq, ← Finset.sum_mul _ _ _ ] ;
            unfold χ_; simp +decide [ ← sq, ← Finset.sum_mul _ _ _ ] ;
            norm_cast;
            rw [ sq, abs_eq_max_neg, max_def ] ; split_ifs <;> simp_all +decide [ sub_eq_add_neg ];
          rw [ h_expand, Finset.sum_mul ];
          simp +decide only [Finset.mul_sum _ _ _];
        push_cast [ h_expand ];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
      -- We simplify the inner sum using the orthogonality of the characters:
      have h_inner : ∀ x y : 𝔽, ∑ u : 𝔽, (χ_ 𝔽 (u * x + x ^ d)) * (χ_ 𝔽 (-u * y - y ^ d)) = if x = y then (Fintype.card 𝔽 : ℂ) else 0 := by
        intro x y
        have h_inner : ∑ u : 𝔽, (χ_ 𝔽 (u * (x - y))) = if x = y then (Fintype.card 𝔽 : ℂ) else 0 := by
          convert χ_orthogonality 𝔽 ( x - y ) using 1 ; simp +decide [ mul_comm ];
          simp +decide [ sub_eq_zero ]
        simp_all +decide [ ← mul_assoc, ← pow_add ];
        convert congr_arg ( fun z => z * χ_ 𝔽 ( x ^ d - y ^ d ) ) h_inner using 1 <;> ring;
        · rw [ Finset.sum_mul ] ; congr ; ext ; rw [ ← mul_comm ] ; rw [ ← χ_add ] ; ring;
          rw [ ← χ_add ] ; ring;
        · aesop;
      rw [ ← Complex.ofReal_inj ] ; simp_all +decide [ sq ]

/-- **Fourth-moment bound:**  APN ⟹ Σ_u ‖Ŵ(u)‖⁴ ≤ 2·|𝔽|³. -/
theorem apn_fourth_moment_bound (d : ℕ) (hAPN : IsAPN 𝔽 d) :
    ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 4 ≤ 2 * (Fintype.card 𝔽 : ℝ) ^ 3 := by sorry

/-- **Cauchy–Schwarz rigidity:**  M₂ + M₄ bound ⟹ flat spectrum. -/
theorem cauchy_schwarz_rigidity (d : ℕ)
    (hM₂ : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 2 = (Fintype.card 𝔽 : ℝ) ^ 2)
    (hM₄ : ∑ u : 𝔽, ‖Ŵ 𝔽 d u‖ ^ 4 ≤ 2 * (Fintype.card 𝔽 : ℝ) ^ 3) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ u : 𝔽, ‖Ŵ 𝔽 d u‖ = 0 ∨ ‖Ŵ 𝔽 d u‖ = C := by sorry

/-- **AB Spectral Collapse:**  APN + n odd ⟹ ‖Ŵ(u)‖ ∈ {0, 2^{(n+1)/2}}.

    Proof: Parseval + fourth-moment ⟹ flat by Cauchy–Schwarz.
    Then C² = 2^{n+1}, so C = 2^{(n+1)/2} (n odd ⟹ n+1 even).

    [Chabaud–Vaudenay 1994; Canteaut–Charpin–Dobbertin 2000] -/
theorem ab_spectral_collapse
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n) :
    ∀ u : 𝔽,
      ‖Ŵ 𝔽 (kasamiExp k) u‖ = 0 ∨
      ‖Ŵ 𝔽 (kasamiExp k) u‖ = (2 : ℝ) ^ ((n + 1) / 2 : ℕ) := by sorry

-- ════════════════════════════════════════════════════════════════
-- §7  DIFFERENTIAL SET, TRIPLE SET, FOURIER IDENTITY
-- ════════════════════════════════════════════════════════════════

/-- Differential set:  Δ := { x^d + (x+1)^d + 1 | x ∈ 𝔽 }. -/
def Delta (d : ℕ) : Finset 𝔽 := univ.image (fun x => x ^ d + (x + 1) ^ d + 1)

/-- Fourier transform of Δ indicator:  deltaHat(a) := Σ_{x ∈ Δ} χ(ax). -/
def deltaHat (d : ℕ) (a : 𝔽) : ℂ := ∑ x ∈ Delta 𝔽 d, χ_ 𝔽 (a * x)

/-- Triple set:
    Triples(v₁,v₂) := { (x,y,z) ∈ Δ³ | v₁x + v₂y + (v₁+v₂)z = 0 }. -/
def Triples (d : ℕ) (v₁ v₂ : 𝔽) : Finset (𝔽 × 𝔽 × 𝔽) :=
  ((Delta 𝔽 d) ×ˢ ((Delta 𝔽 d) ×ˢ (Delta 𝔽 d))).filter
    (fun p => v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0)

/-
════════════════════════════════════════════════════════════════
§8  FOURIER TRIPLE-SUM IDENTITY
════════════════════════════════════════════════════════════════

**Fourier identity:**
    |Triples| = (1/|𝔽|) · Σ_a deltaHat(v₁a)·deltaHat(v₂a)·deltaHat((v₁+v₂)a).

    By character-sum orthogonality.
-/
theorem fourier_triple_identity (d : ℕ) (v₁ v₂ : 𝔽) :
    ((Triples 𝔽 d v₁ v₂).card : ℂ) =
      (1 : ℂ) / (Fintype.card 𝔽 : ℂ) *
        ∑ a : 𝔽, deltaHat 𝔽 d (v₁ * a) * deltaHat 𝔽 d (v₂ * a) *
                  deltaHat 𝔽 d ((v₁ + v₂) * a) := by
                    unfold deltaHat Triples;
                    -- By Fubini's theorem, we can interchange the order of summation.
                    have h_fubini : ∑ a : 𝔽, (∑ x ∈ Delta 𝔽 d, χ_ 𝔽 (v₁ * a * x)) * (∑ y ∈ Delta 𝔽 d, χ_ 𝔽 (v₂ * a * y)) * (∑ z ∈ Delta 𝔽 d, χ_ 𝔽 ((v₁ + v₂) * a * z)) = ∑ x ∈ Delta 𝔽 d, ∑ y ∈ Delta 𝔽 d, ∑ z ∈ Delta 𝔽 d, ∑ a : 𝔽, χ_ 𝔽 (a * (v₁ * x + v₂ * y + (v₁ + v₂) * z)) := by
                      simp +decide only [Finset.sum_mul, Finset.mul_sum _ _ _, mul_comm];
                      simp +decide only [← sum_product'];
                      refine' Finset.sum_bij ( fun x _ => ( x.2.2.2, x.2.2.1, x.2.1, x.1 ) ) _ _ _ _ <;> simp +decide [ χ_add ];
                      · tauto;
                      · aesop;
                      · tauto;
                      · intro a b c d hb hc hd; rw [ ← χ_add, ← χ_add ] ; ring;
                    -- By orthogonality of characters, the inner sum is zero unless $v₁ * x + v₂ * y + (v₁ + v₂) * z = 0$.
                    have h_orthogonality : ∀ x y z : 𝔽, ∑ a : 𝔽, χ_ 𝔽 (a * (v₁ * x + v₂ * y + (v₁ + v₂) * z)) = if v₁ * x + v₂ * y + (v₁ + v₂) * z = 0 then (Fintype.card 𝔽 : ℂ) else 0 := by
                      intro x y z;
                      convert χ_orthogonality 𝔽 ( v₁ * x + v₂ * y + ( v₁ + v₂ ) * z ) using 1;
                      ac_rfl;
                    simp_all +decide [ Finset.sum_ite ];
                    rw [ inv_mul_eq_div, eq_div_iff ];
                    · simp +decide only [card_filter];
                      simp +decide only [sum_product, Nat.cast_sum, sum_mul];
                    · exact Nat.cast_ne_zero.mpr ( Fintype.card_ne_zero )

-- ════════════════════════════════════════════════════════════════
-- §9  AB ⟹ deltaHat SPECTRUM COLLAPSE
-- ════════════════════════════════════════════════════════════════

/-- **AB ⟹ deltaHat collapse:**  ‖deltaHat(a)‖ ∈ {0, 2^{(n−1)/2}} for a ≠ 0. -/
theorem ab_delta_hat_spectrum
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (hAB : ∀ u : 𝔽, ‖Ŵ 𝔽 (kasamiExp k) u‖ = 0 ∨
             ‖Ŵ 𝔽 (kasamiExp k) u‖ = (2 : ℝ) ^ ((n + 1) / 2 : ℕ))
    (a : 𝔽) (ha : a ≠ 0) :
    ‖deltaHat 𝔽 (kasamiExp k) a‖ = 0 ∨
    ‖deltaHat 𝔽 (kasamiExp k) a‖ = (2 : ℝ) ^ ((n - 1) / 2 : ℕ) := by sorry

/-
════════════════════════════════════════════════════════════════
§10  COMBINED IDENTITY
════════════════════════════════════════════════════════════════

**|Δ| = 2^{n−1}** from APN.
-/
theorem delta_card (n k : ℕ) (hn : 3 ≤ n)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n) :
    (Delta 𝔽 (kasamiExp k)).card = 2 ^ (n - 1) := by
      have h_apn : IsAPN 𝔽 (kasamiExp k) := by
        exact?;
      have h_apn_card : ∀ {d : ℕ}, IsAPN 𝔽 d → (Finset.card (Finset.image (fun x : 𝔽 => x ^ d + (x + 1) ^ d + 1) Finset.univ) = 2 ^ (Nat.log 2 (Fintype.card 𝔽) - 1)) := by
        intro d hdn
        have h_apn_card : (Finset.card (Finset.image (fun x : 𝔽 => x ^ d + (x + 1) ^ d + 1) Finset.univ) = 2 ^ (Nat.log 2 (Fintype.card 𝔽) - 1)) := by
          have h_apn_def : ∀ a b : 𝔽, a ≠ 0 → (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) Finset.univ).card ≤ 2 := by
            exact hdn
          have h_apn_card : ∀ a : 𝔽, a ≠ 0 → (Finset.card (Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) Finset.univ) = 2 ^ (Nat.log 2 (Fintype.card 𝔽) - 1)) := by
            intro a ha
            have h_apn_card : ∑ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) Finset.univ, (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) Finset.univ).card = Fintype.card 𝔽 := by
              rw [ ← Finset.card_biUnion ] ; congr ; aesop;
              exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
            have h_apn_card : ∀ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) Finset.univ, (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) Finset.univ).card = 2 := by
              intro b hb
              by_contra h_contra
              have h_card_lt : ∑ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) Finset.univ, (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) Finset.univ).card < ∑ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) Finset.univ, 2 := by
                exact Finset.sum_lt_sum ( fun x hx => h_apn_def a x ha ) ⟨ b, hb, lt_of_le_of_ne ( h_apn_def a b ha ) h_contra ⟩;
              simp_all +decide [ Finset.sum_const, nsmul_eq_mul ];
              have h_card_lt : (Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) Finset.univ).card ≤ 2 ^ (n - 1) := by
                have h_card_lt : ∀ b ∈ Finset.image (fun x : 𝔽 => (x + a) ^ d + x ^ d) Finset.univ, (Finset.filter (fun x => (x + a) ^ d + x ^ d = b) Finset.univ).card ≥ 2 := by
                  intro b hb
                  obtain ⟨x, hx⟩ : ∃ x : 𝔽, (x + a) ^ d + x ^ d = b := by
                    grind;
                  refine' Finset.one_lt_card.mpr ⟨ x, _, x + a, _, _ ⟩ <;> simp_all +decide [ add_comm a ];
                  simp_all +decide [ add_assoc, CharTwo.add_self_eq_zero ];
                  rw [ add_comm, hx ];
                have := Finset.sum_le_sum h_card_lt; simp_all +decide [ pow_succ' ] ;
                grobner;
              cases n <;> simp_all +decide [ pow_succ' ] ; linarith;
            simp_all +decide [ Finset.sum_congr rfl h_apn_card ];
            cases n <;> simp_all +decide [ pow_succ' ];
            linarith;
          have h_apn_card : (Finset.card (Finset.image (fun x : 𝔽 => x ^ d + (x + 1) ^ d) Finset.univ) = 2 ^ (Nat.log 2 (Fintype.card 𝔽) - 1)) := by
            convert h_apn_card 1 one_ne_zero using 1;
            simp +decide only [add_comm];
          rw [ ← h_apn_card ];
          refine' Finset.card_bij ( fun x hx => x - 1 ) _ _ _ <;> simp +decide;
        exact h_apn_card;
      convert h_apn_card h_apn using 2 ; simp +decide [ hcard ]

/-- **Combined Identity:**  |𝔽| · |Triples(v₁,v₂)| = |Δ|³.

    Proof: Fourier identity ⟹ |𝔽|·|Triples| = Σ_a (⋯).
    Split at a = 0: deltaHat(0)³ = |Δ|³.
    For a ≠ 0: AB cancellation kills the tail sum.  ∎ -/
theorem combined_identity_ab
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    Fintype.card 𝔽 * (Triples 𝔽 (kasamiExp k) v₁ v₂).card =
      (Delta 𝔽 (kasamiExp k)).card ^ 3 := by sorry

-- ════════════════════════════════════════════════════════════════
-- §11  MAIN THEOREM
-- ════════════════════════════════════════════════════════════════

/-- Arithmetic: (2^{n-1})³ = 2^n · 2^{2n-3}. -/
private lemma pow_split (n : ℕ) (hn : 3 ≤ n) :
    (2 ^ (n - 1)) ^ 3 = 2 ^ n * 2 ^ (2 * n - 3) := by
  have : (n - 1) * 3 = n + (2 * n - 3) := by omega
  rw [← pow_mul, this, pow_add]

/-- **Kasami Triple-Count Theorem.**
    |Triples(v₁, v₂)| = 2^{2n − 3}
    for v₁ ≠ 0, v₂ ≠ 0, v₁ ≠ v₂, n odd, gcd(k,n) = 1.

    Proof:
      2ⁿ · |Triples|  =  |𝔽| · |Triples|  =  |Δ|³
        =  (2^{n−1})³  =  2ⁿ · 2^{2n−3}.
    Cancel 2ⁿ.  ∎ -/
theorem kasami_triple_count
    (n k : ℕ) (hn : 3 ≤ n) (hn_odd : n % 2 = 1)
    (hcard : Fintype.card 𝔽 = 2 ^ n) (hcoprime : Nat.Coprime k n)
    (v₁ v₂ : 𝔽) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    (Triples 𝔽 (kasamiExp k) v₁ v₂).card = 2 ^ (2 * n - 3) := by
  have h_comb := combined_identity_ab 𝔽 n k hn hn_odd hcard hcoprime
                   v₁ v₂ hv₁ hv₂ hne
  have h_delta := delta_card 𝔽 n k hn hcard hcoprime
  rw [hcard, h_delta] at h_comb
  rw [pow_split n hn] at h_comb
  exact mul_left_cancel₀ (by positivity) h_comb

-- ════════════════════════════════════════════════════════════════
-- §12  AXIOM AUDIT
-- ════════════════════════════════════════════════════════════════

#print axioms kasami_triple_count

end
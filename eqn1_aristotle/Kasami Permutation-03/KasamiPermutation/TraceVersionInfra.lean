import Mathlib
import RequestProject.KasamiPermutation.InverseCubicEquation
import RequestProject.KasamiPermutation.TraceFreeCriterion
import RequestProject.KasamiPermutation.MCM.ToAPN

/-!
# Theorem 8 (Dobbertin 1999) — trace description of the difference set `B`

Over `L = 𝔽_{2ⁿ}`, let `d = 2^{2k} − 2^k + 1` be the Kasami exponent and let

  `D(t) = (t+1)^d + t^d + 1`

be the (two-to-one) Kasami derivative.  Its image `B = {D(t) : t ∈ L}` is the
"Kasami difference set".  **Theorem 8** characterises membership in `B` by a trace
condition on the explicit inverse polynomial `R` built in `InverseCubicEquation`:

  `x ∈ B ⇔ Tr(R(x)) = 0`,

where `Tr(x) = ∑_{i<n} x^{2^i}` is the absolute trace.

This file formalises the case `c = 0`, i.e. `k'` **odd**, which Dobbertin says
"follows immediately from the proof of Corollary 2".  The engine is the *routine
computation* of that proof:

  `D(t) · q(t^{2^k} + t) = 1`   (for `t ∉ 𝔽₂`),

where `q` is the trace-free generalized Kasami permutation (`qPoly`, whose inverse
is `R` by Theorem 6).  Combined with the additive Hilbert-90 fact that
`t ↦ t^{2^k} + t` has image exactly `ker Tr`, this yields Theorem 8.
-/

namespace KasamiPerm.TraceCore

open scoped BigOperators
open KasamiPerm.InverseRec KasamiPerm.InverseCubic

/-- The Kasami exponent `d = 2^{2k} − 2^k + 1`. -/
abbrev kExp (k : ℕ) : ℕ := KasamiPerm.MCMtoAPN.kasamiExp k

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-- The Kasami derivative `D(t) = (t+1)^d + t^d + 1`. -/
noncomputable def Dder (k : ℕ) (t : F) : F :=
  (t + 1) ^ (kExp k) + t ^ (kExp k) + 1

/-- The Kasami difference set `B = image of D`. -/
def Bset (k : ℕ) : Set F := Set.range (Dder (F := F) k)

/-! ## Elementary field facts -/

/-- In `𝔽_{2ⁿ}`, every element satisfies `x^{2ⁿ} = x`. -/
theorem pow_card_eq {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    x ^ (2 ^ n) = x := by
  rw [← hn, FiniteField.pow_card]

/-- `qPoly` at `0` is `0` (the `0/0 = 0` convention). -/
theorem qPoly_zero (k kk : ℕ) : qPoly k kk (0 : F) = 0 := by
  unfold qPoly; simp

/-- With `kk` odd, the constant `ε = (kk+1)` vanishes in characteristic two. -/
theorem eps_zero {kk : ℕ} (hkk : Odd kk) : ((kk + 1 : ℕ) : F) = 0 := by
  obtain ⟨m, rfl⟩ := hkk
  push_cast; ring_nf
  rw [show (2 : F) = 0 from CharTwo.two_eq_zero]; ring

/-
`R` at `0` is `0`.
-/
theorem Rpoly_zero {k kk : ℕ} (hk : 0 < k) (hkk : 1 ≤ kk) :
    Rpoly k kk (0 : F) = 0 := by
  unfold Rpoly;
  rw [ Finset.sum_eq_zero ] ; simp_all +decide [ Aseq, Bseq ];
  · induction' kk using Nat.strong_induction_on with kk ih;
    rcases hkk with ( _ | _ | kk ) <;> simp_all +decide [ twoStep ];
    unfold vc; simp +decide [ hk.ne' ] ;
    exact ne_of_gt ( Nat.sub_pos_of_lt ( one_lt_pow₀ one_lt_two hk.ne' ) );
  · intro i hi; induction' i using Nat.strong_induction_on with i ih; rcases i with ( _ | _ | i ) <;> simp_all +decide [ Aseq ] ;
    simp_all +decide [ twoStep, Zc, vc ];
    exact Or.inl ( Nat.sub_ne_zero_of_lt ( pow_lt_pow_right₀ ( by decide ) ( by nlinarith ) ) )

/-- `D(0) = 0` and `D(1) = 0`: the two `𝔽₂`-points collapse. -/
theorem kExp_pos (k : ℕ) : 0 < kExp k := by
  have h : 2 ^ k ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold kExp KasamiPerm.MCMtoAPN.kasamiExp KasamiAPN.kasamiExp; omega

theorem Dder_zero (k : ℕ) : Dder (F := F) k 0 = 0 := by
  unfold Dder
  rw [zero_add, one_pow, zero_pow (kExp_pos k).ne']
  simp [CharTwo.add_self_eq_zero]

theorem Dder_one (k : ℕ) : Dder (F := F) k 1 = 0 := by
  unfold Dder
  rw [show (1 : F) + 1 = 0 from CharTwo.add_self_eq_zero 1,
    zero_pow (kExp_pos k).ne', one_pow]
  simp [CharTwo.add_self_eq_zero]

/-! ## Trace lemmas -/

/-
Frobenius invariance of the full trace: `Tr(x^{2^k}) = Tr(x)`.
-/
theorem trace_frob_shift {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ) (x : F) :
    FiniteFieldCharTwo.truncTrace n (x ^ (2 ^ k)) = FiniteFieldCharTwo.truncTrace n x := by
  -- By definition of exponentiation in a finite field, we can rewrite the right-hand side.
  have h_exp : ∑ i ∈ Finset.range n, (x ^ (2 ^ k)) ^ (2 ^ i) = ∑ i ∈ Finset.range n, x ^ (2 ^ i) := by
    -- Since $x^{2^n} = x$, we can rewrite the sum as $\sum_{i=k}^{n+k-1} x^{2^i}$.
    have h_sum_shift : ∑ i ∈ Finset.range n, x ^ (2 ^ (i + k)) = ∑ i ∈ Finset.range n, x ^ (2 ^ ((i + k) % n)) := by
      refine' Finset.sum_congr rfl fun i hi => _;
      rw [ ← Nat.mod_add_div ( i + k ) n ] ; simp_all +decide [ pow_add, pow_mul ] ;
      induction' ( i + k ) / n with m ih <;> simp_all +decide [ pow_succ, pow_mul ];
      rw [ ← pow_mul, mul_comm, pow_mul, ← hn, FiniteField.pow_card ];
    -- Since $(i + k) \mod n$ is a permutation of $\{0, 1, ..., n-1\}$, the sums are equal.
    have h_perm : Finset.image (fun i => (i + k) % n) (Finset.range n) = Finset.range n := by
      refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr <| Nat.mod_lt _ <| Nat.pos_of_ne_zero <| by rintro rfl; simp_all +decide [ pow_succ' ] ) _;
      rw [ Finset.card_image_of_injOn ];
      intros i hi j hj hij; have := Nat.modEq_iff_dvd.mp hij.symm; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      obtain ⟨ a, ha ⟩ := this; nlinarith [ show a = 0 by nlinarith ] ;
    have h_perm_sum : ∑ i ∈ Finset.range n, x ^ (2 ^ ((i + k) % n)) = ∑ i ∈ Finset.range n, x ^ (2 ^ i) := by
      conv_rhs => rw [ ← h_perm, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
    convert h_sum_shift.trans h_perm_sum using 2 ; ring;
  exact h_exp

/-
`Tr(t^{2^k} + t) = 0` for all `t`.
-/
theorem trace_artin_schreier_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (t : F) : FiniteFieldCharTwo.truncTrace n (t ^ (2 ^ k) + t) = 0 := by
  rw [ FiniteFieldCharTwo.truncTrace_add ];
  rw [ trace_frob_shift hn k t, ← two_mul, CharTwo.two_eq_zero, MulZeroClass.zero_mul ]

/-
The trace is not the zero map: some element has nonzero trace.  (The trace is a
nonzero polynomial `∑_{i<n} X^{2^i}` of degree `2^{n-1} < 2^n = |F|`, so it cannot
vanish on all of `F`.)
-/
theorem exists_trace_ne_zero {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 0 < n) :
    ∃ x : F, FiniteFieldCharTwo.truncTrace n x ≠ 0 := by
  exact FiniteFieldCharTwo.frobSum_ne_zero 2 hn hn_pos

/-- The map `t ↦ t^{2^k} + t` as an additive group homomorphism of `F`. -/
def asHom (k : ℕ) : F →+ F where
  toFun t := t ^ (2 ^ k) + t
  map_zero' := by
    show (0 : F) ^ (2 ^ k) + 0 = 0
    rw [add_zero, zero_pow (pow_ne_zero k two_ne_zero)]
  map_add' a b := by
    show (a + b) ^ (2 ^ k) + (a + b) = (a ^ (2 ^ k) + a) + (b ^ (2 ^ k) + b)
    rw [add_pow_char_pow]
    ring

/-- The trace `Tr = ∑_{i<n} x^{2^i}` as an additive group homomorphism of `F`. -/
def traceHom (n : ℕ) : F →+ F where
  toFun := FiniteFieldCharTwo.truncTrace n
  map_zero' := FiniteFieldCharTwo.truncTrace_zero n
  map_add' := FiniteFieldCharTwo.truncTrace_add n

/-
**Additive Hilbert 90.**  With `gcd(k,n) = 1`, the image of `t ↦ t^{2^k} + t`
is exactly the kernel of the trace: every trace-zero element is `t^{2^k} + t`.
-/
set_option maxHeartbeats 1600000 in
theorem artin_schreier_surj {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k : ℕ}
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n)
    {y : F} (hy : FiniteFieldCharTwo.truncTrace n y = 0) :
    ∃ t : F, t ^ (2 ^ k) + t = y := by
  have h_card_ker : Nat.card (AddMonoidHom.ker (asHom (F := F) k)) = 2 := by
    have h_ker_card : (asHom (F := F) k).ker = AddSubgroup.zmultiples (1 : F) := by
      ext t; simp [asHom];
      constructor <;> intro h <;> simp_all +decide [ AddSubgroup.mem_zmultiples_iff ];
      · have h_frob : t ^ 2 = t := by
          have h_frob : t ^ (2 ^ k) = t := by
            grind +suggestions;
          have h_frob : ∀ m : ℕ, t ^ (2 ^ (m * k)) = t := by
            intro m; induction m <;> simp_all +decide [ pow_succ', pow_mul' ] ;
          have h_frob : ∃ m : ℕ, m * k ≡ Nat.gcd k n [MOD n] := by
            have := Nat.gcd_eq_gcd_ab k n;
            use Int.toNat ( Nat.gcdA k n % n );
            simp +decide [ ← Int.natCast_modEq_iff, ← this, mul_comm ];
            simp +decide [ Int.ModEq, Int.mul_emod, this ];
            simp +decide [ Int.emod_nonneg _ ( by linarith : ( n : ℤ ) ≠ 0 ) ];
          obtain ⟨ m, hm ⟩ := h_frob;
          have h_frob : t ^ (2 ^ (m * k)) = t ^ (2 ^ (Nat.gcd k n)) := by
            rw [ ← Nat.mod_add_div ( m * k ) n, hm ];
            simp +decide [ pow_add, pow_mul, FiniteField.pow_card ];
            rw [ Nat.mod_eq_of_lt ( Nat.lt_of_le_of_lt ( Nat.le_of_dvd hk ( Nat.gcd_dvd_left _ _ ) ) hkn ) ];
            induction' m * k / n with m ih <;> simp_all +decide [ pow_succ, pow_mul ];
            rw [ ← hn, FiniteField.pow_card ];
          grind;
        by_cases ht : t = 0 <;> simp_all +decide [ sq ];
        · exact ⟨ 0, by simp +decide ⟩;
        · exact ⟨ 1, by simp +decide ⟩;
      · rcases h with ⟨ k, rfl ⟩ ; norm_cast ; simp +decide [ Nat.pow_mod, CharTwo.two_eq_zero ] ;
        rcases Int.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> norm_num [ zpow_add₀, zpow_mul ];
        · simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ];
        · norm_cast ; simp +decide [ CharTwo.two_eq_zero ];
          exact CharTwo.add_self_eq_zero 1;
    rw [ h_ker_card, Nat.card_eq_fintype_card, Fintype.card_zmultiples ];
    rw [ addOrderOf_eq_iff ] <;> norm_num;
    exact ⟨ CharTwo.two_eq_zero, by intros m hm₁ hm₂; interval_cases m ; simp +decide ⟩;
  have h_card_range : Nat.card (AddMonoidHom.range (asHom (F := F) k)) * Nat.card (AddMonoidHom.ker (asHom (F := F) k)) = Nat.card F := by
    have := AddSubgroup.card_mul_index ( AddMonoidHom.ker ( asHom ( F := F ) k ) ) ; simp_all +decide [ AddSubgroup.index ] ;
    have := Nat.card_congr ( QuotientAddGroup.quotientKerEquivRange ( asHom ( F := F ) k ) ).toEquiv; simp_all +decide [ mul_comm ] ;
  have h_card_ker_trace : Nat.card (AddMonoidHom.ker (traceHom (F := F) n)) ≤ 2 ^ (n - 1) := by
    have h_card_ker_trunc : Nat.card (AddMonoidHom.range (traceHom (F := F) n)) ≥ 2 := by
      obtain ⟨ x, hx ⟩ := exists_trace_ne_zero hn ( by linarith );
      refine' le_trans _ ( Set.ncard_le_ncard ( show { 0, FiniteFieldCharTwo.truncTrace n x } ⊆ Set.range ( traceHom n ) from _ ) );
      · rw [ Set.ncard_pair ] ; aesop;
      · simp +decide [ Set.insert_subset_iff, Set.singleton_subset_iff ];
        exact ⟨ ⟨ 0, FiniteFieldCharTwo.truncTrace_zero n ⟩, ⟨ x, rfl ⟩ ⟩;
    have h_card_ker_trunc : Nat.card (AddMonoidHom.ker (traceHom (F := F) n)) * Nat.card (AddMonoidHom.range (traceHom (F := F) n)) = Nat.card F := by
      have := AddSubgroup.card_mul_index ( AddMonoidHom.ker ( traceHom ( F := F ) n ) ) ; simp_all +decide [ Nat.card_eq_fintype_card ] ;
      convert this using 1;
      rw [ AddSubgroup.index_ker ];
      simp +decide [ Set.setOf_exists ];
    cases n <;> simp_all +decide [ pow_succ' ] ; nlinarith [ Nat.pow_le_pow_right two_pos ( show ‹_› ≥ 0 by linarith ) ] ;
  have h_card_range_eq : Nat.card (AddMonoidHom.range (asHom (F := F) k)) = 2 ^ (n - 1) := by
    rcases n with ( _ | n ) <;> simp_all +decide [ pow_succ' ];
    grind;
  have h_eq : AddMonoidHom.range (asHom (F := F) k) = AddMonoidHom.ker (traceHom (F := F) n) := by
    have h_eq : AddMonoidHom.range (asHom (F := F) k) ≤ AddMonoidHom.ker (traceHom (F := F) n) := by
      rintro _ ⟨ x, rfl ⟩ ; exact trace_artin_schreier_zero hn k x;
    exact SetLike.ext' ( Set.eq_of_subset_of_ncard_le h_eq ( by simpa [ Set.ncard_eq_toFinset_card' ] using h_card_range_eq.ge.trans' h_card_ker_trace ) );
  replace h_eq := SetLike.ext_iff.mp h_eq y; simp_all +decide [ AddMonoidHom.mem_ker ] ;
  exact h_eq.mpr hy

/-
`t^{2^k} = t` forces `t ∈ 𝔽₂` (i.e. `t^2 = t`) when `gcd(k,n) = 1`.
-/
omit [CharP F 2] in
theorem frob_k_fixed {n : ℕ} (hn : Fintype.card F = 2 ^ n) {k : ℕ}
    (_hk : 0 < k) (hcop : Nat.Coprime k n) {t : F} (h : t ^ (2 ^ k) = t) :
    t ^ 2 = t := by
  -- By induction on $m$, we show that $t^{2^{mk}} = t$ for any $m$.
  have h_ind : ∀ m : ℕ, t ^ (2 ^ (m * k)) = t := by
    intro m; induction m <;> simp_all +decide [ Nat.succ_mul, pow_add, pow_mul ] ;
  -- Since $k$ and $n$ are coprime, there exists an integer $m$ such that $mk \equiv 1 \pmod{n}$.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m * k ≡ 1 [MOD n] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime hcop;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ mul_comm, Nat.ModEq ];
    · exact ⟨ 0, by simp +decide ⟩;
    · exact ⟨ this.choose, this.choose_spec.2 ⟩;
  convert h_ind m using 1;
  rw [ ← Nat.mod_add_div ( m * k ) n, hm ] ; simp +decide [ pow_add, pow_mul, hn.symm, FiniteField.pow_card ] ;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_eq_of_lt ];
  · have := FiniteField.pow_card t; aesop;
  · rw [ ← hn, FiniteField.pow_card_pow ]

/-! ## The core sum-collapse and routine computation -/

/-
Collapse of the Kasami numerator sum:
`∑_{i=1}^{k'} (t^{2^k}+t)^{2^{ik}} = (t²+t)^{2^k}` using `t^{2^{k'k}} = t²`.
-/
theorem sum_u_collapse {n t0 k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ kk) (hkk : kk * k = t0 * n + 1) (t : F) :
    (∑ i ∈ Finset.Ico 1 (kk + 1), (t ^ (2 ^ k) + t) ^ (2 ^ (i * k)))
      = (t ^ 2 + t) ^ (2 ^ k) := by
  have h_sum_telescope : ∑ i ∈ Finset.Ico 1 (kk + 1), (t ^ (2 ^ k) + t) ^ (2 ^ (i * k)) = ∑ i ∈ Finset.Ico 1 (kk + 1), (t ^ (2 ^ (i * k)) + t ^ (2 ^ ((i + 1) * k))) := by
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ add_pow_char_pow ] ; ring;
  convert sum_pair_telescope kk hk ( fun i => t ^ 2 ^ ( i * k ) ) using 1;
  · rw [ h_sum_telescope, Finset.sum_add_distrib ];
  · rw [ add_pow_char_pow ];
    rw [ show t ^ 2 ^ ( ( kk + 1 ) * k ) = ( t ^ 2 ^ ( kk * k ) ) ^ 2 ^ k by ring, show t ^ 2 ^ ( kk * k ) = t ^ 2 by rw [ show t ^ 2 ^ ( kk * k ) = t ^ 2 by rw [ x_pow_reduce n t0 k kk t ( by rw [ ← hn, FiniteField.pow_card ] ) hkk ] ] ] ; ring

/-
**The routine computation** (proof of Corollary 2): for `k'` odd and
`t ∉ 𝔽₂`, `D(t) · q(t^{2^k}+t) = 1`.
-/
theorem routine_computation {n t0 k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 1 < k) (hkn : k < n) (hkk1 : 1 ≤ kk) (hkk : kk * k = t0 * n + 1)
    (hkk_odd : Odd kk) {t : F} (hu : t ^ (2 ^ k) + t ≠ 0) :
    Dder k t * qPoly k kk (t ^ (2 ^ k) + t) = 1 := by
  rw [ qPoly, sum_u_collapse hn hkk1 hkk t, eps_zero hkk_odd ];
  convert mul_inv_cancel₀ ( pow_ne_zero _ hu ) using 1;
  convert congr_arg ( fun x : F => x * ( ( t ^ 2 ^ k + t ) ^ ( 2 ^ k + 1 ) ) ⁻¹ ) ( KasamiPerm.MCMtoAPN.kasami_key_identity hn k ( by omega ) hkn t ) using 1 ; ring;
  unfold Dder; ring;

/-! ## `q` is a permutation (from Theorem 5) -/

/-
Bridge: on `𝔽_{2ⁿ}`, the Theorem-5 polynomial `qeps` coincides with the
Theorem-6 polynomial `qPoly`.
-/
omit [CharP F 2] in
theorem qeps_eq_qPoly {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (z : F) :
    KasamiPerm.TraceFree.qeps n k kk ((kk + 1 : ℕ) : F) z = qPoly k kk z := by
  by_cases hz : z = 0 <;> simp +decide [ hz, TraceFree.qeps, qPoly ];
  · exact Or.inr ( Nat.sub_ne_zero_of_lt hexp );
  · congr! 1;
    have h_exp : z ^ (2 ^ n - 1) = 1 := by
      rw [ ← hn, FiniteField.pow_card_sub_one_eq_one z hz ];
    exact eq_inv_of_mul_eq_one_left ( by rw [ ← pow_add, Nat.sub_add_cancel ( show 2 ^ k + 1 ≤ 2 ^ n - 1 from le_of_lt hexp ), h_exp ] )

/-
`qPoly` is a bijection of `𝔽_{2ⁿ}` (Theorem 5, `k'` odd case).
-/
theorem qPoly_bijective {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n)
    (hkk' : k * kk % n = 1) (hexp : 2 ^ k + 1 < 2 ^ n - 1) (hkk_odd : Odd kk) :
    Function.Bijective (qPoly (L := F) k kk) := by
  convert KasamiPerm.TraceFree.qeps_bijective_iff hn hk hkn hcop hkk' hexp ( Or.inl ( eps_zero hkk_odd ) ) using 1;
  simp_all +decide [ Nat.even_iff, Nat.odd_iff ];
  rw [ show ( TraceFree.qeps n k kk ( kk + 1 : F ) ) = qPoly k kk from funext fun x => ?_ ];
  · rw [ CharP.cast_eq_zero_iff F 2 ] ; simp_all +decide [ Nat.even_iff ];
  · convert qeps_eq_qPoly hn hexp x using 1;
    norm_cast

/-! ## Theorem 8 -/

/-
**Theorem 8 (Dobbertin 1999), case `k'` odd.**  An element `x ∈ 𝔽_{2ⁿ}` lies
in the Kasami difference set `B = {(t+1)^d + t^d + 1 : t}` if and only if
`Tr(R(x)) = 0`, where `R` is the explicit compositional inverse of the Kasami
permutation (Theorem 6) and `Tr` is the absolute trace.
-/
theorem derivImage_iff_trace_zero {n t0 k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 1 < k) (hkn : k < n) (hcop : Nat.Coprime k n)
    (hkk : kk * k = t0 * n + 1) (hkk_odd : Odd kk)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (x : F) :
    x ∈ Bset k ↔ FiniteFieldCharTwo.truncTrace n (Rpoly k kk x) = 0 := by
  constructor;
  · rintro ⟨ t, rfl ⟩;
    by_cases h : Dder k t = 0;
    · simp +decide [ h, Rpoly_zero ( by linarith : 0 < k ) ( by nlinarith : 1 ≤ kk ) ];
      exact FiniteFieldCharTwo.truncTrace_zero n;
    · have h_u_ne_zero : t ^ (2 ^ k) + t ≠ 0 := by
        intro h_zero
        have h_contra : t ^ 2 = t := by
          apply frob_k_fixed hn (by linarith) hcop;
          grind;
        by_cases ht : t = 0 <;> simp_all +decide [ sq ];
        · exact h ( Dder_zero k );
        · exact h ( by rw [ Dder_one ] );
      have h_u_eq_Rpoly : t ^ (2 ^ k) + t = Rpoly k kk (Dder k t) := by
        apply KasamiPerm.InverseCubic.q_inv_eq_Rpoly;
        any_goals tauto;
        · exact Nat.pos_of_ne_zero hkk_odd.pos.ne';
        · rw [ ← hn, FiniteField.pow_card ];
        · exact eq_inv_of_mul_eq_one_right ( routine_computation hn hk hkn ( Nat.pos_of_ne_zero ( by aesop ) ) hkk hkk_odd h_u_ne_zero );
      rw [ ← h_u_eq_Rpoly, trace_artin_schreier_zero hn k t ];
  · by_cases hx : x = 0;
    · exact fun _ => ⟨ 0, by simp +decide [ hx, Dder_zero ] ⟩;
    · intro hTr
      obtain ⟨t, ht⟩ : ∃ t : F, t ^ (2 ^ k) + t = Rpoly k kk x := by
        apply artin_schreier_surj hn (by linarith) hkn hcop hTr;
      obtain ⟨v, hv⟩ : ∃ v : F, qPoly k kk v = x⁻¹ := by
        have := KasamiPerm.TraceCore.qPoly_bijective hn ( by linarith ) hkn hcop ( by rw [ mul_comm, hkk ] ; simp +decide [ Nat.add_mod, Nat.mod_eq_of_lt ( show 1 < n from by linarith ) ] ) hexp hkk_odd;
        exact this.surjective _;
      have hv_eq : v = Rpoly k kk x := by
        apply KasamiPerm.InverseCubic.q_inv_eq_Rpoly n t0 k kk v x (by
        exact Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide )) (by
        exact hx) (by
        grind +suggestions) (by
        rw [ ← hn, FiniteField.pow_card ]) hkk hv;
      have hDder : Dder k t * qPoly k kk (t ^ (2 ^ k) + t) = 1 := by
        apply routine_computation hn hk hkn (by
        exact Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide )) hkk hkk_odd (by
        intro h; simp_all +decide [ qPoly ] ;
        grind);
      simp_all +decide [ Bset ];
      exact ⟨ t, eq_inv_of_mul_eq_one_left hDder ▸ by simp +decide ⟩

end Field

end KasamiPerm.TraceCore
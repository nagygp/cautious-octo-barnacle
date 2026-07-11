import Mathlib
import KasamiPermutation.TraceFreeCriterion
import KasamiPermutation.TraceVersionInfra
import KasamiPermutation.TraceVersionBase

/-!
# Parity-general trace-version Kasami permutation criterion (`q₁`)

The library file `TraceVersionBase.lean` proves that the *trace version*
`g(x) = q^{(Tr x)}(x) = (S(x) + Tr(x))·x^{(2ⁿ−1)−(2^k+1)}` of the Kasami
polynomial is a **permutation** of `𝔽_{2ⁿ}` in the single parity case
`k'` even, `n` odd (`KasamiPerm.TraceParityCase.gmap_bijective`).

For Dobbertin's **Theorem 1** in full generality (the `α = 1` case), we need the
permutation criterion for `q₁` for *all* admissible parities.  Since `k'` (the
inverse of `k` mod `n`) is coprime to `n`, `k'` and `n` are never both even, so the
three possible parities are

* `k'` even, `n` odd     → `k' + n` odd  → `g` is a permutation (library case);
* `k'` odd,  `n` even    → `k' + n` odd  → `g` is a permutation (**new here**);
* `k'` odd,  `n` odd     → `k' + n` even → `g` is *not* a permutation.

This module packages the criterion as
`gmap_bijective_iff : Bijective g ↔ Odd (k' + n)` by generalizing the library's
`Even kk ∧ Odd n` hypotheses to the single parity criterion `Odd (kk + n)`.  The
proofs mirror `TraceVersionBase.lean` verbatim except that the final parity computation
uses `S(1) + Tr(1) = (k' + n : F)`, which is `1` exactly when `k' + n` is odd.
-/

namespace KasamiPerm.TraceCriterion

open Finset BigOperators FiniteFieldCharTwo
open KasamiPerm KasamiPerm.TraceParityCase KasamiPerm.TraceFree

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-
Cast of a natural number into `F` is a bit determined by parity.
-/
theorem natCast_parity {m : ℕ} : ((m : ℕ) : F) = if Even m then 0 else 1 := by
  rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> simp +decide [ *, CharTwo.two_eq_zero ]

/-
**Non-vanishing of the trace-version numerator (parity-general).**  Under the
criterion `Odd (kk + n)`, `S(x) + Tr(x) ≠ 0` for all `x ≠ 0`.  Generalizes
`KasamiPerm.TraceParityCase.sTrace_add_trace_ne_zero`.
-/
theorem sTrace_add_trace_ne_zero_gen {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * kk % n = 1) (hcrit : Odd (kk + n)) {x : F} (hx : x ≠ 0) :
    sTrace k kk x + truncTrace n x ≠ 0 := by
  by_contra h_contra;
  -- As in the library, `(pTrace k kk x)^(2^k) = truncTrace n x` (a bit, by `trace_bit`).
  have h_ptrace : (pTrace k kk x) ^ (2 ^ k) = truncTrace n x := by
    rw [ ← eq_neg_iff_add_eq_zero ] at h_contra;
    rw [ ← sTrace_eq_pTrace, h_contra, neg_eq_of_add_eq_zero_left ];
    simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
  -- Since $y \mapsto y^{2^k}$ is injective, we get $pTrace k kk x = truncTrace n x$.
  have h_ptrace_eq : pTrace k kk x = truncTrace n x := by
    have h_ptrace_eq : Function.Injective (fun y : F => y ^ (2 ^ k)) := by
      have h_ptrace_eq : Function.Bijective (fun y : F => y ^ (2 ^ k)) := by
        have h_frob : Function.Bijective (fun y : F => y ^ (2 ^ k)) := by
          have h_frob : ∀ y : F, y ^ (2 ^ n) = y := by
            exact fun y => by rw [ ← hn, FiniteField.pow_card ] ;
          exact?
        exact h_frob;
      exact h_ptrace_eq.injective;
    have := trace_bit hn x; aesop;
  -- The Artin–Schreier telescoping `pTrace^(2^k) + pTrace = x^2 + x` then forces `x^2 + x = 0`, i.e. `x = 1` (since `x ≠ 0`).
  have h_x_one : x ^ 2 + x = 0 := by
    have h_x_one : (pTrace k kk x) ^ (2 ^ k) + pTrace k kk x = x ^ 2 + x := by
      apply KasamiPerm.TraceFree.pTrace_telescope hn hkk' x;
    grind +ring;
  -- Since $x \neq 0$, we have $x = 1$.
  have h_x_one : x = 1 := by
    grind +suggestions;
  -- Then `sTrace k kk 1 + truncTrace n 1 = (kk : F) + (n : F)`.
  have h_sum : sTrace k kk 1 + truncTrace n 1 = (kk : F) + (n : F) := by
    simp +decide [ sTrace_one, FiniteFieldCharTwo.truncTrace ];
  obtain ⟨ m, hm ⟩ := hcrit; simp_all +decide ;
  norm_cast at *; simp_all +decide ;

/-
**A solution has `Q ≠ 0` (trace version, parity-general).**  Generalizes
`KasamiPerm.TraceParityCase.sol_qPoly_ne_zero_trace`.
-/
theorem sol_qPoly_ne_zero_trace_gen {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * kk % n = 1) (hcrit : Odd (kk + n))
    {γ c t : F} (hγ : γ ≠ 0) (hcdef : c = γ ^ (2 ^ k + 1) + γ)
    (hεt : c * t ^ (2 ^ k + 1) + sTrace k kk t + truncTrace n t = 0) :
    KasamiPerm.TraceFree.qPoly γ c k t ≠ 0 := by
  intro hq0
  have ht_step : t ^ (2 ^ k) = (γ * t) ^ (2 ^ k) + γ * t + 1 := by
    convert KasamiPerm.TraceFree.qPoly_zero_step hγ hcdef hq0 using 1;
  have ht_trace : truncTrace n t = (n : F) := by
    have ht_trace : truncTrace n t = truncTrace n (γ * t) + truncTrace n (γ * t) + truncTrace n 1 := by
      have h_trace_step : truncTrace n (t ^ (2 ^ k)) = truncTrace n ((γ * t) ^ (2 ^ k) + γ * t + 1) := by
        rw [ht_step];
      grind +suggestions;
    have ht_trace_one : truncTrace n 1 = (n : F) := by
      simp +decide [ FiniteFieldCharTwo.truncTrace ];
    grind;
  have ht_sTrace : sTrace k kk t = (γ * t) ^ 2 + γ * t + (kk : F) := by
    convert KasamiPerm.TraceFree.sTrace_telescope_gen hn hkk' ( Or.inr rfl ) _ using 1;
    rotate_left;
    exacts [ γ * t, ht_step, by ring ];
  have ht_qPoly_zero : c * t ^ (2 ^ k + 1) = (γ * t) ^ 2 + γ * t := by
    unfold qPoly at hq0;
    grind +splitImp;
  grind +splitIndPred

set_option maxHeartbeats 800000 in
/-- **Root count, Case 2 (trace version, parity-general).**  Generalizes
`KasamiPerm.TraceParityCase.root_count_image_trace`. -/
theorem root_count_image_trace_gen {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hcrit : Odd (kk + n)) {c x y : F}
    (hc : c ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hex : sTrace k kk x + truncTrace n x = c * x ^ (2 ^ k + 1))
    (hey : sTrace k kk y + truncTrace n y = c * y ^ (2 ^ k + 1))
    (hg : ∃ γ : F, c = γ ^ (2 ^ k + 1) + γ) :
    x = y := by
  obtain ⟨γ, hcdef⟩ := hg;
  have hΓγ : (γ ^ (2 ^ k - 1) + γ⁻¹) * γ ^ 2 = c := by
    by_cases hγ : γ = 0 <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm];
    simp +decide [ mul_add, ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ), hγ ]
  have hQx : KasamiPerm.TraceFree.qPoly γ c k x ≠ 0 := by
    apply sol_qPoly_ne_zero_trace_gen hn hkk' hcrit;
    · grind +qlia;
    · exact hcdef;
    · grind +ring
  have hQy : KasamiPerm.TraceFree.qPoly γ c k y ≠ 0 := by
    apply sol_qPoly_ne_zero_trace_gen hn hkk' hcrit;
    · grind;
    · exact hcdef;
    · grind +ring
  have hQeq : KasamiPerm.TraceFree.qPoly γ c k x = KasamiPerm.TraceFree.qPoly γ c k y := by
    have hQeq : (KasamiPerm.TraceFree.qPoly γ c k x) ^ (2 ^ k - 1) = γ ^ (2 ^ k - 1) + γ⁻¹ ∧ (KasamiPerm.TraceFree.qPoly γ c k y) ^ (2 ^ k - 1) = γ ^ (2 ^ k - 1) + γ⁻¹ := by
      have hQeq : c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1 = 0 ∧ c ^ (2 ^ k) * y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + c * y + 1 = 0 := by
        grind +suggestions;
      have hQeq : (KasamiPerm.TraceFree.qPoly γ c k x) ^ (2 ^ k) + (γ ^ (2 ^ k - 1) + γ⁻¹) * (KasamiPerm.TraceFree.qPoly γ c k x) = 0 ∧ (KasamiPerm.TraceFree.qPoly γ c k y) ^ (2 ^ k) + (γ ^ (2 ^ k - 1) + γ⁻¹) * (KasamiPerm.TraceFree.qPoly γ c k y) = 0 := by
        convert hQeq using 1;
        · rw [ ← Q_factor ];
          · grind +qlia;
          · exact hcdef;
        · grind +suggestions;
      have hQeq : (KasamiPerm.TraceFree.qPoly γ c k x) ^ (2 ^ k - 1) * (KasamiPerm.TraceFree.qPoly γ c k x) = (γ ^ (2 ^ k - 1) + γ⁻¹) * (KasamiPerm.TraceFree.qPoly γ c k x) ∧ (KasamiPerm.TraceFree.qPoly γ c k y) ^ (2 ^ k - 1) * (KasamiPerm.TraceFree.qPoly γ c k y) = (γ ^ (2 ^ k - 1) + γ⁻¹) * (KasamiPerm.TraceFree.qPoly γ c k y) := by
        simp_all +decide [ ← eq_sub_iff_add_eq', pow_succ, pow_mul ];
        rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ] ; simp +decide [ CharTwo.neg_eq ] ;
        rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide ) ) ];
      exact ⟨ mul_left_cancel₀ hQx <| by linear_combination' hQeq.1, mul_left_cancel₀ hQy <| by linear_combination' hQeq.2 ⟩;
    have := KasamiPerm.TraceFree.pow2k1_inj hn hk hcop;
    exact this ( hQeq.1.trans hQeq.2.symm );
  by_cases hxy : x = y;
  · exact hxy;
  · set d := x + y
    have hd : d ≠ 0 := by
      grind +qlia
    have hker : c * d ^ (2 ^ k) + γ ^ 2 * d = 0 := by
      simp_all +decide [ KasamiPerm.TraceFree.qPoly ];
      rw [ show d = x + y from rfl ] ; rw [ add_pow_char_pow ] ; ring;
      grind
    have hstepd : d ^ (2 ^ k) = (γ * d) ^ (2 ^ k) + γ * d + 0 := by
      simp_all +decide [ mul_pow, pow_add ];
      grind +suggestions
    have htrd : truncTrace n d = 0 := by
      have := KasamiPerm.TraceCore.trace_artin_schreier_zero hn k d; simp_all +decide [ add_comm, add_left_comm ] ;
      grind +suggestions
    have htrxy : truncTrace n x + truncTrace n y = 0 := by
      rw [ ← htrd, FiniteFieldCharTwo.truncTrace_add ]
    have hSd := KasamiPerm.TraceFree.sTrace_telescope_gen hn hkk' (Or.inl rfl) hstepd
    have hSadd := KasamiPerm.TraceFree.sTrace_add k kk x y
    simp_all +decide [ add_eq_zero_iff_eq_neg ];
    simp_all +decide [ KasamiPerm.TraceFree.qPoly, pow_add ];
    grind +ring

/-- **The root count (trace version, parity-general).**  Generalizes
`KasamiPerm.TraceParityCase.root_count_trace`. -/
theorem root_count_trace_gen {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hcrit : Odd (kk + n)) {c x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hex : sTrace k kk x + truncTrace n x = c * x ^ (2 ^ k + 1))
    (hey : sTrace k kk y + truncTrace n y = c * y ^ (2 ^ k + 1)) :
    x = y := by
  by_contra hxy;
  have h_trace_sq : (c ^ (2 ^ k)) * (x + y) ^ (2 ^ (2 * k)) + (x + y) ^ (2 ^ k) + c * (x + y) = 0 := by
    have h_trace_sq : c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1 = 0 ∧ c ^ (2 ^ k) * y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + c * y + 1 = 0 := by
      grind +suggestions;
    rw [ add_pow_char_pow, add_pow_char_pow ] ; ring_nf;
    grind;
  have h_trace_sq : ∃ γ : F, c = γ ^ (2 ^ k + 1) + γ := by
    apply KasamiPerm.TraceFree.ell0_root_imp_image hn hk hkn (by
    intro hc; simp_all +decide [ sTrace_add_trace_ne_zero_gen hn hkk' hcrit ] ;) (by
    grind +qlia) h_trace_sq;
  exact hxy ( root_count_image_trace_gen hn hk hcop hkk' hcrit ( show c ≠ 0 from fun h => by simp_all +decide [ sTrace_add_trace_ne_zero_gen ] ) hx hy hex hey h_trace_sq )

/-- `g(x) ≠ 0` for `x ≠ 0` (parity-general). -/
theorem gmap_ne_zero_gen {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * kk % n = 1) (hcrit : Odd (kk + n)) {x : F} (hx : x ≠ 0) :
    TraceParityCase.gmap n k kk x ≠ 0 := by
  exact mul_ne_zero (sTrace_add_trace_ne_zero_gen hn hkk' hcrit hx) (pow_ne_zero _ hx)

/-
**`g` is a permutation of `𝔽_{2ⁿ}` (parity-general "if" direction).**
-/
theorem gmap_bijective_of_crit {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hcrit : Odd (kk + n)) (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    Function.Bijective (TraceParityCase.gmap (F := F) n k kk) := by
  refine' ⟨ _, _ ⟩;
  · intro x y hxy
    by_cases hx : x = 0
    by_cases hy : y = 0
    all_goals generalize_proofs at *;
    · rw [ hx, hy ];
    · have := gmap_ne_zero_gen hn hkk' hcrit hy; simp_all +decide [ gmap ] ;
      contrapose! hxy; simp_all +decide [ qeps ] ;
      simp_all +decide [ sTrace, truncTrace ];
    · by_cases hy : y = 0 <;> simp_all +decide [ gmap ];
      · contrapose! hxy; simp_all +decide [ qeps_zero ] ;
        exact gmap_ne_zero_gen hn hkk' hcrit hx;
      · grind +suggestions;
  · convert Finite.injective_iff_surjective.mp _;
    · infer_instance;
    · intro x y hxy
      by_cases hx : x = 0
      by_cases hy : y = 0;
      · rw [ hx, hy ];
      · have := gmap_ne_zero_gen hn hkk' hcrit hy; simp_all +decide [ gmap ] ;
        contrapose! hxy; simp_all +decide [ qeps ] ;
        simp_all +decide [ sTrace, truncTrace ];
      · by_cases hy : y = 0 <;> simp_all +decide [ gmap ];
        · contrapose! hxy; simp_all +decide [ qeps_zero ] ;
          exact gmap_ne_zero_gen hn hkk' hcrit hx;
        · grind +suggestions

/-
**`g` is not a permutation when the parity criterion fails.**  If `kk + n` is
even then `g(0) = g(1) = 0`, so `g` is not injective.
-/
theorem gmap_not_bijective_of_not_crit {n k kk : ℕ}
    (hcrit : ¬ Odd (kk + n))
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    ¬ Function.Bijective (TraceParityCase.gmap (F := F) n k kk) := by
  intro hbij; have := hbij.injective; simp_all +decide [ TraceParityCase.gmap ] ;
  convert @this 0 1 ?_ using 1;
  · simp +decide;
  · unfold gmap; simp +decide [ KasamiPerm.TraceFree.qeps, FiniteFieldCharTwo.truncTrace ] ;
    rw [ zero_pow ( Nat.sub_ne_zero_of_lt hexp ) ] ; simp +decide [ sTrace_one, natCast_parity ] ;
    grind

/-- **The trace-version permutation criterion.**  `g = q₁` is a permutation of
`𝔽_{2ⁿ}` iff `k' + n` is odd. -/
theorem gmap_bijective_iff {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    Function.Bijective (TraceParityCase.gmap (F := F) n k kk) ↔ Odd (kk + n) := by
  constructor
  · intro hbij
    by_contra hcrit
    exact gmap_not_bijective_of_not_crit hcrit hexp hbij
  · intro hcrit
    exact gmap_bijective_of_crit hn hk hkn hcop hkk' hcrit hexp

end KasamiPerm.TraceCriterion
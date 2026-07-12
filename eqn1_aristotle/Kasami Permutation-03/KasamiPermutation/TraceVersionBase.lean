import Mathlib
import RequestProject.KasamiPermutation.TraceVersionInfra

/-!
# Theorem 8 (Dobbertin 1999) — the `c = 1` case (`k'` even, `n` odd)

This file completes **Theorem 8** for the remaining case `c = 1`, i.e. `k'` even
and `n` odd, where the generalized Kasami *permutation* is `q = q₁` (the `ε = 1`
version).  Following Dobbertin, the extra ingredient beyond the `k'`-odd case is
the **`q`-vs-`q₁` image argument**:

> the *trace* version `g` of the Kasami polynomial (which uses `ε = Tr(z)` instead
> of a constant `ε`) is a permutation; it agrees with `q₁` on `Tr⁻¹(1)` and with
> `q₀` on `Tr⁻¹(0)`.  Hence, although `q₀` and `q₁` do **not** coincide on
> `T₀ = Tr⁻¹(0)`, their *images* of `T₀` coincide:
> `q₀[T₀] = g[T₀] = L ∖ g[T₁] = L ∖ q₁[T₁] = q₁[T₀]`.

Combined with the routine computation `D(t)·q₀(t^{2^k}+t) = 1` and additive
Hilbert 90, this yields Theorem 8 in the `c = 1` case.

Here `q₀ = qeps n k k' 0` and `q₁ = qeps n k k' 1 = qPoly` (for `k'` even), where
`qeps` is the trace-free Kasami polynomial of Theorem 5.
-/

namespace KasamiPerm.TraceParityCase

open scoped BigOperators
open KasamiPerm.TraceFree KasamiPerm.TraceCore KasamiPerm.InverseCubic FiniteFieldCharTwo

section Field

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## Elementary trace facts -/

/-
On `𝔽_{2ⁿ}` the absolute trace is idempotent under squaring:
`Tr(x)² = Tr(x)`.
-/
theorem trace_sq {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    (truncTrace n x) ^ 2 = truncTrace n x := by
  have := @truncTrace_sq_add_self F _ _ n x;
  simp_all +decide [ ← hn, FiniteField.pow_card ];
  grind

/-
On `𝔽_{2ⁿ}` the absolute trace is a bit: `Tr(x) ∈ {0,1}`.
-/
theorem trace_bit {n : ℕ} (hn : Fintype.card F = 2 ^ n) (x : F) :
    truncTrace n x = 0 ∨ truncTrace n x = 1 := by
  have := trace_sq hn x; simp_all +decide [ pow_succ' ] ;
  grind

/-
For `n` even the constant `ε = (k'+1)` cast to `F` equals `1` in char two.
-/
theorem eps_one {kk : ℕ} (hkk : Even kk) : ((kk + 1 : ℕ) : F) = 1 := by
  obtain ⟨ k, rfl ⟩ := even_iff_two_dvd.mp hkk;
  simp +decide [ CharTwo.two_eq_zero ]

/-! ## Core non-vanishing: `S(x) + Tr(x) ≠ 0` for `x ≠ 0` -/

/-
**Non-vanishing of the trace-version numerator.**  For `k'` even and `n` odd,
`S(x) + Tr(x) ≠ 0` for all `x ≠ 0`, where `S(x) = ∑_{i=1}^{k'} x^{2^{ik}}`.

If `S(x) + Tr(x) = 0` then `P(x)^{2^k} = Tr(x)` (a bit), so `P(x) = Tr(x)`, and the
Artin–Schreier telescoping `P^{2^k}+P = x²+x` forces `x² + x = 0`, i.e. `x = 1`.
But then `S(1) + Tr(1) = k' + 1 = 0 + 1 = 1 ≠ 0` (using `k'` even and `n` odd).
-/
theorem sTrace_add_trace_ne_zero {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * kk % n = 1) (hkeven : Even kk) (hnodd : Odd n) {x : F} (hx : x ≠ 0) :
    sTrace k kk x + truncTrace n x ≠ 0 := by
  by_cases h : sTrace k kk x + truncTrace n x = 0;
  · -- By `sTrace_eq_pTrace`, `(pTrace k kk x)^(2^k) = sTrace k kk x = ε`. Since `ε` is a bit, `ε^(2^k) = ε` (`bit_pow`), so `(pTrace k kk x)^(2^k) = ε = ε^(2^k)`; as `y ↦ y^(2^k)` is injective (`frob_bijective 2 k`), `pTrace k kk x = ε`.
    have h_pTrace : pTrace k kk x = truncTrace n x := by
      have h_pTrace : (pTrace k kk x) ^ (2 ^ k) = truncTrace n x := by
        convert eq_neg_of_add_eq_zero_left h using 1;
        · rw [ KasamiPerm.TraceFree.sTrace_eq_pTrace ];
        · rw [ eq_neg_iff_add_eq_zero, ← two_smul F, CharTwo.two_eq_zero, zero_smul ];
      have h_pTrace_bit : (pTrace k kk x) ^ (2 ^ k) = truncTrace n x ∧ (truncTrace n x) ^ (2 ^ k) = truncTrace n x := by
        exact ⟨ h_pTrace, by rcases trace_bit hn x with h | h <;> simp +decide [ h ] ⟩;
      have h_frob_bijective : Function.Bijective (fun y : F => y ^ (2 ^ k)) := by
        exact FiniteFieldCharTwo.frob_bijective 2 k;
      exact h_frob_bijective.injective ( by aesop );
    grind +suggestions;
  · exact h

/-! ## The root count for the trace version -/

/-
**A solution has `Q ≠ 0` (trace version).**  If `t` solves the trace-version
equation `c·t^{2^k+1} + S(t) + Tr(t) = 0` (with `c = γ^{2^k+1}+γ`, `γ ≠ 0`), then
the Case-2 quadratic `Q(t) = c t^{2^k} + γ² t + γ` is nonzero.

If `Q(t) = 0` the step lemma gives `t^{2^k} = (γt)^{2^k} + γt + 1`; taking traces
yields `Tr(t) = Tr(1) = 1` (as `n` is odd).  The driven telescoping then gives
`S(t) = (γt)² + γt + k'` and `c t^{2^k+1} = (γt)² + γt`, so
`c t^{2^k+1} + S(t) + Tr(t) = k' + 1 = 0 + 1 = 1 ≠ 0`.
-/
theorem sol_qPoly_ne_zero_trace {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * kk % n = 1) (hkeven : Even kk) (hnodd : Odd n)
    {γ c t : F} (hγ : γ ≠ 0) (hcdef : c = γ ^ (2 ^ k + 1) + γ)
    (hεt : c * t ^ (2 ^ k + 1) + sTrace k kk t + truncTrace n t = 0) :
    KasamiPerm.TraceFree.qPoly γ c k t ≠ 0 := by
  intro hq
  have hstep : t ^ (2 ^ k) = (γ * t) ^ (2 ^ k) + γ * t + 1 := by
    convert TraceFree.qPoly_zero_step hγ hcdef hq using 1
  have htr : truncTrace n t = 1 := by
    have htr : truncTrace n t = truncTrace n (γ * t) + truncTrace n (γ * t) + 1 := by
      have htr : truncTrace n (t ^ (2 ^ k)) = truncTrace n ((γ * t) ^ (2 ^ k) + γ * t + 1) := by
        rw [hstep];
      grind +suggestions;
    grobner
  have hSt : sTrace k kk t = (γ * t) ^ 2 + γ * t + (kk : F) := by
    convert sTrace_telescope_gen hn hkk' ( Or.inr rfl ) hstep using 1;
    ring
  have hct : c * t ^ (2 ^ k + 1) = (γ * t) ^ 2 + γ * t := by
    unfold TraceFree.qPoly at hq; simp_all +decide [ pow_succ, pow_mul ] ;
    grind +ring
  have hfinal : (kk : F) + 1 = 0 := by
    grind;
  obtain ⟨ m, rfl ⟩ := even_iff_two_dvd.mp hkeven; simp_all +decide [ Nat.even_add_one ] ;
  grind

/-
**Root count, Case 2 (trace version).**  Two nonzero solutions `x, y` of the
trace-version equation with `c` in the image of `γ ↦ γ^{2^k+1}+γ` are equal.

Mirrors `KasamiPerm.TraceFree.root_count_image`: both `Q(x), Q(y) ≠ 0`
(`sol_qPoly_ne_zero_trace`), then `Q(x)^{2^k-1} = Γ = Q(y)^{2^k-1}` gives
`Q(x) = Q(y)`; with `d = x + y`, the step `d^{2^k} = (γd)^{2^k}+γd` has `b = 0`, so
`Tr(d) = 0` (hence `Tr(x) = Tr(y)`, the two `ε`-terms cancel), and the driven
telescoping produces the contradiction `1 = 0` unless `d = 0`.
-/
set_option maxHeartbeats 800000 in
theorem root_count_image_trace {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hkeven : Even kk) (hnodd : Odd n) {c x y : F}
    (hc : c ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hex : sTrace k kk x + truncTrace n x = c * x ^ (2 ^ k + 1))
    (hey : sTrace k kk y + truncTrace n y = c * y ^ (2 ^ k + 1))
    (hg : ∃ γ : F, c = γ ^ (2 ^ k + 1) + γ) :
    x = y := by
  obtain ⟨γ, hcdef⟩ := hg;
  have hΓγ : (γ ^ (2 ^ k - 1) + γ⁻¹) * γ ^ 2 = c := by
    by_cases hγ : γ = 0 <;> simp_all +decide [ pow_succ, mul_assoc, mul_comm, mul_left_comm ];
    simp +decide [ mul_add, ← pow_succ', Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ), hγ ]
  have hQx : KasamiPerm.TraceFree.qPoly γ c k x ≠ 0 := by
    apply sol_qPoly_ne_zero_trace hn hkk' hkeven hnodd;
    · grind +qlia;
    · exact hcdef;
    · grind +ring
  have hQy : KasamiPerm.TraceFree.qPoly γ c k y ≠ 0 := by
    apply sol_qPoly_ne_zero_trace hn hkk' hkeven hnodd;
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
      simp_all +decide [ TraceFree.qPoly ];
      rw [ show d = x + y from rfl ] ; rw [ add_pow_char_pow ] ; ring;
      grind
    have hstepd : d ^ (2 ^ k) = (γ * d) ^ (2 ^ k) + γ * d + 0 := by
      simp_all +decide [ mul_pow, pow_add ];
      grind +suggestions
    have htrd : truncTrace n d = 0 := by
      have := trace_artin_schreier_zero hn k d; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
      grind +suggestions
    have htrxy : truncTrace n x + truncTrace n y = 0 := by
      rw [ ← htrd, FiniteFieldCharTwo.truncTrace_add ]
    have hSd := KasamiPerm.TraceFree.sTrace_telescope_gen hn hkk' (Or.inl rfl) hstepd
    have hSadd := KasamiPerm.TraceFree.sTrace_add k kk x y
    simp_all +decide [ add_eq_zero_iff_eq_neg ];
    simp_all +decide [ TraceFree.qPoly, pow_add ];
    grind +ring

/-
**The root count (trace version).**  The trace-version Kasami map is injective
on units: `g(x) = g(y) = c` (i.e. `S(x)+Tr(x) = c x^{2^k+1}` and similarly for `y`)
forces `x = y`.

`c ≠ 0` by `sTrace_add_trace_ne_zero`; both `x, y` satisfy the linearized `ℓ = 0`
(`ell_of_eq`, valid for any bit `ε`).  If `c` is **not** in the image of
`γ ↦ γ^{2^k+1}+γ` then `ℓ₀` is injective and additivity forces `x = y`
(`ell0_root_imp_image`); otherwise use `root_count_image_trace`.
-/
theorem root_count_trace {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hkeven : Even kk) (hnodd : Odd n) {c x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hex : sTrace k kk x + truncTrace n x = c * x ^ (2 ^ k + 1))
    (hey : sTrace k kk y + truncTrace n y = c * y ^ (2 ^ k + 1)) :
    x = y := by
  by_contra hxy;
  -- Apply the lemma that states if the trace of x is not zero, then the trace of x squared is equal to the trace of x.
  have h_trace_sq : (c ^ (2 ^ k)) * (x + y) ^ (2 ^ (2 * k)) + (x + y) ^ (2 ^ k) + c * (x + y) = 0 := by
    have h_trace_sq : c ^ (2 ^ k) * x ^ (2 ^ (2 * k)) + x ^ (2 ^ k) + c * x + 1 = 0 ∧ c ^ (2 ^ k) * y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + c * y + 1 = 0 := by
      grind +suggestions;
    rw [ add_pow_char_pow, add_pow_char_pow ] ; ring_nf;
    grind;
  have h_trace_sq : ∃ γ : F, c = γ ^ (2 ^ k + 1) + γ := by
    apply ell0_root_imp_image hn hk hkn (by
    intro hc; simp_all +decide [ sTrace_add_trace_ne_zero hn hkk' hkeven hnodd ] ;) (by
    grind +qlia) h_trace_sq;
  exact hxy ( root_count_image_trace hn hk hcop hkk' hkeven hnodd ( show c ≠ 0 from fun h => by simp_all +decide [ sTrace_add_trace_ne_zero ] ) hx hy hex hey h_trace_sq )

/-! ## The trace-version permutation `g` -/

/-- The **trace version** `g(x) = q^{(Tr x)}(x)` of the Kasami polynomial: it uses
the actual trace `Tr(x)` in place of a constant bit. -/
noncomputable def gmap (n k kk : ℕ) (x : F) : F := qeps n k kk (truncTrace n x) x

/-
`g(x) ≠ 0` for `x ≠ 0`.
-/
theorem gmap_ne_zero {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hkk' : k * kk % n = 1) (hkeven : Even kk) (hnodd : Odd n)
    {x : F} (hx : x ≠ 0) :
    gmap n k kk x ≠ 0 := by
  exact mul_ne_zero ( sTrace_add_trace_ne_zero hn hkk' hkeven hnodd hx ) ( pow_ne_zero _ hx )

/-
**`g` is a permutation of `𝔽_{2ⁿ}`.**
-/
theorem gmap_bijective {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hkeven : Even kk) (hnodd : Odd n) (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    Function.Bijective (gmap (F := F) n k kk) := by
  refine' ⟨ _, _ ⟩;
  · intro x y hxy;
    by_cases hx : x = 0 <;> by_cases hy : y = 0;
    · rw [ hx, hy ];
    · have := gmap_ne_zero hn hkk' hkeven hnodd hy; simp_all +decide [ gmap ] ;
      exact False.elim ( this ( hxy ▸ by rw [ FiniteFieldCharTwo.truncTrace_zero ] ; exact KasamiPerm.TraceFree.qeps_zero ( Nat.sub_pos_of_lt hexp ) _ ) );
    · have := gmap_ne_zero hn hkk' hkeven hnodd hx; simp_all +decide [ gmap ] ;
      exact this ( KasamiPerm.TraceFree.qeps_zero ( Nat.sub_pos_of_lt hexp ) _ );
    · have h_eq : sTrace k kk x + truncTrace n x = (gmap n k kk x) * x ^ (2 ^ k + 1) ∧ sTrace k kk y + truncTrace n y = (gmap n k kk y) * y ^ (2 ^ k + 1) := by
        exact ⟨ by exact Eq.symm ( KasamiPerm.TraceFree.qeps_mul_unit hn k kk ( by linarith ) _ hx ), by exact Eq.symm ( KasamiPerm.TraceFree.qeps_mul_unit hn k kk ( by linarith ) _ hy ) ⟩;
      exact root_count_trace hn hk hkn hcop hkk' hkeven hnodd hx hy ( by rw [ h_eq.1, hxy ] ) ( by rw [ h_eq.2 ] );
  · convert Finite.injective_iff_surjective.mp _;
    · infer_instance;
    · intro x y hxy
      by_cases hx : x = 0
      by_cases hy : y = 0;
      · rw [ hx, hy ];
      · have := gmap_ne_zero hn hkk' hkeven hnodd hy; simp_all +decide [ gmap ] ;
        exact False.elim ( this ( hxy ▸ by rw [ FiniteFieldCharTwo.truncTrace_zero ] ; exact KasamiPerm.TraceFree.qeps_zero ( Nat.sub_pos_of_lt hexp ) _ ) );
      · by_cases hy : y = 0;
        · have := gmap_ne_zero hn hkk' hkeven hnodd hx; simp_all +decide [ gmap ] ;
          exact this ( KasamiPerm.TraceFree.qeps_zero ( Nat.sub_pos_of_lt hexp ) _ );
        · have h_eq : sTrace k kk x + truncTrace n x = (gmap n k kk x) * x ^ (2 ^ k + 1) ∧ sTrace k kk y + truncTrace n y = (gmap n k kk y) * y ^ (2 ^ k + 1) := by
            exact ⟨ by exact Eq.symm ( KasamiPerm.TraceFree.qeps_mul_unit hn k kk ( by linarith ) _ hx ), by exact Eq.symm ( KasamiPerm.TraceFree.qeps_mul_unit hn k kk ( by linarith ) _ hy ) ⟩;
          exact root_count_trace hn hk hkn hcop hkk' hkeven hnodd hx hy ( by rw [ h_eq.1, hxy ] ) ( by rw [ h_eq.2 ] )

/-! ## `q₁ = qPoly` and the inverse relation -/

/-
For `k'` even, `q₁ = qeps n k k' 1` coincides with the Theorem-6 permutation
`qPoly`.
-/
theorem qeps_one_eq_qPoly {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (hkeven : Even kk) (z : F) :
    qeps n k kk (1 : F) z = qPoly k kk z := by
  unfold qeps InverseCubic.qPoly;
  by_cases hz : z = 0 <;> simp_all +decide [ sTrace ];
  · grind;
  · have h_inv : z ^ (2 ^ n - 1) = 1 := by
      rw [ ← hn, FiniteField.pow_card_sub_one_eq_one z hz ];
    convert congr_arg ( fun x : F => x * z ^ ( 2 ^ n - 1 - ( 2 ^ k + 1 ) ) ) ( show ( ∑ i ∈ Finset.Ico 1 ( kk + 1 ), z ^ 2 ^ ( i * k ) + 1 ) = ( ∑ i ∈ Finset.Ico 1 ( kk + 1 ), z ^ 2 ^ ( i * k ) + ( kk + 1 : F ) ) from ?_ ) using 1;
    · rw [ inv_eq_of_mul_eq_one_right ];
      rw [ ← pow_add, Nat.add_sub_of_le hexp.le, h_inv ];
    · grind +splitIndPred

/-
`qPoly` is a permutation for `k'` even.
-/
theorem qPoly_bijective_even {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (hkeven : Even kk) :
    Function.Bijective (qPoly (L := F) k kk) := by
  convert TraceFree.qeps_bijective_iff hn hk hkn hcop hkk' hexp ( Or.inr rfl ) using 1;
  rw [ show ( InverseCubic.qPoly k kk : F → F ) = qeps n k kk 1 from funext fun x => by rw [ qeps_one_eq_qPoly hn hexp hkeven ] ] ; simp +decide [ hkeven ]

/-
`R` inverts `qPoly`: `qPoly (R(x)) = 1/x` for `x ≠ 0`.
-/
theorem qPoly_Rpoly {n t0 k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hkk : kk * k = t0 * n + 1) (hkeven : Even kk) (hexp : 2 ^ k + 1 < 2 ^ n - 1)
    {x : F} (hx : x ≠ 0) :
    qPoly k kk (Rpoly k kk x) = x⁻¹ := by
  obtain ⟨w, hw⟩ : ∃ w : F, InverseCubic.qPoly k kk w = x⁻¹ := by
    convert ( qPoly_bijective_even hn hk hkn hcop hkk' hexp hkeven ).2 x⁻¹ using 1;
  convert hw using 1;
  rw [ InverseCubic.q_inv_eq_Rpoly n t0 k kk w x (by
  exact Nat.pos_of_ne_zero ( by rintro rfl; simp_all +decide )) hx (by
  intro hw_zero
  simp [hw_zero] at hw;
  exact hx ( inv_eq_zero.mp ( hw.symm.trans ( qPoly_zero k kk ) ) )) (by
  rw [ ← hn, FiniteField.pow_card ]) hkk hw ]

/-! ## The image argument -/

/-
**The image argument** `q₀[T₀] = q₁[T₀]`, where `T₀ = Tr⁻¹(0)`.

`g` agrees with `q₀` on `T₀` and with `q₁` on `T₁ = T₀ᶜ`; since `g` and `q₁` are
both permutations, `q₀[T₀] = g[T₀] = (g[T₁])ᶜ = (q₁[T₁])ᶜ = q₁[T₀]`.
-/
theorem image_eq {n k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 0 < k) (hkn : k < n) (hcop : Nat.Coprime k n) (hkk' : k * kk % n = 1)
    (hkeven : Even kk) (hnodd : Odd n) (hexp : 2 ^ k + 1 < 2 ^ n - 1) :
    (qeps n k kk (0 : F)) '' {z : F | truncTrace n z = 0}
      = (qeps n k kk (1 : F)) '' {z : F | truncTrace n z = 0} := by
  have h_compl : Set.image (gmap (F := F) n k kk) {z : F | truncTrace n z ≠ 0} = Set.image (qeps n k kk 1) {z : F | truncTrace n z ≠ 0} := by
    refine' Set.image_congr fun x hx => _;
    have := trace_bit hn x; have := trace_bit hn 1; simp_all +decide ;
    unfold gmap; aesop;
  have h_compl : Set.image (gmap (F := F) n k kk) {z : F | truncTrace n z ≠ 0}ᶜ = (Set.image (gmap (F := F) n k kk) {z : F | truncTrace n z ≠ 0})ᶜ := by
    apply Set.image_compl_eq;
    apply gmap_bijective hn hk hkn hcop hkk' hkeven hnodd hexp;
  have h_compl : Set.image (qeps n k kk 1) {z : F | truncTrace n z ≠ 0}ᶜ = (Set.image (qeps n k kk 1) {z : F | truncTrace n z ≠ 0})ᶜ := by
    apply Set.image_compl_eq;
    convert qPoly_bijective_even hn hk hkn hcop hkk' hexp hkeven using 1;
    exact funext fun x => qeps_one_eq_qPoly hn hexp hkeven x;
  have h_compl : Set.image (gmap (F := F) n k kk) {z : F | truncTrace n z = 0} = Set.image (qeps n k kk 0) {z : F | truncTrace n z = 0} := by
    exact Set.image_congr fun x hx => by unfold gmap; aesop;
  simp_all +decide [ Set.ext_iff ]

/-! ## The routine computation (`ε = 0` form) -/

/-
**Routine computation, `ε = 0` form.**  For `u = t^{2^k}+t ≠ 0`,
`D(t)·q₀(u) = 1`, where `q₀ = qeps n k k' 0`.  (This holds for all `k'`; the
constant `ε` is genuinely `0` here, so no parity hypothesis is needed.)
-/
theorem routine_qeps0 {n t0 k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 1 < k) (hkn : k < n) (hkk1 : 1 ≤ kk) (hkk : kk * k = t0 * n + 1)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) {t : F} (hu : t ^ (2 ^ k) + t ≠ 0) :
    Dder k t * qeps n k kk (0 : F) (t ^ (2 ^ k) + t) = 1 := by
  -- Let `u = t^(2^k)+t` (hypothesis `hu : u ≠ 0`). Set `hexp' : 2^k+1 ≤ 2^n-1` from `hexp`.
  let u := t ^ (2 ^ k) + t
  have hu' : u ≠ 0 := hu
  have hexp' : 2 ^ k + 1 ≤ 2 ^ n - 1 := by
    exact le_of_lt hexp;
  -- Now `qeps n k kk 0 u * u^(2^k+1) = sTrace k kk u + 0 = sTrace k kk u` by `qeps_mul_unit`.
  have h_qeps_mul_unit : qeps n k kk 0 u * u ^ (2 ^ k + 1) = sTrace k kk u := by
    convert KasamiPerm.TraceFree.qeps_mul_unit hn k kk hexp' 0 hu' using 1 ; simp +decide;
  -- And `sTrace k kk u = ∑ i ∈ Finset.Ico 1 (kk+1), u^(2^(i*k))` (since `Finset.Icc 1 kk = Finset.Ico 1 (kk+1)`), which by `sum_u_collapse` equals `(t^2+t)^(2^k)`.
  have h_sum_u_collapse : sTrace k kk u = (t ^ 2 + t) ^ (2 ^ k) := by
    convert KasamiPerm.TraceCore.sum_u_collapse hn hkk1 hkk t using 1;
  -- Unfolding `Dder` (which is `(t+1)^(kExp k) + t^(kExp k) + 1`), this equals `((t+1)^(kasamiExp k) + t^(kasamiExp k) + 1) * (t^2+t)^(2^k)`.
  have h_Dder : Dder k t * (t ^ 2 + t) ^ (2 ^ k) = u ^ (2 ^ k + 1) := by
    convert KasamiPerm.MCMtoAPN.kasami_key_identity hn k ( by linarith ) ( by linarith ) t using 1;
  exact mul_left_cancel₀ ( pow_ne_zero ( 2 ^ k + 1 ) hu' ) ( by linear_combination' h_Dder + h_qeps_mul_unit * Dder k t + h_sum_u_collapse * Dder k t )

/-! ## Theorem 8, case `c = 1` -/

/-
**Theorem 8 (Dobbertin 1999), case `c = 1` (`k'` even, `n` odd).**  An element
`x ∈ 𝔽_{2ⁿ}` lies in the Kasami difference set `B = {(t+1)^d + t^d + 1 : t}` iff
`Tr(R(x)) = 0`, where `R` is the explicit compositional inverse of the Kasami
permutation (Theorem 6) and `Tr` is the absolute trace.

`Odd n` is not assumed separately: it follows from `Even kk` and
`kk·k = t0·n + 1`.
-/
set_option maxHeartbeats 800000 in
theorem derivImage_iff_trace_zero_evenCase {n t0 k kk : ℕ} (hn : Fintype.card F = 2 ^ n)
    (hk : 1 < k) (hkn : k < n) (hcop : Nat.Coprime k n)
    (hkk : kk * k = t0 * n + 1) (hkeven : Even kk)
    (hexp : 2 ^ k + 1 < 2 ^ n - 1) (x : F) :
    x ∈ Bset k ↔ FiniteFieldCharTwo.truncTrace n (Rpoly k kk x) = 0 := by
  constructor;
  · rintro ⟨ t, rfl ⟩;
    by_cases h : Dder k t = 0;
    · rw [ h, Rpoly_zero ];
      · exact FiniteFieldCharTwo.truncTrace_zero n;
      · linarith;
      · grind;
    · obtain ⟨u, hu⟩ : ∃ u : F, truncTrace n u = 0 ∧ qeps n k kk (1 : F) u = (Dder k t)⁻¹ := by
        obtain ⟨u, hu⟩ : ∃ u : F, truncTrace n u = 0 ∧ qeps n k kk (0 : F) u = (Dder k t)⁻¹ := by
          have := routine_qeps0 hn hk hkn (by
          contrapose! h; aesop) hkk hexp (by
          intro H;
          have h_frob_k_fixed : t ^ 2 = t := by
            apply frob_k_fixed hn (by linarith) hcop;
            grind;
          cases eq_or_ne t 0 <;> simp_all +decide [ pow_succ' ];
          · exact h ( Dder_zero k );
          · exact h ( by rw [ Dder_one ] ) : t ^ (2 ^ k) + t ≠ 0);
          exact ⟨ t ^ 2 ^ k + t, trace_artin_schreier_zero hn k t, eq_inv_of_mul_eq_one_right this ⟩;
        have := KasamiPerm.TraceParityCase.image_eq hn ( by linarith ) ( by linarith ) hcop ( by
          rw [ mul_comm, hkk, Nat.add_mod ];
          rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ] ) hkeven ( by
          replace hkk := congr_arg Even hkk; simp_all +decide [ parity_simps ] ; ) hexp;
        exact this.subset ⟨ u, hu.1, hu.2 ⟩;
      have hu_eq : u = Rpoly k kk (Dder k t) := by
        apply q_inv_eq_Rpoly;
        any_goals assumption;
        · contrapose! h; aesop;
        · intro hu_zero
          simp [hu_zero] at hu;
          simp_all +decide [ qeps ];
          simp_all +decide [ Nat.sub_ne_zero_of_lt hexp ];
        · rw [ ← hn, FiniteField.pow_card ];
        · rw [ ← hu.2, qeps_one_eq_qPoly hn hexp hkeven ];
      aesop;
  · by_cases hx : x = 0;
    · exact fun _ => ⟨ 0, by simp +decide [ hx, Dder_zero ] ⟩;
    · intro hTr
      set v := Rpoly k kk x
      have hv0 : v ≠ 0 := by
        intro hv0
        have hq : qPoly k kk v = x⁻¹ := by
          apply qPoly_Rpoly hn (by linarith) (by linarith) hcop (by
          rw [ mul_comm, hkk, Nat.add_mod ] ; norm_num [ Nat.mod_eq_of_lt ( show 1 < n from by linarith ) ]) hkk hkeven hexp hx;
        simp_all +decide [ InverseCubic.qPoly ]
      have hvn : v ^ (2 ^ n) = v := by
        rw [ ← hn, FiniteField.pow_card ]
      have hv_eq : qPoly k kk v = x⁻¹ := by
        apply qPoly_Rpoly hn (by linarith) (by linarith) hcop (by
        rw [ mul_comm, hkk, Nat.add_mod ] ; norm_num [ Nat.mod_eq_of_lt ( show 1 < n from by linarith ) ]) hkk hkeven hexp hx;
      -- By `image_eq` (symm), `x⁻¹ ∈ (qeps n k kk 0) '' {z|truncTrace n z=0}`: obtain `u` with `truncTrace n u = 0` and `qeps n k kk 0 u = x⁻¹`.
      obtain ⟨u, hu⟩ : ∃ u : F, truncTrace n u = 0 ∧ qeps n k kk 0 u = x⁻¹ := by
        have h_image_eq : (qeps n k kk (0 : F)) '' {z : F | truncTrace n z = 0} = (qeps n k kk (1 : F)) '' {z : F | truncTrace n z = 0} := by
          apply KasamiPerm.TraceParityCase.image_eq hn (by linarith) (by linarith) hcop (by
          rw [ mul_comm, hkk, Nat.add_mod ];
          rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ]) hkeven (by
          replace hkk := congr_arg Even hkk; simp_all +decide [ parity_simps ] ;) hexp;
        have hv_eq : qeps n k kk 1 v = x⁻¹ := by
          rw [ ← hv_eq, qeps_one_eq_qPoly hn hexp hkeven ];
        exact h_image_eq.symm.subset ⟨ v, hTr, hv_eq ⟩;
      -- By `artin_schreier_surj`, obtain `t` with `t^(2^k)+t = u`.
      obtain ⟨t, ht⟩ : ∃ t : F, t ^ (2 ^ k) + t = u := by
        apply artin_schreier_surj hn (by linarith) hkn hcop hu.left;
      have hDder : Dder k t * qeps n k kk 0 (t ^ (2 ^ k) + t) = 1 := by
        apply routine_qeps0 hn hk hkn (by
        grind) hkk hexp (by
        grind +suggestions);
      have hDder_eq : Dder k t = x := by
        grind;
      exact ⟨ t, hDder_eq ⟩

end Field

end KasamiPerm.TraceParityCase
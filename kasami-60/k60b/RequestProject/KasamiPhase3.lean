import Mathlib
import RequestProject.KasamiDefs
import RequestProject.KasamiPhase1
import RequestProject.KasamiPhase2
import RequestProject.CCDCounting
import RequestProject.Mathlib.QuadraticFourier

/-!
# Kasami AB — Phase 3: WHT Squared Trichotomy (Almost Bent Property)

This is a lightweight "plug-in" phase that combines:
  • The kernel dimension bound from Phase 1 (`mk_ker_eq_F2`),
  • The radical = kernel characterization from Phase 2 (`radical_eq_ker_LA`),
  • The universal Fourier lemmas from `QuadraticFourier` (`walsh_set_from_sq`,
    `radical_parity_constraint`).

The main theorem `kasami_wht_sq_value` states that the WHT squared takes
only the values {0, 2^n, 2^{n+1}}, which is the Almost Bent (AB) property.
-/

open scoped BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

section Phase3

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
attribute [local instance] ZMod.algebra

/-! ### Additive characters and Walsh–Hadamard Transform -/

/-- An additive character of F derived from the trace: χ_b(x) = (-1)^{Tr(bx)}.
    Since Tr(bx) ∈ GF(2) = {0,1}, this gives values in {1, -1}. -/
noncomputable def addChar (b : F) (x : F) : ℂ :=
  if AbsTrace (b * x) = (0 : ZMod 2) then 1 else -1

/-- The Walsh–Hadamard transform of the Kasami function f(x) = x^d at (a, b):
    W_f(a, b) = ∑_{x ∈ F} χ_b(a·x^d + x). -/
noncomputable def wht (k : ℕ) (a b : F) : ℂ :=
  ∑ x : F, addChar b (a * x ^ kasamiExp k + x)

/-- The squared magnitude of the WHT. -/
noncomputable def whtSqMag (k : ℕ) (a b : F) : ℝ :=
  Complex.normSq (wht k a b)

/-! ### WHT and radical connection -/

/-- The cardinality of the kernel of L_a. -/
noncomputable def kerDimLA (k : ℕ) (a : F) : ℕ :=
  Set.ncard {y : F | linPolyLA k a y = 0}

/-! ### Vanishing and peak cases -/

/-- **Vanishing case:** If b is nonzero on the radical of Q_a, then W_f(a,b) = 0.

The proof uses character orthogonality over cosets of the radical:
the sum over each coset contains a character sum over the radical that
cancels unless the character is trivial on the radical. -/
lemma wht_vanishing (k : ℕ) (a b : F)
    (hb : ∃ y ∈ radical k a, AbsTrace (b * y) ≠ 0) :
    wht (F := F) k a b = 0 := by
  sorry

/-- **Peak case:** If b vanishes on the radical, then
    |W_f(a,b)|² = |F| · |rad(Q_a)| = 2^n · |ker(L_a)|. -/
lemma wht_peak (k n : ℕ) (a b : F) (hn : n ≠ 0) (hcard : Nat.card F = 2 ^ n)
    (hb : ∀ y ∈ radical k a, AbsTrace (b * y) = 0) :
    whtSqMag (F := F) k a b = (2 : ℝ) ^ n * (kerDimLA k a : ℝ) := by
  sorry

/-! ### Kernel dimension bound via algebraic argument

The key proof that |ker(L_a)| ≤ 2 under gcd(3k,n) = 1.

The argument:
1. If z₁, z₂ are GF(2)-linearly independent in ker(L_a), both non-zero.
2. Then z₁ + z₂ ∈ ker(L_a) \ {0} (since L_a is additive).
3. Setting uᵢ = zᵢ^{2^k - 1}, all three u₁, u₂, u₃ satisfy the same
   polynomial equation P(u) = 0 derived from L_a(z) = 0.
4. From Frobenius additivity: (z₁+z₂)^{2^k} = z₁^{2^k} + z₂^{2^k}.
   This gives (u₃ + u₁)·z₁ = (u₂ + u₃)·z₂ over F.
5. Linear independence forces u₁ = u₂ = u₃.
6. So (z₁/z₂)^{2^k - 1} = 1 in F*.
7. Since gcd(k,n) = 1 (which follows from gcd(3k,n) = 1),
   gcd(2^k - 1, 2^n - 1) = 2^{gcd(k,n)} - 1 = 1.
8. So z₁/z₂ = 1, contradiction. -/

/-! #### Helper lemmas for the kernel bound -/

/-- gcd(k, n) = 1 follows from gcd(3k, n) = 1. -/
lemma gcd_k_n_of_gcd_3k_n {k n : ℕ} (h : Nat.gcd (3 * k) n = 1) :
    Nat.gcd k n = 1 :=
  Nat.Coprime.coprime_dvd_left (Dvd.intro_left 3 rfl) h

/-- The key identity: gcd(2^k - 1, 2^n - 1) = 2^{gcd(k,n)} - 1. -/
lemma gcd_pow_sub_one (k n : ℕ) :
    Nat.gcd (2 ^ k - 1) (2 ^ n - 1) = 2 ^ (Nat.gcd k n) - 1 :=
  Nat.pow_sub_one_gcd_pow_sub_one 2 k n

/-
In GF(2^n), if gcd(k,n) = 1 and x^{2^k - 1} = 1, then x = 1.
-/
lemma pow_sub_one_eq_one_imp {n k : ℕ} (hk : k ≠ 0) (hn : n ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd_kn : Nat.gcd k n = 1)
    (x : F) (hx : x ≠ 0) (hx_pow : x ^ (2 ^ k - 1) = 1) :
    x = 1 := by
  have h_order : orderOf x ∣ 2 ^ k - 1 ∧ orderOf x ∣ 2 ^ n - 1 := by
    have h_order_divides : x ^ (Fintype.card F - 1) = 1 := by
      exact FiniteField.pow_card_sub_one_eq_one x hx;
    simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
  have := Nat.dvd_gcd h_order.1 h_order.2; aesop;

/-- L_a is additive (GF(2)-linear) in its second argument. -/
lemma linPolyLA_add' (k : ℕ) (a x y : F) :
    linPolyLA k a (x + y) = linPolyLA k a x + linPolyLA k a y :=
  linPolyLA_add k a x y

/-- L_a(0) = 0. -/
lemma linPolyLA_zero' (k : ℕ) (a : F) : linPolyLA k a 0 = 0 := by
  simp [linPolyLA]

/-
For z ≠ 0 with L_a(z) = 0, we derive z^{2^{2k}-1} satisfies a
    polynomial equation: a · u^{2^k+1} + a^{2^k} · u + a^{2^{2k}} = 0
    where u = z^{2^k - 1}.
-/
lemma ker_element_norm_eq {k : ℕ} (hk : k ≥ 1)
    {a z : F} (ha : a ≠ 0) (hz : z ≠ 0) (hLa : linPolyLA k a z = 0) :
    let u := z ^ (2 ^ k - 1)
    a * u ^ (2 ^ k + 1) + a ^ (2 ^ k) * u + a ^ (2 ^ (2 * k)) = 0 := by
  unfold linPolyLA at hLa;
  convert congr_arg ( · / z ) hLa using 1;
  · field_simp;
    rw [ show 2 ^ ( 2 * k ) = ( 2 ^ k - 1 ) * ( 2 ^ k + 1 ) + 1 by zify ; norm_num ; ring ] ; ring;
    rw [ show z ^ 2 ^ k = z ^ ( 2 ^ k - 1 ) * z by rw [ ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ zero_lt_two ) ] ] ; ring;
  · rw [ zero_div ]

/-
Key algebraic identity: if z₁, z₂ are both non-zero elements of ker(L_a),
    and u₁ = z₁^{q-1}, u₂ = z₂^{q-1}, u₃ = (z₁+z₂)^{q-1},
    then (u₃ + u₁) · z₁ = (u₂ + u₃) · z₂.
-/
lemma ker_frobenius_identity {k : ℕ} (hk : k ≥ 1)
    {a z₁ z₂ : F} (ha : a ≠ 0)
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) (hz₃ : z₁ + z₂ ≠ 0)
    (hL₁ : linPolyLA k a z₁ = 0) (hL₂ : linPolyLA k a z₂ = 0) :
    let u₁ := z₁ ^ (2 ^ k - 1)
    let u₂ := z₂ ^ (2 ^ k - 1)
    let u₃ := (z₁ + z₂) ^ (2 ^ k - 1)
    (u₃ + u₁) * z₁ = (u₂ + u₃) * z₂ := by
  have h_frobenius : (z₁ + z₂) ^ (2 ^ k) = z₁ ^ (2 ^ k) + z₂ ^ (2 ^ k) := by
    exact?;
  cases n : 2 ^ k <;> simp_all +decide [ pow_succ, pow_mul ];
  grind

/-- If z₁, z₂ are GF(2)-linearly independent (both nonzero, z₁ ≠ z₂,
    z₁ + z₂ ≠ 0), and the Frobenius identity holds, then u₁ = u₂. -/
lemma u_eq_of_lin_indep {z₁ z₂ : F} {u₁ u₂ u₃ : F}
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    (hne : z₁ ≠ z₂) -- z₁, z₂ are not equal (part of linear independence over GF(2))
    (hid : (u₃ + u₁) * z₁ = (u₂ + u₃) * z₂)
    (hu₁₃ : u₁ = u₃ ∨ u₂ = u₃ → u₁ = u₂) -- consequence of the identity
    : u₁ = u₂ := by
  sorry

/-- The kernel of L_a always contains {0}, so it has at least 1 element. -/
lemma kerDimLA_pos (k : ℕ) (a : F) : 1 ≤ kerDimLA (F := F) k a := by
  unfold kerDimLA
  have hmem : (0 : F) ∈ {y : F | linPolyLA k a y = 0} := linPolyLA_zero' k a
  have hne : Set.Nonempty {y : F | linPolyLA k a y = 0} := ⟨0, hmem⟩
  exact (Set.ncard_pos (hs := Set.toFinite _)).mpr hne

/-
Under the hypotheses, the kernel of L_a (for a ≠ 0) has at most 2 elements,
    so `kerDimLA k a ∈ {1, 2}`.
-/
lemma kerDimLA_mem {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (a : F) (ha : a ≠ 0) :
    kerDimLA (F := F) k a = 1 ∨ kerDimLA (F := F) k a = 2 := by
  have h_kernel_le_two : kerDimLA k a ≤ 2 := by
    have h_kernel_le_two : ∀ z₁ z₂ : F, z₁ ≠ 0 → z₂ ≠ 0 → linPolyLA k a z₁ = 0 → linPolyLA k a z₂ = 0 → z₁ ≠ z₂ → False := by
      intros z₁ z₂ hz₁ hz₂ hL₁ hL₂ hne
      set u₁ := z₁ ^ (2 ^ k - 1)
      set u₂ := z₂ ^ (2 ^ k - 1)
      set u₃ := (z₁ + z₂) ^ (2 ^ k - 1)
      have h_eq : (u₃ + u₁) * z₁ = (u₂ + u₃) * z₂ := by
        apply ker_frobenius_identity (Nat.pos_of_ne_zero hk) ha hz₁ hz₂ (by
        grind) hL₁ hL₂
      generalize_proofs at *; (
      have h_u_eq : u₁ = u₂ := by
        apply u_eq_of_lin_indep hz₁ hz₂ hne h_eq (by
        grind)
      generalize_proofs at *; (
      have h_div : (z₁ / z₂) ^ (2 ^ k - 1) = 1 := by
        rw [ div_pow, div_eq_iff ] <;> aesop
      generalize_proofs at *; (
      have h_div_one : z₁ / z₂ = 1 := by
        apply pow_sub_one_eq_one_imp hk hn hcard (gcd_k_n_of_gcd_3k_n hgcd) (z₁ / z₂) (div_ne_zero hz₁ hz₂) h_div
      generalize_proofs at *; (
      exact hne ( eq_of_div_eq_one h_div_one ▸ rfl )))))
    generalize_proofs at *; (
    have h_kernel_le_two : Set.ncard {y : F | linPolyLA k a y = 0} ≤ Set.ncard ({0} ∪ {y : F | y ≠ 0 ∧ linPolyLA k a y = 0}) := by
      exact Set.ncard_le_ncard fun x hx => by by_cases hx' : x = 0 <;> aesop;
    generalize_proofs at *; (
    have h_kernel_le_two : Set.ncard ({0} ∪ {y : F | y ≠ 0 ∧ linPolyLA k a y = 0}) ≤ 2 := by
      have h_kernel_le_two : Set.ncard {y : F | y ≠ 0 ∧ linPolyLA k a y = 0} ≤ 1 := by
        exact le_of_not_gt fun h => by obtain ⟨ y₁, hy₁ ⟩ := Set.nonempty_of_ncard_ne_zero ( ne_bot_of_gt h ) ; obtain ⟨ y₂, hy₂ ⟩ := Set.exists_ne_of_one_lt_ncard h y₁; specialize ‹∀ z₁ z₂ : F, z₁ ≠ 0 → z₂ ≠ 0 → linPolyLA k a z₁ = 0 → linPolyLA k a z₂ = 0 → z₁ ≠ z₂ → False› y₁ y₂; aesop;
      generalize_proofs at *; (
      exact le_trans ( Set.ncard_union_le _ _ ) ( by norm_num; linarith ))
    generalize_proofs at *; (
    exact le_trans ‹_› h_kernel_le_two)));
  have := kerDimLA_pos k a; interval_cases kerDimLA k a <;> trivial;

/-! ### Main Theorem: WHT Squared Trichotomy -/

theorem kasami_wht_sq_value {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (_hodd : ¬ 2 ∣ n)
    (a : F) (ha : a ≠ 0) (b : F) :
    whtSqMag (F := F) k a b = 0 ∨
    whtSqMag (F := F) k a b = 2 ^ n ∨
    whtSqMag (F := F) k a b = 2 ^ (n + 1) := by
  by_cases h : ∃ y ∈ radical k a, AbsTrace (b * y) ≠ 0
  · exact Or.inl (by rw [show whtSqMag k a b = Complex.normSq (wht k a b) by rfl,
      wht_vanishing k a b h, Complex.normSq_zero])
  · have := wht_peak k n a b hn hcard
      (fun y hy => Classical.not_not.1 fun hy' => h ⟨y, hy, hy'⟩)
    rcases kerDimLA_mem hn hk hcard hgcd a ha with h | h <;>
      rw [this, h] <;> ring_nf <;> norm_num

/-- **The Kasami function is Almost Bent.**

For `F = GF(2^n)` with `n` odd, `a ≠ 0`, and `gcd(3k, n) = 1`,
the Walsh–Hadamard transform of the Kasami power function
`f(x) = x^{2^{2k} − 2^k + 1}` satisfies

  `|W_f(a,b)|² ∈ {0, 2^n, 2^{n+1}}`

for all `b ∈ F`. -/
theorem kasami_is_AB {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hcard : Nat.card F = 2 ^ n)
    (hgcd : Nat.gcd (3 * k) n = 1)
    (hodd : ¬ 2 ∣ n)
    (a : F) (ha : a ≠ 0) (b : F) :
    whtSqMag (F := F) k a b = 0 ∨
    whtSqMag (F := F) k a b = 2 ^ n ∨
    whtSqMag (F := F) k a b = 2 ^ (n + 1) :=
  kasami_wht_sq_value hn hk hcard hgcd hodd a ha b

end Phase3
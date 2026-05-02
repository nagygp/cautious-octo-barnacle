/-
# Linearized Polynomial Kernel Theory

This module develops the kernel dimension theory for linearized polynomials
over finite fields of characteristic 2.

## Main results

* `linPoly_ker_card_pow_two` : |ker(L)| is a power of 2
* `linPolyM_ker_card` : |ker(M_k)| over GF(2^n) = 2^{gcd(k,n)}
* `linPolyL_ker_card_le` : |ker(L_k)| ≤ 2^{2k}
* `linPolyL_ker_trivial_of_three_ndvd` : ker(L_k) = {0} when gcd(k,n) = 1 and 3 ∤ n
* `linPolyL_ker_card_classification` : Complete classification of ker(L_k) size

## References

* Lidl, Niederreiter, *Finite Fields*, Theorems 3.50–3.62
-/
import Mathlib
import RequestProject.LinearizedPoly.Defs

set_option linter.unusedSectionVars false

open Finset BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Kernel as Finset -/

/-- The kernel of a function `P : F → F` as a `Finset`. -/
def funKer (P : F → F) : Finset F :=
  Finset.univ.filter (fun x => P x = 0)

/-- 0 is in the kernel of any linearized function. -/
theorem zero_mem_funKer {P : F → F} (hP : IsLinearizedFn P) :
    (0 : F) ∈ funKer P := by
  simp [funKer, hP.map_zero]

/-- The kernel of a linearized function is closed under addition. -/
theorem funKer_add {P : F → F} (hP : IsLinearizedFn P)
    {x y : F} (hx : x ∈ funKer P) (hy : y ∈ funKer P) :
    x + y ∈ funKer P := by
  simp only [funKer, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact hP.ker_add hx hy

/-! ### Kernel cardinality bounds -/

/-- |ker(L_k)| ≤ 2^{2k}. -/
theorem linPolyL_ker_card_le (k : ℕ) :
    (funKer (linPolyL (F := F) k)).card ≤ 2 ^ (2 * k) := by
  have h_eq_roots : funKer (linPolyL k) = Multiset.toFinset
      (Polynomial.roots
        ((Polynomial.X ^ (2 ^ (2 * k)) + Polynomial.X ^ (2 ^ k) + Polynomial.X) : Polynomial F)) := by
          ext x
          simp [funKer, linPolyL];
          intro hx; intro h; have := congr_arg ( Polynomial.eval 1 ) h; norm_num at this;
          grobner;
  refine' h_eq_roots ▸ le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
  rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
  simp +zetaDelta at *;
  intro m hm; split_ifs <;> simp_all +decide [ Polynomial.coeff_X ] ;
  · exact absurd hm ( not_lt_of_ge ( pow_le_pow_right₀ ( by decide ) ( by linarith ) ) );
  · rintro rfl; norm_cast at hm; simp_all +decide [ pow_mul' ]

/-- |ker(M_k)| ≤ 2^k (for k ≥ 1). -/
theorem linPolyM_ker_card_le (k : ℕ) (hk : 0 < k) :
    (funKer (linPolyM (F := F) k)).card ≤ 2 ^ k := by
  have h_kernel : (funKer (linPolyM (F := F) k)) = (Polynomial.roots (Polynomial.X ^ (2 ^ k) + Polynomial.X : Polynomial F)).toFinset := by
    unfold funKer linPolyM;
    ext x; simp +decide [ add_eq_zero_iff_eq_neg ] ;
    intro hx; intro h; have := congr_arg Polynomial.natDegree h; norm_num at this;
    linarith;
  refine' h_kernel ▸ le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
  rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num [ hk ];
  linarith

/-! ### Kernel cardinality is a power of 2 -/

/-- |ker(L)| is a power of 2 for any linearized function. -/
theorem linPoly_ker_card_pow_two {P : F → F} (hP : IsLinearizedFn P) :
    ∃ d : ℕ, (funKer P).card = 2 ^ d := by
  set G := funKer P with hG_def;
  have hG_iso : ∃ d : ℕ, Nonempty (G ≃ (Fin d → ZMod 2)) := by
    have hG_iso : ∀ (G : AddSubgroup F), (∀ x ∈ G, x + x = 0) → ∃ d : ℕ, Nonempty (↥G ≃ (Fin d → ZMod 2)) := by
      intro G hG
      have hG_iso : ∃ d : ℕ, Nonempty (↥G ≃ (Fin d → ZMod 2)) := by
        have hG_vector_space : Module (ZMod 2) ↥G := by
          have hG_vector_space : ∀ x : G, 2 • x = 0 := by
            simp_all +decide [ two_smul ];
          exact?
        exact ⟨ Module.finrank ( ZMod 2 ) G, ⟨ ( Module.finBasis ( ZMod 2 ) G ).equivFun ⟩ ⟩;
      exact hG_iso;
    convert hG_iso ( AddSubgroup.closure G ) _;
    · ext x; simp [hG_def];
      refine' ⟨ fun hx => AddSubgroup.subset_closure hx, fun hx => _ ⟩;
      refine' AddSubgroup.closure_induction ( fun y hy => _ ) _ _ _ hx;
      · exact hy;
      · exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by simp +decide [ IsLinearizedFn.map_zero hP ] ⟩;
      · exact fun x y hx hy hx' hy' => by simpa [ hP ] using funKer_add hP hx' hy';
      · grind +suggestions;
    · grind +qlia;
  obtain ⟨ d, ⟨ e ⟩ ⟩ := hG_iso; use d; have := Fintype.card_congr e; simp_all +decide ;

/-! ### Kernel dimension -/

/-- The kernel dimension of a linearized function `P` over 𝔽₂. -/
noncomputable def kerDim (P : F → F) : ℕ :=
  Nat.log 2 (funKer P).card

/-! ### Helper lemmas for Frobenius fixed points -/

/-
Iterating x^{2^k} = x gives x^{2^{k%n}} = x when |F| = 2^n.
-/
theorem frob_mod (n k : ℕ) (hn : 0 < n) (x : F)
    (hcard : Fintype.card F = 2 ^ n)
    (hk : x ^ (2 ^ k) = x) :
    x ^ (2 ^ (k % n)) = x := by
  -- By definition of exponentiation in finite fields, we know that $x^{2^n} = x$.
  have h_exp : x ^ (2 ^ n) = x := by
    rw [ ← hcard, FiniteField.pow_card ];
  rw [ ← Nat.mod_add_div k n ] at hk; simp_all +decide [ pow_add, pow_mul ] ;
  have h_exp_iter : ∀ m : ℕ, (x ^ (2 ^ (k % n))) ^ ((2 ^ n) ^ m) = x ^ (2 ^ (k % n)) := by
    intro m; induction m <;> simp_all +decide [ pow_succ, pow_mul ] ;
    rw [ pow_right_comm, h_exp ];
  rw [ ← h_exp_iter, hk ]

/-
The fixed points of σ^k equal those of σ^{gcd(k,n)}.
-/
theorem frob_fixed_gcd (n k : ℕ) (hn : 0 < n) (x : F)
    (hcard : Fintype.card F = 2 ^ n) :
    x ^ (2 ^ k) = x ↔ x ^ (2 ^ Nat.gcd k n) = x := by
  constructor <;> intro hx;
  · -- By the properties of the Frobenius endomorphism, we have that $x^{2^{\gcd(k, n)}} = x$.
    have h_frob_gcd : ∀ m n : ℕ, x ^ (2 ^ m) = x → x ^ (2 ^ n) = x → x ^ (2 ^ (Nat.gcd m n)) = x := by
      intros m n hm hn
      have h_frob_gcd : ∀ m n : ℕ, x ^ (2 ^ m) = x → x ^ (2 ^ n) = x → x ^ (2 ^ (m % n)) = x := by
        intros m n hm hn
        have h_frob_mod : x ^ (2 ^ (m % n)) = x := by
          have h_frob_mod_step : ∀ k : ℕ, x ^ (2 ^ (k * n + m % n)) = x ^ (2 ^ (m % n)) := by
            intro k
            induction' k with k ih;
            · simp +decide;
            · simp_all +decide [ add_mul, pow_add, pow_mul' ];
              simp_all +decide [ pow_right_comm ]
          rw [ ← h_frob_mod_step ( m / n ), Nat.div_add_mod' ] at * ; aesop;
        exact h_frob_mod;
      induction' n using Nat.strong_induction_on with n ih generalizing m;
      by_cases hn : n = 0;
      · aesop;
      · rw [ Nat.gcd_comm, Nat.gcd_rec ];
        simpa [ Nat.gcd_comm ] using ih ( m % n ) ( Nat.mod_lt _ ( Nat.pos_of_ne_zero hn ) ) n ‹_› ( h_frob_gcd m n hm ‹_› );
    apply h_frob_gcd k n hx;
    rw [ ← hcard, FiniteField.pow_card ];
  · rw [ ← Nat.mul_div_cancel' ( Nat.gcd_dvd_left k n ), pow_mul ];
    induction' k / Nat.gcd k n with m ih <;> simp_all +decide [ pow_succ, pow_mul ]

/-
The polynomial X^{2^m} - X has exactly 2^m roots in GF(2^n) when m | n.
    This is because X^{2^m} - X is separable (derivative = -1) and its roots
    form the subfield GF(2^m) ⊂ GF(2^n).
-/
theorem card_frob_fixed (m n : ℕ) (hn : 0 < n) (hm : m ∣ n)
    (hcard : Fintype.card F = 2 ^ n) :
    (Finset.univ.filter (fun x : F => x ^ (2 ^ m) = x)).card = 2 ^ m := by
  revert m;
  have h_card : ∀ m, m ∣ n → (Finset.filter (fun x : F => x ^ (2 ^ m) = x) Finset.univ).card = (Polynomial.roots (Polynomial.X ^ (2 ^ m) - Polynomial.X : Polynomial F)).toFinset.card := by
    intro m hm; congr; ext x; simp +decide [ sub_eq_zero ] ;
    intro hx; exact ne_of_apply_ne Polynomial.natDegree ( by rw [ Polynomial.natDegree_X_pow, Polynomial.natDegree_X ] ; aesop ) ;
  intro m hm;
  rw [ h_card m hm, eq_comm ];
  -- Since $m \mid n$, we have $X^{2^m} - X \mid X^{2^n} - X$.
  have h_div : (Polynomial.X ^ (2 ^ m) - Polynomial.X : Polynomial F) ∣ (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F) := by
    obtain ⟨ k, rfl ⟩ := hm;
    induction' k with k ih;
    · contradiction;
    · induction' k + 1 with k ih <;> simp_all +decide [ pow_succ, pow_mul ];
      have := dvd_trans ih ( sub_dvd_pow_sub_pow _ _ ( 2 ^ m ) );
      simpa using dvd_add this ( dvd_refl _ );
  -- Since $X^{2^n} - X$ splits into linear factors over $F$, it has exactly $2^n$ roots.
  have h_splits : (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F).roots.toFinset.card = 2 ^ n := by
    have h_splits : (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F).roots.toFinset = Finset.univ := by
      ext x; simp [hcard];
      exact ⟨ sub_ne_zero_of_ne <| ne_of_apply_ne Polynomial.natDegree <| by aesop, sub_eq_zero.mpr <| by rw [ ← hcard, FiniteField.pow_card ] ⟩;
    rw [ h_splits, Finset.card_univ, hcard ];
  obtain ⟨ q, hq ⟩ := h_div;
  have h_roots : (Polynomial.X ^ (2 ^ m) - Polynomial.X : Polynomial F).roots.toFinset.card + q.roots.toFinset.card ≥ 2 ^ n := by
    rw [ ← h_splits, hq, Polynomial.roots_mul ];
    · simp +decide [ Finset.card_union_add_card_inter ];
      exact Finset.card_union_le _ _;
    · intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
      exact absurd h_splits ( by positivity );
  have h_roots_q : q.roots.toFinset.card ≤ 2 ^ n - 2 ^ m := by
    refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
    have h_deg_q : Polynomial.natDegree (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F) = 2 ^ n := by
      rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
      linarith;
    rw [ hq, Polynomial.natDegree_mul' ] at h_deg_q <;> simp_all +decide [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
    · rw [ ← h_deg_q, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
      rintro rfl; simp_all +decide [ pow_eq_one_iff ];
    · constructor <;> intro h <;> simp_all +decide;
      · exact absurd h_splits ( by positivity );
      · exact absurd h_splits ( by positivity );
  have h_roots_p : (Polynomial.X ^ (2 ^ m) - Polynomial.X : Polynomial F).roots.toFinset.card ≤ 2 ^ m := by
    refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
    rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
    rintro rfl; simp_all +decide;
    exact absurd h_splits ( by positivity );
  linarith [ Nat.sub_add_cancel ( show 2 ^ m ≤ 2 ^ n from pow_le_pow_right₀ ( by decide ) ( Nat.le_of_dvd hn hm ) ) ]

/-! ### The key result: kernel of M_k over GF(2^n) -/

/-- **Kernel of `M_k(x) = x^{2^k} + x` over `GF(2^n)`**:
    `|ker(M_k)| = 2^{gcd(k,n)}`. -/
theorem linPolyM_ker_card (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n) (k : ℕ) :
    (funKer (linPolyM (F := F) k)).card = 2 ^ Nat.gcd k n := by
  have h_eq : funKer (linPolyM (F := F) k) =
      Finset.univ.filter (fun x : F => x ^ (2 ^ Nat.gcd k n) = x) := by
    ext x; simp only [funKer, linPolyM, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hfixed : x ^ (2 ^ k) = x := by
        have heq : x ^ (2 ^ k) + x = 0 := h
        have h1 : x ^ (2 ^ k) + x + x = x := by rw [heq, zero_add]
        rwa [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h1
      exact (frob_fixed_gcd n k hn x hcard).mp hfixed
    · intro h
      have hfixed : x ^ (2 ^ k) = x := (frob_fixed_gcd n k hn x hcard).mpr h
      show x ^ (2 ^ k) + x = 0
      rw [hfixed, CharTwo.add_self_eq_zero]
  rw [h_eq]
  exact card_frob_fixed (Nat.gcd k n) n hn (Nat.gcd_dvd_right k n) hcard

/-- When `gcd(k, n) = 1`, |ker(M_k)| = 2. -/
theorem linPolyM_ker_card_coprime (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n) (k : ℕ) (hgcd : Nat.Coprime k n) :
    (funKer (linPolyM (F := F) k)).card = 2 := by
  rw [linPolyM_ker_card n hn hcard k, hgcd, pow_one]

/-
When `gcd(k,n) = 1` and `k ≥ 1`, ker(M_k) = {0, 1}.
-/
theorem linPolyM_ker_eq_coprime (n : ℕ) (hn : 0 < n)
    (hcard : Fintype.card F = 2 ^ n) (k : ℕ) (hgcd : Nat.Coprime k n)
    (hk : 0 < k) :
    funKer (linPolyM (F := F) k) = {0, 1} := by
  have h_card : (funKer (linPolyM (F := F) k)).card = 2 := by
    exact?;
  rw [ Finset.card_eq_two ] at h_card;
  obtain ⟨ x, y, hxy, h ⟩ := h_card;
  simp_all +decide [ Finset.ext_iff, funKer ];
  have := h 0; have := h 1; simp_all +decide [ linPolyM ] ;
  grind

/-! ### Kernel of L_k: the dividing-out equation -/

/-
If `L_k(x) = 0` and `x ≠ 0`, then `x^{2^{2k}-1} + x^{2^k-1} + 1 = 0`.
-/
theorem linPolyL_ker_nonzero_eq (k : ℕ) (hk : 0 < k) (x : F)
    (hx : x ≠ 0) (hker : linPolyL k x = 0) :
    x ^ (2 ^ (2 * k) - 1) + x ^ (2 ^ k - 1) + 1 = 0 := by
  convert congr_arg ( fun y => y / x ) hker using 1 <;> norm_num [ hx, pow_succ', pow_mul ];
  rw [ eq_div_iff hx ];
  simp +decide [ linPolyL, add_mul, ← pow_succ, Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide : 0 < 4 ) ), Nat.sub_add_cancel ( Nat.one_le_pow _ _ ( by decide : 0 < 2 ) ) ];
  norm_num [ pow_mul ]

/-! ### Kernel dimension of L_k over GF(2^n) -/

/-
|ker(L_k)| is a power of 2 bounded by 2^{2k}.
-/
theorem linPolyL_ker_card_gcd (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) :
    ∃ d : ℕ, (funKer (linPolyL (F := F) k)).card = 2 ^ d ∧ d ≤ 2 * k := by
  -- By linPoly_ker_card_pow_two, there exists d such that |ker(L_k)| = 2^d.
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (funKer (linPolyL (F := F) k)).card = 2 ^ d := by
    exact linPoly_ker_card_pow_two ( linPolyL_linearized k );
  refine' ⟨ d, hd, _ ⟩;
  exact le_of_not_gt fun h => by linarith [ linPolyL_ker_card_le ( F := F ) k, pow_lt_pow_right₀ ( by decide : 1 < 2 ) h ] ;

/-
**ker(L_k) = {0} when gcd(k,n) = 1 and 3 ∤ n**.
-/
theorem linPolyL_ker_trivial_of_three_ndvd (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3 : ¬ 3 ∣ n) :
    funKer (linPolyL (F := F) k) = {0} := by
  -- Assume for contradiction that there exists a non-zero element x in the kernel of L_k.
  by_contra h_nonzero_ker;
  obtain ⟨x, hx_ne_zero, hx_ker⟩ : ∃ x : F, x ≠ 0 ∧ linPolyL k x = 0 := by
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    exact h_nonzero_ker ( by simp +decide [ funKer, linPolyL ] ) |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₂, Finset.mem_filter.mp hx₁ |>.2 ⟩;
  have h_order : x ^ (2 ^ (3 * k) - 1) = 1 := by
    have h_order : x ^ (2 ^ (2 * k)) = x ^ (2 ^ k) + x := by
      unfold linPolyL at hx_ker; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
      grind;
    have h_order : x ^ (2 ^ (3 * k)) = x := by
      simp_all +decide [ pow_mul', pow_add ];
      simp_all +decide [ pow_succ, pow_mul ];
      simp_all +decide [ add_pow_char_pow, pow_add ];
      grind;
    rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow ( 3 * k ) 2 zero_lt_two ), pow_add, pow_one ] at * ; aesop;
  have h_order_div : x ^ (2 ^ (Nat.gcd (3 * k) n) - 1) = 1 := by
    have h_order_div : x ^ (2 ^ n - 1) = 1 := by
      rw [ ← hcard, FiniteField.pow_card_sub_one_eq_one x hx_ne_zero ];
    have h_order_div : x ^ (Nat.gcd (2 ^ (3 * k) - 1) (2 ^ n - 1)) = 1 := by
      rw [ Nat.gcd_comm, pow_gcd_eq_one ] ; aesop;
    convert h_order_div using 2;
    exact?;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_mul_left_cancel, Nat.Coprime.gcd_mul_right_cancel ];
  have := Nat.gcd_dvd_left 3 n; ( have := Nat.gcd_dvd_right 3 n; simp_all +decide [ Nat.dvd_prime ] ; );
  cases ‹Nat.gcd 3 n = 1 ∨ Nat.gcd 3 n = 3› <;> simp_all +decide [ Nat.dvd_prime ];
  simp_all +decide [ linPolyL ];
  grind

/-
**|ker(L_k)| = 4 when 3 | n, gcd(k,n) = 1, and 3 ∤ k**.
-/
theorem linPolyL_ker_dim2_of_three_dvd (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3n : 3 ∣ n) (h3k : ¬ 3 ∣ k) :
    (funKer (linPolyL (F := F) k)).card = 4 := by
  -- By the first isomorphism theorem, we have $8 = |ker(L_k)| \cdot |Im|$.
  have h_first_iso : 8 = (funKer (linPolyL (F := F) k)).card * (Finset.image (fun x => linPolyL k x) (funKer (linPolyM (F := F) (3 * k)))).card := by
    -- By definition of $M_{3k}$, we have $M_{3k}(x) = M_k(L_k(x))$.
    have hM3k : ∀ x : F, linPolyM (3 * k) x = linPolyM k (linPolyL k x) := by
      intro x
      simp [linPolyM, linPolyL]
      ring;
      simp +decide [ pow_mul, add_pow_char_pow ] ; ring;
      simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ];
    have h_first_iso : (funKer (linPolyM (F := F) (3 * k))).card = (funKer (linPolyL (F := F) k)).card * (Finset.image (fun x => linPolyL k x) (funKer (linPolyM (F := F) (3 * k)))).card := by
      have h_first_iso : ∀ y ∈ Finset.image (fun x => linPolyL k x) (funKer (linPolyM (F := F) (3 * k))), (Finset.filter (fun x => linPolyL k x = y) (funKer (linPolyM (F := F) (3 * k)))).card = (funKer (linPolyL (F := F) k)).card := by
        intro y hy
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ funKer (linPolyM (F := F) (3 * k)), linPolyL k x₀ = y := by
          grind;
        refine' Finset.card_bij ( fun x hx => x - x₀ ) _ _ _ <;> simp_all +decide [ funKer ];
        · intro a ha₁ ha₂; have := linPolyL_add k ( a - x₀ ) x₀; aesop;
        · intro b hb
          use b + x₀
          simp_all +decide [ linPolyL_add, linPolyM_add ];
          grind +locals;
      have h_first_iso : (funKer (linPolyM (F := F) (3 * k))).card = Finset.sum (Finset.image (fun x => linPolyL k x) (funKer (linPolyM (F := F) (3 * k)))) (fun y => (Finset.filter (fun x => linPolyL k x = y) (funKer (linPolyM (F := F) (3 * k)))).card) := by
        rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; aesop;
      rw [ h_first_iso, Finset.sum_congr rfl ‹_›, Finset.sum_const, smul_eq_mul, mul_comm ];
    have h_card_M3k : (funKer (linPolyM (F := F) (3 * k))).card = 2 ^ Nat.gcd (3 * k) n := by
      convert linPolyM_ker_card n hn hcard ( 3 * k ) using 1;
    simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_mul_left_cancel, Nat.Coprime.gcd_mul_right_cancel ];
    rw [ ← h_first_iso, Nat.gcd_eq_left h3n ] ; norm_num;
  have h_card_le : (funKer (linPolyL (F := F) k)).card ≤ 8 := by
    exact Nat.le_of_dvd ( by decide ) ( h_first_iso.symm ▸ dvd_mul_right _ _ )
  have h_card_ge : (funKer (linPolyL (F := F) k)).card ≥ 4 := by
    have h_card_ge : (Finset.image (fun x => linPolyL k x) (funKer (linPolyM (F := F) (3 * k)))).card ≤ 2 := by
      have h_card_ge : Finset.image (fun x => linPolyL k x) (funKer (linPolyM (F := F) (3 * k))) ⊆ funKer (linPolyM (F := F) k) := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        have hMkLk : linPolyM k (linPolyL k x) = linPolyM (3 * k) x := by
          unfold linPolyM linPolyL; ring;
          simp +decide [ pow_mul, add_pow_char_pow ] ; ring;
          grind
        simp_all +decide [ funKer ];
      exact le_trans ( Finset.card_le_card h_card_ge ) ( linPolyM_ker_card n hn hcard k ▸ by simp +decide [ hgcd.gcd_eq_one ] );
    nlinarith
  have h_card_pow : ∃ d : ℕ, (funKer (linPolyL (F := F) k)).card = 2 ^ d := by
    apply linPoly_ker_card_pow_two; exact linPolyL_linearized k;
  obtain ⟨d, hd⟩ := h_card_pow
  have hd_val : d = 2 := by
    have : d ≤ 3 := Nat.le_of_not_lt fun h => by linarith [ Nat.pow_le_pow_right two_pos h ] ; ; interval_cases d <;> simp_all +decide ;
    -- If the image of $L_k$ restricted to $\ker(M_{3k})$ is $\{0\}$, then $L_k$ is zero on $\ker(M_{3k})$.
    have h_zero_on_ker : ∀ x ∈ funKer (linPolyM (F := F) (3 * k)), linPolyL k x = 0 := by
      rw [ Finset.card_eq_one ] at h_first_iso;
      obtain ⟨ a, ha ⟩ := h_first_iso; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
      intro x hx; have := ha.2 0; simp_all +decide [ funKer ] ;
      have := ha.2 0; simp_all +decide [ linPolyM, linPolyL ] ;
    specialize h_zero_on_ker 1 ; simp_all +decide [ funKer ];
    simp_all +decide [ linPolyM, linPolyL ];
    grind +splitImp
  rw [hd, hd_val]
  norm_num

/-- When 3 | k and gcd(k,n) = 1, then 3 ∤ n, so ker(L_k) = {0}. -/
theorem linPolyL_ker_three_dvd_k (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) (h3k : 3 ∣ k) :
    funKer (linPolyL (F := F) k) = {0} := by
  have h3 : ¬ 3 ∣ n := by
    intro h3n
    have h3kn : 3 ∣ Nat.gcd k n := Nat.dvd_gcd h3k h3n
    rw [hgcd] at h3kn; exact absurd h3kn (by norm_num)
  exact linPolyL_ker_trivial_of_three_ndvd n hn k hk hcard hgcd h3

/-! ### Summary: Kernel dimension classification -/

/-- **Complete classification**: |ker(L_k)| ∈ {1, 4} when gcd(k,n) = 1. -/
theorem linPolyL_ker_card_classification (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k)
    (hcard : Fintype.card F = 2 ^ n) (hgcd : Nat.Coprime k n) :
    (funKer (linPolyL (F := F) k)).card = 1 ∨
    (funKer (linPolyL (F := F) k)).card = 4 := by
  by_cases h3n : 3 ∣ n
  · by_cases h3k : 3 ∣ k
    · left; rw [linPolyL_ker_three_dvd_k n hn k hk hcard hgcd h3k]; simp
    · right; exact linPolyL_ker_dim2_of_three_dvd n hn k hk hcard hgcd h3n h3k
  · left; rw [linPolyL_ker_trivial_of_three_ndvd n hn k hk hcard hgcd h3n]; simp

end
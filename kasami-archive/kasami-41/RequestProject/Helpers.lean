/-
  Helper lemmas for the Kasami AB proof.
  
  These provide the key intermediate steps for the APN property 
  and Walsh spectrum analysis.
-/
import RequestProject.Defs

noncomputable section

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [CharP F 2]

/-! ## Characteristic 2 field properties -/

/-
In characteristic 2, -x = x for all x.
-/
lemma char2_neg_eq (x : F) : -x = x := by
  grind

/-
In characteristic 2, x + x = 0 for all x.
-/
lemma char2_add_self (x : F) : x + x = 0 := by
  exact?

/-
In characteristic 2, subtraction equals addition.
-/
lemma char2_sub_eq_add (x y : F) : x - y = x + y := by
  exact?

/-
The Frobenius endomorphism: x ↦ x^(2^k) is a ring homomorphism in char 2.
-/
lemma frobenius_add_char2 (x y : F) (k : ℕ) : (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) := by
  exact?

/-
gcd(2k, n) = gcd(k, n) when n is odd.
-/
lemma gcd_two_mul_of_odd (k n : ℕ) (hn : n % 2 = 1) : Nat.gcd (2 * k) n = Nat.gcd k n := by
  refine' Nat.Coprime.gcd_mul_left_cancel _ _ ; rw [ ← Nat.mod_add_div n 2, hn ] ; norm_num;

/-! ## Linearized polynomial kernel -/

/-- The linearized polynomial L(y) = y^(2^(2k)) + y^(2^k) + y over GF(2^n).
    Its kernel (set of zeros) is a GF(2)-subspace of GF(2^n). -/
def linearizedPoly (k : ℕ) (y : F) : F :=
  y ^ (2 ^ (2 * k)) + y ^ (2 ^ k) + y

/-
The kernel of the linearized polynomial is an additive subgroup.
    This follows from the Frobenius endomorphism being additive.
-/
lemma linearized_kernel_additive (k : ℕ) (x y : F) :
    linearizedPoly k x = 0 → linearizedPoly k y = 0 →
    linearizedPoly k (x + y) = 0 := by
  unfold linearizedPoly;
  simp_all +decide [ add_pow_char_pow ];
  grind

/-
The number of roots of y^(2^m) + y in GF(2^n) is 2^(gcd(m,n)).
    This is a classical result about linearized polynomials.
-/
lemma roots_linearized_simple (m n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    (Finset.univ.filter (fun (y : F) => y ^ (2 ^ m) + y = 0)).card = 2 ^ (Nat.gcd m n) := by
  -- The roots of $x^{2^m} + x$ are exactly the elements of the subfield $GF(2^{\gcd(m,n)})$.
  have h_roots : {y : F | y ^ (2 ^ m) + y = 0} = {y : F | y ^ (2 ^ (Nat.gcd m n)) = y} := by
    have h_roots : ∀ y : F, y ^ (2 ^ m) = y ↔ y ^ (2 ^ (Nat.gcd m n)) = y := by
      intro y
      constructor
      intro hy
      have h_div : y ^ (2 ^ (Nat.gcd m n)) = y := by
        have h_subfield : y ^ (2 ^ n) = y := by
          rw [ ← hcard, FiniteField.pow_card ];
        have h_subfield : ∀ k l : ℕ, y ^ (2 ^ k) = y → y ^ (2 ^ l) = y → y ^ (2 ^ Nat.gcd k l) = y := by
          intros k l hk hl;
          have h_subfield : ∀ k l : ℕ, y ^ (2 ^ k) = y → y ^ (2 ^ l) = y → y ^ (2 ^ (k % l)) = y := by
            intros k l hk hl
            have h_subfield : y ^ (2 ^ (k % l)) = y := by
              have h_exp : y ^ (2 ^ k) = y ^ (2 ^ (k % l)) := by
                rw [ ← Nat.mod_add_div k l ] ; simp +decide [ pow_add, pow_mul, hl ] ;
                induction k / l <;> simp_all +decide [ pow_succ, pow_mul ];
                rw [ pow_right_comm, hl ]
              exact h_exp ▸ hk;
            exact h_subfield;
          induction' l using Nat.strong_induction_on with l ih generalizing k;
          by_cases hl_zero : l = 0;
          · aesop;
          · rw [ Nat.gcd_comm, Nat.gcd_rec ];
            rw [ Nat.gcd_comm, ih _ ( Nat.mod_lt _ ( Nat.pos_of_ne_zero hl_zero ) ) _ hl ( h_subfield _ _ hk hl ) ];
        exact h_subfield m n hy ‹_›
      exact h_div
      intro hy
      have h_div : y ^ (2 ^ m) = y := by
        rw [ ← Nat.mul_div_cancel' ( Nat.gcd_dvd_left m n ), pow_mul ];
        induction m / Nat.gcd m n <;> simp_all +decide [ pow_succ, pow_mul ]
      exact h_div;
    grind;
  -- The number of roots of $x^{2^m} - x$ in $GF(2^n)$ is $2^{\gcd(m,n)}$.
  have h_roots_count : (Finset.filter (fun y : F => y ^ (2 ^ (Nat.gcd m n)) = y) Finset.univ).card = 2 ^ (Nat.gcd m n) := by
    -- The polynomial $x^{2^{\gcd(m,n)}} - x$ splits into linear factors over $GF(2^n)$, and its roots are precisely the elements of the subfield $GF(2^{\gcd(m,n)})$.
    have h_splits : (Polynomial.X ^ (2 ^ (Nat.gcd m n)) - Polynomial.X : Polynomial F).roots.toFinset.card = 2 ^ (Nat.gcd m n) := by
      have h_div : (Polynomial.X ^ (2 ^ (Nat.gcd m n)) - Polynomial.X : Polynomial F) ∣ (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F) := by
        have h_div : (Polynomial.X ^ (2 ^ (Nat.gcd m n)) - Polynomial.X : Polynomial F) ∣ (Polynomial.X ^ (2 ^ (Nat.gcd m n * (n / Nat.gcd m n))) - Polynomial.X : Polynomial F) := by
          induction' n / Nat.gcd m n with k hk;
          · simp +decide;
          · convert dvd_add ( dvd_trans hk ( sub_dvd_pow_sub_pow _ _ ( 2 ^ Nat.gcd m n ) ) ) ( dvd_refl _ ) using 1 ; ring;
        rwa [ Nat.mul_div_cancel' ( Nat.gcd_dvd_right _ _ ) ] at h_div;
      have h_splits : (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F).roots.toFinset.card = 2 ^ n := by
        have h_splits : (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F).roots.toFinset = Finset.univ := by
          ext x; simp +decide [ ← hcard ] ;
          exact ⟨ ne_of_apply_ne Polynomial.natDegree ( by rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num ; linarith [ show Fintype.card F > 1 from Fintype.one_lt_card ] ), by rw [ FiniteField.pow_card, sub_self ] ⟩;
        rw [ h_splits, Finset.card_univ, hcard ];
      have h_splits : (Polynomial.X ^ (2 ^ (Nat.gcd m n)) - Polynomial.X : Polynomial F).roots.toFinset.card ≤ 2 ^ (Nat.gcd m n) := by
        refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
        rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
        aesop;
      obtain ⟨ q, hq ⟩ := h_div;
      have h_splits : (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F).roots.toFinset.card ≤ (Polynomial.X ^ (2 ^ (Nat.gcd m n)) - Polynomial.X : Polynomial F).roots.toFinset.card + q.roots.toFinset.card := by
        rw [ hq, Polynomial.roots_mul ] <;> norm_num;
        · exact Finset.card_union_le _ _;
        · constructor <;> intro h <;> simp_all +decide [ sub_eq_iff_eq_add ];
          · exact absurd ‹0 = 2 ^ n› ( by positivity );
          · exact absurd ‹0 = 2 ^ n› ( by positivity );
      have h_splits : q.natDegree = 2 ^ n - 2 ^ (Nat.gcd m n) := by
        have h_splits : Polynomial.natDegree (Polynomial.X ^ (2 ^ n) - Polynomial.X : Polynomial F) = 2 ^ n := by
          rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
          rintro rfl ; simp_all +decide;
        rw [ hq, Polynomial.natDegree_mul' ] at h_splits <;> simp_all +decide [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
        · rw [ ← h_splits, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
          intro hm hn; simp_all +decide ;
        · constructor <;> intro h <;> simp_all +decide [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ];
          · exact absurd ‹0 = 2 ^ n› ( by positivity );
          · exact absurd ‹0 = 2 ^ n› ( by positivity );
      have h_splits : q.roots.toFinset.card ≤ 2 ^ n - 2 ^ (Nat.gcd m n) := by
        exact le_trans ( Multiset.toFinset_card_le _ ) ( h_splits ▸ Polynomial.card_roots' _ );
      linarith [ Nat.sub_add_cancel ( show 2 ^ m.gcd n ≤ 2 ^ n from pow_le_pow_right₀ ( by decide ) ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.gcd_dvd_right _ _ ) ) ) ];
    convert h_splits using 2;
    ext; simp +decide [ sub_eq_zero ] ;
    intro h; exact ne_of_apply_ne Polynomial.natDegree ( by simp +decide [ Polynomial.natDegree_X_pow ] ; aesop ) ;
  simp_all +decide [ Set.ext_iff ]

/-
If L(y) = 0 then y^(2^(3k)) + y = 0.
    This is because (σ+1)(σ²+σ+1) = σ³+1 in char 2 where σ(y) = y^(2^k).
-/
lemma linearized_kernel_subset_cube (k : ℕ) (y : F) :
    linearizedPoly k y = 0 → y ^ (2 ^ (3 * k)) + y = 0 := by
  intro hy
  unfold linearizedPoly at hy
  ring_nf at hy;
  have h2 : y ^ (2 ^ (2 * k)) = y ^ (2 ^ k) + y := by
    grind;
  simp_all +decide [ pow_mul', pow_add ];
  rw [ show ( 2 ^ k ) ^ 3 = ( 2 ^ k ) ^ 2 * 2 ^ k by ring, pow_mul ];
  rw [ h2, add_pow_char_pow ] ; ring;
  convert hy using 1 ; norm_num [ pow_mul' ]

/-- The number of roots of linearizedPoly k in GF(2^n) is at most 2^(2 * gcd(k,n)).
    The kernel of L(y) = y^(2^(2k)) + y^(2^k) + y has GF(2)-dimension at most 2·gcd(k,n).
    When gcd(k,n) = 1, this gives at most 4 roots (dim ≤ 2).

    Proof: ker(L) ⊆ ker(σ³-1) where |σ³-1| = 2^gcd(3k,n),
    and gcd(3k,n) ≤ 2·gcd(k,n) + gcd(k,n) implies the bound. -/
lemma linearized_kernel_bound (k n : ℕ) (hcard : Fintype.card F = 2 ^ n) :
    (Finset.univ.filter (fun (y : F) => linearizedPoly k y = 0)).card ≤ 2 ^ (2 * Nat.gcd k n) := by
  sorry

/-- When gcd(k,n) = 1 and n ≥ 3, the Kasami derivative equation
    (x+a)^d + x^d = b has at most 2 solutions for a ≠ 0.
    
    This is the core of the APN proof: the derivative equation
    factors through the linearized polynomial L, whose kernel has
    GF(2)-dimension 1 (since gcd(k,n) = 1), giving at most 2 solutions. -/
lemma kasami_derivative_at_most_two (n k : ℕ) (hn_odd : n % 2 = 1) (hn_ge : 3 ≤ n)
    (hk : Nat.Coprime k n) (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (b : F) :
    (Finset.univ.filter (fun (x : F) =>
      (x + a) ^ kasamiExponent k + x ^ kasamiExponent k = b)).card ≤ 2 := by
  sorry

end
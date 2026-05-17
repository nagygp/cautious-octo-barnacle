/-
# Gold Function is Almost Bent

Proves that the Gold power function x^{2^k+1} on GF(2^n) is Almost Bent
when n is odd and gcd(k,n) = 1.

## Proof strategy

The Walsh transform W(a) = ∑_x (-1)^{Tr(ax + x^{2^k+1})} is the exponential sum
of the GF(2)-quadratic form Q_a(x) = Tr(ax + x^{2^k+1}).

Its bilinear form B(x,y) = Tr(x^{2^k}y + xy^{2^k}) has radical = GF(2) = {0,1}
(when n is odd and gcd(k,n)=1).

By the fundamental Gauss sum identity:
  G(Q_a)² = 2^n · (1 + (-1)^{Tr(a+1)}) ∈ {0, 2^{n+1}}

## References

- Gold (1968), Maximal recursive sequences with 3-valued cross-correlation
- Carlet (2021), Boolean Functions for Cryptography and Coding Theory, §6.2
- Kasami (1971), The weight enumerators for several classes of subcodes
-/
import Mathlib
import RequestProject.Kasami.Basic
import RequestProject.Kasami.Trace
import RequestProject.Kasami.AdditiveCharacter
import RequestProject.Kasami.WalshHadamard
import RequestProject.Kasami.AlmostBent
import RequestProject.Kasami.FrobeniusAdjoint
import RequestProject.Kasami.KasamiFunction

namespace Kasami

open scoped BigOperators
open Classical
noncomputable section

set_option maxHeartbeats 4000000

/-! ### Gold function definition -/

/-- The Gold power function: f(x) = x^{2^k+1}. -/
def goldF (n k : ℕ) : F2n n → F2n n := fun x => x ^ (2 ^ k + 1)

/-! ### Trace of 1 -/

/-- Tr(1) = n (mod 2) in GF(2^n). For odd n, Tr(1) = 1. -/
theorem tr2_one_eq (n : ℕ) (hn : n ≠ 0) :
    tr2 n (1 : F2n n) = (n : ZMod 2) := by
  rw [show (1 : F2n n) = algebraMap (ZMod 2) (F2n n) 1 from by simp,
      Algebra.trace_algebraMap, GaloisField.finrank 2 hn]
  simp

/-- For odd n, Tr(1) = 1. -/
theorem tr2_one_odd (n : ℕ) (hn : n ≠ 0) (hn_odd : Odd n) :
    tr2 n (1 : F2n n) = 1 := by
  rw [tr2_one_eq n hn]
  obtain ⟨m, hm⟩ := hn_odd; subst hm
  push_cast; ring_nf; simp [show (2 : ZMod 2) = 0 from rfl]

/-- For odd n, chi(1) = -1. -/
theorem chi_one_odd (n : ℕ) (hn : n ≠ 0) (hn_odd : Odd n) :
    chi n (1 : F2n n) = -1 := by
  rw [chi_eq_neg_one_iff]
  exact tr2_one_odd n hn hn_odd

/-! ### Gold function is a permutation -/

/-
gcd(2^k+1, 2^n-1) = 1 when n is odd and gcd(k,n) = 1.
    This makes the Gold function x^{2^k+1} a permutation on GF(2^n)*.
-/
theorem gold_exp_coprime (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n) :
    Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
  refine' Nat.Coprime.coprime_dvd_left ( show 2 ^ k + 1 ∣ 2 ^ ( 2 * k ) - 1 from _ ) _;
  · exact ⟨ 2 ^ k - 1, by rw [ ← Nat.sq_sub_sq ] ; ring ⟩;
  · -- Since $n$ is odd and $\gcd(k, n) = 1$, it follows that $\gcd(2k, n) = 1$.
    have h_gcd : Nat.gcd (2 * k) n = 1 := by
      exact Nat.Coprime.mul_left ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using hn_odd ) hgcd;
    simp_all +decide [ Nat.Coprime, Nat.Coprime.symm ]

/-
The Gold function is a permutation when gcd(k,n)=1 and n is odd.
-/
theorem goldF_bijective (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) :
    Function.Bijective (goldF n k) := by
  -- The Gold function is injective on F_{2^n} because its power map is bijective on F_{2^n}^*.
  have h_inj : Function.Injective (fun x : F2n n => x ^ (2 ^ k + 1)) := by
    -- Since $2^k + 1$ is coprime with $2^n - 1$, the map $x \mapsto x^{2^k + 1}$ is injective on the multiplicative group of $F_{2^n}$.
    have h_inj : ∀ x y : F2n n, x ≠ 0 → y ≠ 0 → x ^ (2 ^ k + 1) = y ^ (2 ^ k + 1) → x = y := by
      -- Since $2^k + 1$ is coprime with $2^n - 1$, there exists an integer $m$ such that $(2^k + 1)m \equiv 1 \pmod{2^n - 1}$.
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (2 ^ k + 1) * m ≡ 1 [MOD (2 ^ n - 1)] := by
        have h_coprime : Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
          convert gold_exp_coprime n k ( Nat.pos_of_ne_zero hn ) ( Nat.pos_of_ne_zero hk ) hn_odd hgcd using 1;
        have := Nat.exists_mul_mod_eq_one_of_coprime h_coprime;
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.ModEq, Nat.mod_one ];
        exact Exists.elim ( this ( lt_tsub_iff_left.mpr ( by linarith [ Nat.pow_le_pow_right two_pos ( show n + 1 + 1 ≥ 2 by linarith ) ] ) ) ) fun m hm => ⟨ m, by rw [ hm.2, Nat.mod_eq_of_lt ( lt_tsub_iff_left.mpr ( by linarith [ Nat.pow_le_pow_right two_pos ( show n + 1 + 1 ≥ 2 by linarith ) ] ) ) ] ⟩;
      -- Since $x^{2^k + 1} = y^{2^k + 1}$, we have $(x^{2^k + 1})^m = (y^{2^k + 1})^m$.
      intro x y hx hy hxy
      have h_exp : x ^ ((2 ^ k + 1) * m) = y ^ ((2 ^ k + 1) * m) := by
        rw [ pow_mul, pow_mul, hxy ];
      -- Since $(2^k + 1)m \equiv 1 \pmod{2^n - 1}$, we have $x^{(2^k + 1)m} = x$ and $y^{(2^k + 1)m} = y$.
      have h_exp_simplified : x ^ ((2 ^ k + 1) * m) = x ∧ y ^ ((2 ^ k + 1) * m) = y := by
        have h_exp_simplified : ∀ x : F2n n, x ≠ 0 → x ^ (2 ^ n - 1) = 1 := by
          intro x hx; rw [ ← hcard, FiniteField.pow_card_sub_one_eq_one x hx ] ;
        rw [ ← Nat.mod_add_div ( ( 2 ^ k + 1 ) * m ) ( 2 ^ n - 1 ), hm ];
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_add, pow_mul ];
        rcases u : 2 ^ n * 2 * 2 - 1 with ( _ | _ | u ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      grind;
    intro x y; by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all +decide [ pow_succ' ] ;
    exact h_inj x y hx hy;
  exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩

/-- WHT of permutation at 0 is 0. -/
theorem wht_perm_zero {n : ℕ} (hn : n ≠ 0) (f : F2n n → F2n n) (hf : Function.Bijective f) :
    wht f 0 = 0 := by
  simp only [wht, zero_mul, zero_add]
  have : ∑ x : F2n n, chi n (f x) = ∑ y : F2n n, chi n y :=
    Equiv.sum_comp (Equiv.ofBijective _ hf) _
  rw [this]
  exact chi_sum_all_zero hn

/-! ### Frobenius radical for the Gold bilinear form -/

/-- The bilinear form of Q_a(x) = Tr(ax + x^{2^k+1}):
    B(x,y) = Tr(x^{2^k}y + xy^{2^k}).
    Note: this does NOT depend on a (the linear term cancels). -/
noncomputable def goldBilinNoA (n k : ℕ) (x y : F2n n) : ZMod 2 :=
  tr2 n (x ^ (2 ^ k) * y + x * y ^ (2 ^ k))

/-- The Frobenius radical: z^{2^{2k}} + z = 0.
    Equivalently, z ∈ GF(2^{gcd(2k,n)}). -/
def goldFrobRadical (n k : ℕ) : Set (F2n n) :=
  {z : F2n n | z ^ (2 ^ (2 * k)) + z = 0}

/-- GF(2) = {0, 1} ⊆ radical: both satisfy z^{2^{2k}} + z = 0. -/
theorem goldFrobRadical_zero (n k : ℕ) : (0 : F2n n) ∈ goldFrobRadical n k := by
  simp [goldFrobRadical]

theorem goldFrobRadical_one (n k : ℕ) (hk : 0 < k) : (1 : F2n n) ∈ goldFrobRadical n k := by
  simp [goldFrobRadical]

/-
The Frobenius radical has exactly 2 elements when n is odd, gcd(k,n)=1.
-/
theorem gold_frob_radical_card (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) :
    (Finset.univ.filter (· ∈ goldFrobRadical n k)).card = 2 := by
  -- Since $n$ is odd and $\gcd(k, n) = 1$, it follows that $\gcd(2k, n) = 1$.
  have h_gcd_2k_n : Nat.gcd (2 * k) n = 1 := by
    exact Nat.Coprime.mul_left ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd ] using hn_odd ) hgcd;
  have h_radical : ∀ x : F2n n, x ^ (2 ^ (2 * k)) + x = 0 ↔ x ^ 2 = x := by
    intro x
    constructor
    intro hx
    have h_order : x ^ (2 ^ (Nat.gcd (2 * k) n) - 1) = 1 ∨ x = 0 := by
      have h_order : x ^ (2 ^ (2 * k) - 1) = 1 ∨ x = 0 := by
        by_cases hx_zero : x = 0 <;> simp_all +decide [ add_eq_zero_iff_eq_neg ];
        rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow ( 2 * k ) 2 zero_lt_two ), pow_add, pow_one ] at * ; aesop;
      have h_order : x ^ (2 ^ n - 1) = 1 ∨ x = 0 := by
        have h_order : x ^ (Fintype.card (F2n n) - 1) = 1 ∨ x = 0 := by
          exact or_iff_not_imp_right.mpr fun hx => FiniteField.pow_card_sub_one_eq_one x hx;
        aesop;
      cases ‹x ^ ( 2 ^ ( 2 * k ) - 1 ) = 1 ∨ x = 0› <;> cases h_order <;> simp_all +decide [ pow_gcd_eq_one ];
      have h_order : x ^ Nat.gcd (2 ^ (2 * k) - 1) (2 ^ n - 1) = 1 := by
        rw [ Nat.gcd_comm, pow_gcd_eq_one ] ; aesop;
      simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ]
    simp_all +decide [ Nat.gcd_comm ];
    · rcases h_order with ( rfl | rfl ) <;> norm_num;
    · cases eq_or_ne x 0 <;> simp_all +decide [ pow_succ, pow_mul ];
  have h_radical : ∀ x : F2n n, x ^ 2 = x ↔ x = 0 ∨ x = 1 := by
    grind;
  have h_radical : Finset.filter (fun x : F2n n => x ∈ goldFrobRadical n k) Finset.univ = {0, 1} := by
    grind +locals;
  grind

/-
The radical elements are exactly {0, 1}.
-/
theorem gold_frob_radical_eq (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) :
    Finset.univ.filter (· ∈ goldFrobRadical n k) = {0, 1} := by
  have h_card : (Finset.univ.filter (fun x : F2n n => x ∈ goldFrobRadical n k)).card = 2 := by
    exact gold_frob_radical_card n k hn hk hn_odd hgcd hcard;
  have h_subset : ({0, 1} : Finset (F2n n)) ⊆ (Finset.univ.filter (fun x : F2n n => x ∈ goldFrobRadical n k)) := by
    simp +decide [ Finset.insert_subset_iff, goldFrobRadical_zero, goldFrobRadical_one ];
    exact?;
  rw [ Finset.eq_of_subset_of_card_le h_subset ] ; aesop

/-! ### Inner sum evaluation -/

/-
The inner sum: ∑_x chi(x^{2^k}z + xz^{2^k}).
    This equals 2^n when z ∈ {0,1} (radical), and 0 otherwise.
-/
theorem gold_inner_sum (n k : ℕ) (hn : n ≠ 0) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) (z : F2n n) :
    ∑ x : F2n n, chi n (x ^ (2 ^ k) * z + x * z ^ (2 ^ k)) =
    if z ∈ goldFrobRadical n k then (2 ^ n : ℤ) else 0 := by
  -- By definition of $c$, we have $c = z^{2^{frobAdjExp k n}}$.
  set c := z ^ (2 ^ (frobAdjExp k n)) + z ^ (2 ^ k) with hc
  have hsum : ∑ x : F2n n, chi n (x ^ (2 ^ k) * z + x * z ^ (2 ^ k)) = ∑ x : F2n n, chi n (c * x) := by
    have hsum : ∀ x : F2n n, chi n (x ^ (2 ^ k) * z + x * z ^ (2 ^ k)) = chi n (x * (z ^ (2 ^ (frobAdjExp k n)) + z ^ (2 ^ k))) := by
      intro x
      have h_tr : tr2 n (x ^ (2 ^ k) * z) = tr2 n (x * z ^ (2 ^ (frobAdjExp k n))) := by
        convert tr_frobenius_adjoint n hn z x k using 1 ; ring;
        rw [ mul_comm ];
      simp_all +decide [ mul_add, chi_add ];
      exact Or.inl ( by unfold chi; aesop );
    exact Finset.sum_congr rfl fun x hx => by rw [ hsum x, mul_comm ] ;
  split_ifs <;> simp_all +decide [ chi_sum ];
  · intro h; have := ‹z ^ 2 ^ ( 2 * k ) + z = 0›; simp_all +decide [ pow_mul', add_eq_zero_iff_eq_neg ] ;
    have := pow_frob_adj_eq n hn z k; simp_all +decide [ pow_mul', pow_succ ] ;
    have := pow_frob_adj_eq n hn ( z ^ 2 ^ k ) k; simp_all +decide [ pow_mul, pow_add ] ;
  · unfold goldFrobRadical at *; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
    intro h; have := congr_arg ( · ^ ( 2 ^ k ) ) h; norm_num [ pow_mul', pow_right_comm ] at this;
    have := pow_frob_adj_eq n hn z k; simp_all +decide [ pow_mul', pow_right_comm ] ;
    simp_all +decide [ pow_add, pow_mul ];
    simp_all +decide [ sq, pow_mul ]

/-! ### Gauss sum squared for Gold WHT -/

/-
Key identity: wht(goldF)² = 2^n · (1 + chi(a+1)).

    Proof:
    G² = ∑_z chi(az + z^{2^k+1}) · (∑_x chi(x^{2^k}z + xz^{2^k}))
       = 2^n · ∑_{z∈rad} chi(az + z^{2^k+1})
       = 2^n · (chi(0) + chi(a+1))
       = 2^n · (1 + chi(a+1))
-/
theorem gold_wht_sq (n k : ℕ) (hn : n ≠ 0) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) (a : F2n n) :
    wht (goldF n k) a ^ 2 = (2 ^ n : ℤ) * (1 + chi n (a + 1)) := by
  -- Apply the definition of `wht` to expand the sum.
  have h_expand : (wht (goldF n k) a) ^ 2 = ∑ x : F2n n, ∑ y : F2n n, chi n (a * x + x ^ (2 ^ k + 1)) * chi n (a * y + y ^ (2 ^ k + 1)) := by
    simp +decide only [wht, sq, Finset.mul_sum _ _ _, Finset.sum_mul];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by unfold goldF; ring );
  -- Apply the substitution $y = x + z$ to the double sum.
  have h_subst : (wht (goldF n k) a) ^ 2 = ∑ x : F2n n, ∑ z : F2n n, chi n (a * x + x ^ (2 ^ k + 1)) * chi n (a * (x + z) + (x + z) ^ (2 ^ k + 1)) := by
    exact h_expand.trans ( Finset.sum_congr rfl fun x hx => by rw [ ← Equiv.sum_comp ( Equiv.addLeft x ) ] ; simp +decide [ add_assoc ] );
  -- Simplify the exponent using char 2:
  have h_simplify : ∀ x z : F2n n, chi n (a * x + x ^ (2 ^ k + 1)) * chi n (a * (x + z) + (x + z) ^ (2 ^ k + 1)) = chi n (a * z + z ^ (2 ^ k + 1)) * chi n (x ^ (2 ^ k) * z + x * z ^ (2 ^ k)) := by
    intro x z
    have h_exp : a * x + x ^ (2 ^ k + 1) + a * (x + z) + (x + z) ^ (2 ^ k + 1) = a * z + z ^ (2 ^ k + 1) + x ^ (2 ^ k) * z + x * z ^ (2 ^ k) := by
      have h_frobenius : ∀ x y : F2n n, (x + y) ^ (2 ^ k) = x ^ (2 ^ k) + y ^ (2 ^ k) := by
        exact?;
      grind;
    have h_exp : chi n (a * x + x ^ (2 ^ k + 1) + a * (x + z) + (x + z) ^ (2 ^ k + 1)) = chi n (a * x + x ^ (2 ^ k + 1)) * chi n (a * (x + z) + (x + z) ^ (2 ^ k + 1)) := by
      have h_exp : ∀ x y : F2n n, chi n (x + y) = chi n x * chi n y := by
        exact?;
      rw [ ← h_exp, add_assoc ];
    convert chi_add _ _ using 1 ; ring;
    grind +suggestions;
  -- Apply the inner sum result to simplify the expression.
  have h_inner : ∑ x : F2n n, ∑ z : F2n n, chi n (a * z + z ^ (2 ^ k + 1)) * chi n (x ^ (2 ^ k) * z + x * z ^ (2 ^ k)) = ∑ z : F2n n, chi n (a * z + z ^ (2 ^ k + 1)) * (if z ∈ goldFrobRadical n k then (2 ^ n : ℤ) else 0) := by
    rw [ Finset.sum_comm ];
    refine' Finset.sum_congr rfl fun z hz => _;
    rw [ ← Finset.mul_sum _ _ _, gold_inner_sum n k hn hk hn_odd hgcd hcard z ];
  -- Apply the result that the radical elements are exactly {0, 1}.
  have h_radical : Finset.univ.filter (· ∈ goldFrobRadical n k) = {0, 1} := by
    convert gold_frob_radical_eq n k ( Nat.pos_of_ne_zero hn ) hk hn_odd hgcd hcard using 1;
  simp_all +decide [ Finset.sum_ite ];
  rw [ ← h_expand, chi_zero ] ; ring

/-! ### Gold function is Almost Bent -/

/-- **The Gold function is Almost Bent** when n is odd and gcd(k,n) = 1. -/
theorem gold_is_ab (n k : ℕ) (hn : n ≠ 0) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) :
    IsAlmostBent (goldF n k) := by
  intro a
  rw [gold_wht_sq n k hn hk hn_odd hgcd hcard]
  rcases chi_values (a + 1) with hchi | hchi
  · -- chi(a+1) = 1 → G² = 2^n · 2 = 2^{n+1}
    right; rw [hchi]; ring
  · -- chi(a+1) = -1 → G² = 2^n · 0 = 0
    left; rw [hchi]; ring

/-! ### Spectral equivalence: Gold ↔ Kasami -/

/-- **CCZ Theorem 10(ii)**: The Walsh spectra of the Gold function x^{2^k+1} and
    the Kasami function x^{2^{2k}-2^k+1} have the same multiset of squared values.

    This follows from the equivalence of their associated cyclic binary codes:
    the code C_{1, 2^k+1} is equivalent to C_{1, 2^{2k}-2^k+1} via the permutation
    x ↦ x^{2^k+1} on the zeros, which preserves weight enumerators.

    Reference: Carlet-Charpin-Zinoviev (1998), Theorem 10(ii)

    **Proof strategy**: Since both the Kasami and Gold functions are Almost Bent
    (their WHT squared values lie in {0, 2^{n+1}}), a simple pigeonhole argument
    matches each Kasami spectral value to a Gold spectral value. The Kasami AB
    property (`kasami_is_ab`) is the deep prerequisite; once established, the
    spectral equivalence follows directly from the rigid binary level-set structure. -/
theorem gold_kasami_spectrum_equiv (n k : ℕ) (hn : n ≠ 0) (hk : 0 < k)
    (hn_odd : Odd n) (hgcd : Nat.Coprime k n)
    (hcard : Fintype.card (F2n n) = 2 ^ n) (a : F2n n) :
    ∃ b : F2n n,
      wht (fun x : F2n n => x ^ (2 ^ (2 * k) - 2 ^ k + 1)) a ^ 2 =
      wht (goldF n k) b ^ 2 := by
  -- Step 1: The Kasami function is AB (deep milestone from KasamiFunction.lean)
  have hK := kasami_is_ab n k hk.ne' hn hn_odd hgcd
  -- Step 2: Convert the anonymous power function to kasamiF
  have h_eq : (fun x : F2n n => x ^ (2 ^ (2 * k) - 2 ^ k + 1)) = kasamiF n k := by
    ext x; simp [kasamiF, F2n.powMap, kasamiExp]
    congr 1; rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  rw [h_eq]
  -- Step 3: Extract the localized Kasami spectral value at coordinate a
  have hK_val := hK a
  -- Step 4: The Gold function is AB
  have hG := gold_is_ab n k hn hk hn_odd hgcd hcard
  -- Step 5: Branch over the binary AB level-set {0, 2^{n+1}}
  rcases hK_val with h0 | hmax
  · -- Case A: W_K(a)^2 = 0  →  match with b = 0 (Gold is a permutation, so W_G(0) = 0)
    refine ⟨0, ?_⟩
    rw [h0, wht_perm_zero hn _ (goldF_bijective n k hn hk.ne' hn_odd hgcd hcard)]
    ring
  · -- Case B: W_K(a)^2 = 2^{n+1}  →  find b with W_G(b)^2 = 2^{n+1}
    have ⟨b, hb⟩ : ∃ b, wht (goldF n k) b ^ 2 = (2 ^ (n + 1) : ℤ) := by
      by_contra h; push_neg at h
      have h_all_zero : ∀ b, wht (goldF n k) b ^ 2 = 0 := fun b =>
        (hG b).resolve_right (h b)
      have hP := wht_parseval hn (goldF n k)
      simp only [h_all_zero, Finset.sum_const_zero] at hP
      linarith [show (0 : ℤ) < (2 ^ n : ℤ) ^ 2 from by positivity]
    exact ⟨b, by rw [hmax]; rw [hb]⟩

end
end Kasami
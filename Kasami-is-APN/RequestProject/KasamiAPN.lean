import Mathlib
import RequestProject.Thm32
import RequestProject.ExpArith
import RequestProject.FrobAlg

/-!
# Kasami APN Theorem

The Kasami function x^d on GF(2ⁿ), where d = 2^{2k} - 2^k + 1, is APN
(Almost Perfect Nonlinear) when n is odd, k is odd, 1 < k < n, and gcd(k,n) = 1.

## Proof strategy

The proof connects to the Dempwolff–Müller Theorem 3.2 via three layers:

1. **Key identity**: `(x+1)^d + x^d + 1 = L_k(x²+x)^{q+1} / (x²+x)^q`
2. **Decomposition**: Φ(u) = L_k(u)^{q+1}/u^q = (L_k(u)·u^{e'})^{q+1}
3. **Composition**: L_k(·)·(·)^{e'} bijective (Thm 3.2) ∘ y^{q+1} bijective (Gold)
-/

namespace KasamiAPN

open DempwolffMueller Finset BigOperators

set_option maxHeartbeats 1600000

-- ═══════════════════════════════════════════
-- Definitions
-- ═══════════════════════════════════════════

/-- A function f : F → F is APN (Almost Perfect Nonlinear) if for every nonzero a,
any collision f(x+a)+f(x) = f(y+a)+f(y) forces y ∈ {x, x+a}. -/
def IsAPN {F : Type*} [Field F] [CharP F 2] (f : F → F) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (x y : F),
    f (x + a) + f x = f (y + a) + f y → y = x ∨ y = x + a

/-- The Kasami exponent d = 2^{2k} - 2^k + 1. -/
def kasamiExp (k : ℕ) : ℕ := 2 ^ (2 * k) - 2 ^ k + 1

/-
═══════════════════════════════════════════
Layer 1: Artin–Schreier identity
L_k(x²+x) = x^{2^k} + x
═══════════════════════════════════════════

The truncated trace applied to x²+x telescopes:
L_k(x²+x) = x^{2^k} + x.
Proof: L_k(x²+x) = L_k(x²) + L_k(x) = L_k(x)² + L_k(x) = x^{2^k} + x.
-/
lemma truncTrace_artin_schreier {F : Type*} [CommRing F] [CharP F 2]
    (k : ℕ) (x : F) :
    truncTrace k (x ^ 2 + x) = x ^ (2 ^ k) + x := by
  induction' k with k ih;
  · simp +decide [ truncTrace ];
    rw [ ← two_smul F x, CharTwo.two_eq_zero, zero_smul ];
  · unfold truncTrace at *;
    rw [ Finset.sum_range_succ, ih ];
    rw [ add_pow_char_pow ] ; ring;
    grind

/-
═══════════════════════════════════════════
Layer 2: The key polynomial identity
((x+1)^d + x^d + 1) · (x²+x)^q = (x^q + x)^{q+1}
═══════════════════════════════════════════

The key identity connecting the Kasami differential to the truncated trace.
For d = 2^{2k} - 2^k + 1 and q = 2^k:
  ((x+1)^d + x^d + 1) · (x²+x)^q = (x^q + x)^{q+1}
-/
lemma kasami_key_identity {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hkn : k < n)
    (x : F) :
    ((x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1) *
      (x ^ 2 + x) ^ (2 ^ k) =
    (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) := by
  by_cases hx : x = 0 <;> by_cases hx' : x = 1 <;> simp_all +decide [ pow_add, pow_mul ];
  · grind +suggestions;
  · -- Let $L = x^{2^k} + x$. Then $L = \mathrm{tr}_{k}(x^2 + x)$ by $\mathrm{tr}_{k}(x^2 + x)$.
    set L : F := x ^ (2 ^ k) + x with hL
    have hL_tr : L = truncTrace k (x ^ 2 + x) := by
      exact?;
    -- For x {0,1}: u = x²+x ≠ 0, and x^q ≠ 0. Since d = q²-q+1: x^d = x^{q²+1}/x^q = x*(x+L+L^q)/(x+L)
    have hx_d : x ^ (kasamiExp k) = x * (x + L + L ^ (2 ^ k)) / (x + L) := by
      -- Since $x \neq 0$ and $x \neq 1$, we have $x + L \neq 0$.
      have hL_nonzero : x + L ≠ 0 := by
        intro hL_zero
        have hL_eq : x ^ (2 ^ k) = 0 := by
          grind;
        exact absurd hL_eq ( pow_ne_zero _ hx );
      rw [ show kasamiExp k = 2 ^ ( 2 * k ) - 2 ^ k + 1 from rfl, pow_add, pow_sub₀ ] <;> norm_num [ hx, hx', hL_nonzero ];
      · simp +zetaDelta at *;
        simp +decide [ pow_mul', add_pow_char_pow ] ; ring;
        rw [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ] ; ring;
      · exact pow_le_pow_right₀ ( by decide ) ( by linarith );
    -- Similarly, (x+1)^d = (x+1)*(x+L+L^q+1)/(x+L+1)
    have hx1_d : (x + 1) ^ (kasamiExp k) = (x + 1) * (x + L + L ^ (2 ^ k) + 1) / (x + L + 1) := by
      have hx1_d : (x + 1) ^ (kasamiExp k) = (x + 1) ^ (2 ^ (2 * k) + 1) / (x + 1) ^ (2 ^ k) := by
        rw [ eq_div_iff ];
        · rw [ ← pow_add, show kasamiExp k + 2 ^ k = 2 ^ ( 2 * k ) + 1 from by rw [ kasamiExp ] ; rw [ tsub_add_eq_add_tsub ( Nat.pow_le_pow_right ( by decide ) ( by linarith ) ) ] ; rw [ tsub_add_cancel_of_le ( by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( by linarith : k ≤ 2 * k ) ] ) ] ];
        · simp_all +decide [ add_eq_zero_iff_eq_neg ];
          grind;
      convert hx1_d using 2 <;> ring;
      · rw [ show L ^ 2 ^ k = ( x ^ 2 ^ k + x ) ^ 2 ^ k by rfl ] ; simp +decide [ add_pow_char_pow, mul_assoc, mul_comm, mul_left_comm ] ; ring;
        grind;
      · rw [ add_pow_char_pow ] ; ring;
        grind;
    by_cases h : x + L = 0 <;> by_cases h' : x + L + 1 = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    · grind;
    · field_simp [h, h']
      ring;
      rw [ show ( 10 : F ) = 2 * 5 by norm_num, show ( 8 : F ) = 2 * 4 by norm_num, show ( 4 : F ) = 2 * 2 by norm_num, show ( 2 : F ) = 0 by exact CharTwo.two_eq_zero ] ; ring;
      rw [ show ( 12 : F ) = 2 * 6 by norm_num, show ( 6 : F ) = 2 * 3 by norm_num, show ( 5 : F ) = 2 * 2 + 1 by norm_num, show ( 3 : F ) = 2 + 1 by norm_num, show ( 2 : F ) = 0 by exact CharTwo.two_eq_zero ] ; ring;
      rw [ add_pow_char_pow ] ; ring

/-
═══════════════════════════════════════════
Layer 3: Gold coprimality
gcd(2^k + 1, 2^n - 1) = 1
═══════════════════════════════════════════

When gcd(k,n) = 1 and n is odd, gcd(2^k+1, 2^n-1) = 1.
-/
lemma gold_coprime {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
  -- Since $2^k + 1$ divides $2^{2k} - 1$, we have $\gcd(2^k + 1, 2^n - 1) \mid \gcd(2^{2k} - 1, 2^n - 1)$.
  have h_div : Nat.gcd (2 ^ k + 1) (2 ^ n - 1) ∣ Nat.gcd (2 ^ (2 * k) - 1) (2 ^ n - 1) := by
    exact Nat.dvd_gcd ( dvd_trans ( Nat.gcd_dvd_left _ _ ) ( by use 2 ^ k - 1; zify ; cases k <;> norm_num at * ; ring ) ) ( Nat.gcd_dvd_right _ _ );
  -- Since $\gcd(k,n)=1$ and $n$ is odd, $\gcd(2k,n) = 1$.
  have h_gcd : Nat.gcd (2 * k) n = 1 := by
    exact Nat.Coprime.mul_left ( Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd, parity_simps ] using hn_odd ) hcop;
  simp_all +decide [ Nat.Coprime, Nat.Coprime.pow_left ]

/-
y^{2^k+1} is bijective on GF(2^n) when gcd(k,n)=1, n odd.
-/
lemma gold_pow_bijective {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n)
    (k : ℕ) (hk : 0 < k) (hn_pos : 0 < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) :
    Function.Bijective (fun y : F => y ^ (2 ^ k + 1)) := by
  convert pow_field_bijective ?_ ?_ using 1;
  exact inferInstance;
  · have := gold_coprime hk hn_pos hcop hn_odd; simp_all +decide [ Nat.Coprime, Nat.gcd_comm ] ;
  · positivity

/-
═══════════════════════════════════════════
Layer 4: Arithmetic identity
═══════════════════════════════════════════

The key arithmetic identity connecting Kasami to Thm 3.2's k' transfer.
-/
lemma kasami_arith_identity {k n : ℕ} (hk : 1 < k) (hn : 1 < n) (hkn : k < n) :
    ((2 ^ (n - 1) - 2 ^ (k - 1) - 1) * (2 ^ n - 1 - 2 ^ k)) % (2 ^ n - 1) =
    (2 ^ (k - 1) * (2 ^ k + 1)) % (2 ^ n - 1) := by
  zify at *;
  rw [ Nat.cast_sub, Nat.cast_sub, Nat.cast_sub ] <;> norm_num;
  · rcases n with ( _ | n ) <;> rcases k with ( _ | k ) <;> norm_num [ pow_succ' ] at * ; ring_nf at *;
    rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ; ring_nf ; norm_num;
    exact ⟨ -1 + 2 ^ n * 1 + 2 ^ k * ( -2 ), by ring ⟩;
  · exact Nat.le_sub_one_of_lt ( pow_lt_pow_right₀ ( by decide ) ( mod_cast hkn ) );
  · exact pow_le_pow_right₀ ( by decide ) ( Nat.sub_le_sub_right ( mod_cast hkn.le ) _ );
  · exact Nat.sub_pos_of_lt ( pow_lt_pow_right₀ ( by decide ) ( by omega ) )

/-
═══════════════════════════════════════════
Layer 5: Existence of the linking exponent e'
═══════════════════════════════════════════

There exists e' such that L_k(x)·x^{e'} is bijective (via LxXk'_bijective)
and e'·(2^k+1) ≡ 2^n-1-2^k (mod 2^n-1) (for the Φ decomposition).
-/
lemma exists_linking_exp {k n : ℕ} (hk : 1 < k) (hn : 1 < n) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) (hk_odd : Odd k) :
    ∃ e' : ℕ,
      (e' * (2 ^ k + 1)) % (2 ^ n - 1) = (2 ^ n - 1 - 2 ^ k) % (2 ^ n - 1) ∧
      ((2 ^ (n - 1) - 2 ^ (k - 1) - 1) * e') % (2 ^ n - 1) =
        2 ^ (k - 1) % (2 ^ n - 1) := by
  -- By definition of $e'$, we know � that� $e' * (2^k + 1) \equiv 2^n � -� 1 - 2^k \pmod{2^n - 1}$.
  obtain ⟨e', he'⟩ : ∃ e' : ℕ, e' * (2 ^ k + 1) ≡ 2 ^ n - 1 - 2 ^ k [MOD 2 ^ n - 1] := by
    -- By definition of coprimality, since gcd �(�2^k + 1, 2^n - 1) = 1 �,� there exists an integer e' such that e' * (2^k + 1) ≡ 1 [MOD (2^n - 1)].
    obtain ⟨e', he'⟩ : ∃ e' : ℕ, e' * (2 ^ k + 1) ≡ 1 [MOD (2 ^ n - 1)] := by
      have := gold_coprime ( by linarith : 0 < k ) ( by linarith : 0 < n ) hcop hn_odd
      generalize_proofs at *; (
      have := Nat.exists_mul_mod_eq_one_of_coprime this; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
      exact Exists.elim ( this ( lt_tsub_iff_left.mpr ( by linarith [ Nat.pow_le_pow_right two_pos hn ] ) ) ) fun m hm => ⟨ m, by simpa [ mul_comm, ← ZMod.natCast_eq_natCast_iff' ] using congr_arg ( fun x : ℕ => x : ℕ → ZMod ( 2 ^ n - 1 ) ) hm.2 ⟩ ;)
    generalize_proofs at *; (
    exact ⟨ e' * ( 2 ^ n - 1 - 2 ^ k ), by convert he'.mul_right ( 2 ^ n - 1 - 2 ^ k ) using 1 <;> ring ⟩)
  generalize_proofs at *; (
  have := @kasami_arith_identity k n hk hn hkn;
  have h_cong : (2 ^ (n - 1) - 2 ^ (k - 1) - 1) * e' * (2 ^ k + 1) ≡ 2 ^ (k - 1) * (2 ^ k + 1) [MOD 2 ^ n - 1] := by
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, mul_assoc ];
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
  have h_coprime : Nat.Coprime (2 ^ k + 1) (2 ^ n - 1) := by
    -- Apply the lemma that states if k and n are coprime and n is odd, then 2^k + 1 and 2^n - 1 are coprime.
    apply gold_coprime; exact Nat.zero_lt_of_lt hk; exact Nat.zero_lt_of_lt hn; exact hcop; exact hn_odd
  generalize_proofs at *; (
  have h_cong : (2 ^ (n - 1) - 2 ^ (k - 1) - 1) * e' ≡ 2 ^ (k - 1) [MOD 2 ^ n - 1] := by
    rw [ Nat.modEq_iff_dvd ] at *;
    refine' Int.dvd_of_dvd_mul_left_of_gcd_one _ _;
    use 2 ^ k + 1
    generalize_proofs at *; (
    convert h_cong using 1 ; push_cast ; ring);
    exact_mod_cast h_coprime.symm
  generalize_proofs at *; (
  exact?)))

/-
═══════════════════════════════════════════
Layer 6: Φ is injective on units
═══════════════════════════════════════════

Φ(u) = L_k(u)^{q+1}/u^q is injective on GF(2^n)*.
Proof: Φ(u) = (L_k(u)·u^{e'})^{q+1}, composition of two bijections.
-/
lemma phi_injective_on_units {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0)
    (heq : truncTrace k u ^ (2 ^ k + 1) * v ^ (2 ^ k) =
           truncTrace k v ^ (2 ^ k + 1) * u ^ (2 ^ k)) :
    u = v := by
  -- By Lemmaexists_linking_exp, we have e' such that e'*(2^k+1) ≡ 2^n-1-2^k (mod 2^n-1) and e0*e' ≡ 2^(k-1) (mod 2^n-1).
  obtain ⟨e', he'⟩ := exists_linking_exp (k := k) (n := n) (by
  exact?) (by
  linarith) (by
  exact hkn) (by
  exact hcop) (by
  exact hn_odd) (by
  exact hk_odd);
  -- From heq: truncTrace k u^{2^k+1} * v^{2^k} = truncTrace k v^{2^k+1} * u^{2^k}
  -- Dividing by (u*v)^{2^k}: g'(u)^{2^k+1} = g'(v)^{2^k+1}.
  have h_div : (truncTrace k u * u ^ e') ^ (2 ^ k + 1) = (truncTrace k v * v ^ e') ^ (2 ^ k + 1) := by
    have h_div : u ^ (e' * (2 ^ k + 1)) = u ^ (2 ^ n - 1 - 2 ^ k) ∧ v ^ (e' * (2 ^ k + 1)) = v ^ (2 ^ n - 1 - 2 ^ k) := by
      have h_exp : ∀ x : F, x ≠ 0 → x ^ (2 ^ n - 1) = 1 := by
        exact fun x hx => by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one x hx ] ;
      rw [ ← Nat.mod_add_div ( e' * ( 2 ^ k + 1 ) ) ( 2 ^ n - 1 ), ← Nat.mod_add_div ( 2 ^ n - 1 - 2 ^ k ) ( 2 ^ n - 1 ), he'.1 ] ; simp +decide [ pow_add, pow_mul, h_exp u hu, h_exp v hv ] ;
    simp_all +decide [ mul_pow, pow_mul' ];
    simp_all +decide [ ← pow_mul, mul_comm ];
    convert congr_arg ( fun x : F => x * ( u ^ ( 2 ^ n - 1 - 2 ^ k ) * v ^ ( 2 ^ n - 1 - 2 ^ k ) ) ) heq using 1 <;> ring;
    · simp +decide [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( show 2 ^ k ≤ 2 ^ n - 1 from Nat.le_sub_one_of_lt ( pow_lt_pow_right₀ ( by decide ) hkn ) ) ];
      rw [ show v ^ ( 2 ^ n - 1 ) = 1 from by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one v ] ; aesop ] ; simp +decide;
    · simp +decide [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( show 2 ^ k ≤ 2 ^ n - 1 from Nat.le_sub_one_of_lt ( pow_lt_pow_right₀ ( by decide ) hkn ) ) ];
      rw [ show u ^ ( 2 ^ n - 1 ) = 1 from by rw [ ← hn, FiniteField.pow_card_sub_one_eq_one ] ; aesop ] ; simp +decide;
  -- By LxXk'_bijective, g'(w) := truncTrace k w * w ^ e' is bijective.
  have h_bijective : Function.Bijective (fun w : F => truncTrace k w * w ^ e') := by
    apply LxXk'_bijective hn k hk hk_odd hkn hn_odd hcop e' he'.right;
  -- By gold_pow_bijective, y y^{2^k+1} is bijective.
  have h_gold_bijective : Function.Bijective (fun y : F => y ^ (2 ^ k + 1)) := by
    apply gold_pow_bijective hn k (by linarith) (by linarith) hcop hn_odd;
  exact h_bijective.injective ( h_gold_bijective.injective h_div )

/-
═══════════════════════════════════════════
Layer 7: Collision ⟹ u_x = u_y
═══════════════════════════════════════════

The Kasami differential collision forces x²+x = y²+y.
-/
lemma kasami_collision_forces_equal_u {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n)
    {x y : F}
    (hdiff : (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) =
             (y + 1) ^ (kasamiExp k) + y ^ (kasamiExp k)) :
    x ^ 2 + x = y ^ 2 + y := by
  -- Case 1: u_x = 0 (i.e., x = 0 or x = 1).
  by_cases hx : x ^ 2 + x = 0;
  · -- By kasami_key_identity: 0 * u_y^q = (y^q+y)^{q+1}, so (y^q+y)^{q+1} = 0, so y^q+y = 0.
    have hy_zero : (y ^ (2 ^ k) + y) ^ (2 ^ k + 1) = 0 := by
      have h_y_zero : (y + 1) ^ (kasamiExp k) + y ^ (kasamiExp k) + 1 = 0 := by
        have hLx : (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1 = 0 := by
          have hx_cases : x = 0 ∨ x = 1 := by
            grind +suggestions
          rcases hx_cases with ( rfl | rfl ) <;> simp +decide [ kasamiExp ];
          · grind +splitImp;
          · grind;
        aesop;
      have := kasami_key_identity hn k ( by linarith ) ( by linarith ) y; simp_all +decide [ pow_succ, pow_mul ] ;
    have hy_zero : truncTrace k (y ^ 2 + y) = 0 := by
      simp_all +decide [ truncTrace_artin_schreier ];
    have := truncTrace_ker_trivial hn k hk_odd hk hkn hcop hy_zero; aesop;
  · by_cases hy : y ^ 2 + y = 0;
    · have h_univ_x : (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) = 0 := by
        have h_univ_x : (x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1 = 0 := by
          have hy_cases : y = 0 ∨ y = 1 := by
            grind +suggestions;
          cases hy_cases <;> simp_all +decide [ kasamiExp ];
          grind;
        have h_univ_x : ((x + 1) ^ (kasamiExp k) + x ^ (kasamiExp k) + 1) * (x ^ 2 + x) ^ (2 ^ k) = (x ^ (2 ^ k) + x) ^ (2 ^ k + 1) := by
          apply kasami_key_identity hn k (by linarith) (by linarith) x;
        aesop;
      have h_univ_x : truncTrace k (x ^ 2 + x) = 0 := by
        rw [ truncTrace_artin_schreier ] at * ; aesop;
      have := truncTrace_ker_trivial hn k hk_odd hk hkn hcop h_univ_x; aesop;
    · have h_eq : truncTrace k (x ^ 2 + x) ^ (2 ^ k + 1) * (y ^ 2 + y) ^ (2 ^ k) = truncTrace k (y ^ 2 + y) ^ (2 ^ k + 1) * (x ^ 2 + x) ^ (2 ^ k) := by
        grind +suggestions;
      apply phi_injective_on_units hn k hk hk_odd hkn hn_odd hcop hx hy h_eq

/-
═══════════════════════════════════════════
Layer 8: Structural lemmas
═══════════════════════════════════════════

u²+u = 0 in characteristic 2 iff u ∈ {0, 1}.
-/
lemma sq_add_self_eq_zero_char2 {F : Type*} [Field F] [CharP F 2] {u : F} :
    u ^ 2 + u = 0 ↔ u = 0 ∨ u = 1 := by
  grind

/-
The Kasami exponent d is coprime to 2^n-1.
-/
lemma kasami_exp_coprime {k n : ℕ} (hk : 1 < k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hn_odd : Odd n) (hk_odd : Odd k) :
    Nat.Coprime (kasamiExp k) (2 ^ n - 1) := by
  -- So $d | 2^{ �6�k} - 1$.
  have h_div : kasamiExp k ∣ 2 ^ (6 * k) - 1 := by
    -- By definition of $kasamiExp$, we know that $(2^{2k} - 2^k + 1) * (2^k + 1) = 2^{3k} + 1$.
    have h_kasami_mul : (2 ^ (2 * k) - 2 ^ k + 1) * (2 ^ k + 1) = 2 ^ (3 * k) + 1 := by
      zify;
      rw [ Nat.cast_sub ( by gcongr <;> linarith ) ] ; push_cast ; ring;
    exact dvd_trans ( dvd_of_mul_right_eq _ h_kasami_mul ) ( by use 2 ^ ( 3 * k ) - 1; zify ; cases k <;> norm_num [ Nat.pow_succ', Nat.pow_mul' ] at * ; ring );
  -- Thus $\gcd(d, 2^n - 1) | \gcd(2^{6k} - 1, 2^n - 1) = 2^{\gcd(6k,n)} - 1$.
  have h_gcd : Nat.gcd (kasamiExp k) (2 ^ n - 1) ∣ 2 ^ (Nat.gcd (6 * k) n) - 1 := by
    have h_gcd : Nat.gcd (kasamiExp k) (2 ^ n - 1) ∣ Nat.gcd (2 ^ (6 * k) - 1) (2 ^ n - 1) := by
      exact Nat.dvd_gcd ( Nat.dvd_trans ( Nat.gcd_dvd_left _ _ ) h_div ) ( Nat.gcd_dvd_right _ _ );
    simp_all +decide [ Nat.dvd_gcd_iff ];
  -- Since $\gcd(k, n) = 1$ and $n$ is odd, $\gcd(6k, n) = \gcd(6, n)$.
  have h_gcd_simplified : Nat.gcd (6 * k) n = Nat.gcd 6 n := by
    exact Nat.Coprime.gcd_mul_right_cancel _ hcop;
  -- Since $n$ is odd, $\gcd(6, n) = 1$ or $3$.
  have h_gcd_final : Nat.gcd 6 n = 1 ∨ Nat.gcd 6 n = 3 := by
    have := Nat.gcd_dvd_left 6 n; ( have := Nat.le_of_dvd ( by linarith ) this; interval_cases _ : Nat.gcd 6 n <;> simp_all +decide ; );
    · have := Nat.gcd_dvd_right 6 n; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
      exact absurd this ( by simpa using hn_odd );
    · have := Nat.gcd_dvd_right 6 n; simp_all +decide [ Nat.dvd_prime ] ;
      exact absurd ( hn_odd.of_dvd_nat this ) ( by decide );
  cases h_gcd_final <;> simp_all +decide [ Nat.Coprime, Nat.Coprime.symm ];
  have := Nat.gcd_dvd_left ( kasamiExp k ) ( 2 ^ n - 1 ) ; ( have := Nat.le_of_dvd ( by decide ) h_gcd; interval_cases _ : Nat.gcd ( kasamiExp k ) ( 2 ^ n - 1 ) <;> simp_all +decide ; );
  unfold kasamiExp at this; norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod ] at this;
  rw [ ← Nat.mod_add_div ( 2 ^ ( 2 * k ) ) 7, ← Nat.mod_add_div ( 2 ^ k ) 7 ] at this; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at this;
  rw [ ← Nat.mod_add_div k 6 ] at this; norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod ] at this; have := Nat.mod_lt k ( by decide : 6 > 0 ) ; interval_cases k % 6 <;> norm_num at *;
  all_goals omega;

/-
WLOG reduction: APN of x^d reduces to the normalized differential.
-/
lemma apn_of_normalized {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (hn_pos : 1 < n)
    (d : ℕ) (hd_cop : Nat.Coprime d (2 ^ n - 1))
    (h_norm : ∀ (x y : F),
      (x + 1) ^ d + x ^ d = (y + 1) ^ d + y ^ d →
      y = x ∨ y = x + 1) :
    IsAPN (fun (x : F) => x ^ d) := by
  intro a ha x y hxy
  have h_subst : (x / a + 1) ^ d + (x / a) ^ d = (y / a + 1) ^ d + (y / a) ^ d := by
    convert congr_arg ( fun z => z / a ^ d ) hxy using 1 <;> ring;
    · rw [ show 1 + x * a⁻¹ = ( x + a ) * a⁻¹ by rw [ add_mul, mul_inv_cancel₀ ha ] ; ring ] ; rw [ mul_pow ] ; ring;
    · rw [ show 1 + y * a⁻¹ = ( y + a ) * a⁻¹ by rw [ add_mul, mul_inv_cancel₀ ha ] ; ring ] ; rw [ mul_pow ] ; ring;
  cases h_norm _ _ h_subst <;> simp_all +decide [ div_eq_iff, add_mul ]

-- ═══════════════════════════════════════════
-- Layer 9: Main theorem
-- ═══════════════════════════════════════════

/-- **Kasami APN Theorem.** Let F = GF(2ⁿ) with n odd. Let k be odd with
1 < k < n and gcd(k,n) = 1. Then f(x) = x^d where d = 2^{2k} - 2^k + 1
is APN on F.

The proof uses the Dempwolff–Müller Theorem 3.2 (LxXk'_bijective) as its core
engine, connecting the Kasami differential to the truncated trace via the
key identity and decomposing the resulting map as a composition of two bijections. -/
theorem kasami_is_apn {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : Fintype.card F = 2 ^ n) (k : ℕ)
    (hk : 1 < k) (hk_odd : Odd k) (hkn : k < n)
    (hn_odd : Odd n) (hcop : Nat.Coprime k n) :
    IsAPN (fun (x : F) => x ^ (kasamiExp k)) := by
  have hn_pos : 1 < n := lt_trans hk hkn
  apply apn_of_normalized hn hn_pos _ (kasami_exp_coprime hk hkn hcop hn_odd hk_odd)
  intro x y hdiff
  have hu : x ^ 2 + x = y ^ 2 + y :=
    kasami_collision_forces_equal_u hn k hk hk_odd hkn hn_odd hcop hdiff
  -- x²+x = y²+y means (x+y)²+(x+y) = 0
  have h_sum_zero : (x + y) ^ 2 + (x + y) = 0 := by
    have h2 : (x + y) ^ 2 = x ^ 2 + y ^ 2 := add_pow_char (R := F) (p := 2) x y
    rw [h2]
    have : x ^ 2 + y ^ 2 + (x + y) = (x ^ 2 + x) + (y ^ 2 + y) := by ring
    rw [this, hu, CharTwo.add_self_eq_zero]
  rw [sq_add_self_eq_zero_char2] at h_sum_zero
  rcases h_sum_zero with h | h
  · left
    have := neg_eq_of_add_eq_zero_left h
    rwa [CharTwo.neg_eq] at this
  · right
    have : y = x + y + x := by
      rw [add_comm x y, add_assoc]; simp [CharTwo.add_self_eq_zero]
    rwa [h, add_comm] at this

end KasamiAPN
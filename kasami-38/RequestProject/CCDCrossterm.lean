/-
# CCD Cross-Term Analysis: `ccd_crossterm_gives_linPolyL`

## Proof Strategy (Canteaut-Charpin-Dobbertin)

1. **S3.1**: `z^{2^{3k}} + z = M_k(L_k(z))` (algebraic factorization)
2. **S3.2**: `C(y₂+z) + C(y₂)` decomposes into cross-terms
3. **S3.3**: `ker(M_k) = {0,1}` when `gcd(k,n) = 1`
4. **S3.4**: Assembly: conclude `L_k(z) = 0`
-/
import RequestProject.Defs

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

/-! ## L_k and M_k are Additive -/

theorem linPolyL_add (k : ℕ) (a b : F) :
    linPolyL k (a + b) = linPolyL k a + linPolyL k b := by
  simp only [linPolyL, char2_freshman a b (2 * k), char2_freshman a b k]; ring

theorem linPolyM_add (k : ℕ) (a b : F) :
    linPolyM k (a + b) = linPolyM k a + linPolyM k b := by
  simp only [linPolyM, char2_freshman a b k]; ring

/-! ## S3.1: Key Factorization M_k(L_k(z)) = z^{2^{3k}} + z -/

/-- `L_k(z)^{2^k}` expanded via Freshman's dream. -/
theorem linPolyL_pow2k (k : ℕ) (z : F) :
    (linPolyL k z) ^ (2 ^ k) = z ^ (2 ^ (3 * k)) + z ^ (2 ^ (2 * k)) + z ^ (2 ^ k) := by
  simp only [linPolyL]
  rw [add_pow_char_pow (z ^ (2 ^ (2 * k)) + z ^ (2 ^ k)) z 2 k,
      add_pow_char_pow (z ^ (2 ^ (2 * k))) (z ^ (2 ^ k)) 2 k]
  have h1 : (z ^ 2 ^ (2 * k)) ^ 2 ^ k = z ^ 2 ^ (3 * k) := by rw [← pow_mul]; congr 1; ring
  have h2 : (z ^ 2 ^ k) ^ 2 ^ k = z ^ 2 ^ (2 * k) := by rw [← pow_mul]; congr 1; ring
  rw [h1, h2]

/-- **S3.1**: `z^{2^{3k}} + z = M_k(L_k(z))`. -/
theorem mk_lk_factorization (k : ℕ) (z : F) :
    z ^ (2 ^ (3 * k)) + z = linPolyM k (linPolyL k z) := by
  simp only [linPolyM]
  rw [linPolyL_pow2k]
  simp only [linPolyL]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf; simp [h2]

/-! ## S3.2: CCD Cross-Term Difference -/

/-- **(S3.2a)** Generic cross-term for `2^i + 2^j` exponents in char 2. -/
theorem pow2_cross_term (y z : F) (i j : ℕ) :
    (y + z) ^ (2 ^ i + 2 ^ j) + y ^ (2 ^ i + 2 ^ j) =
    y ^ (2 ^ i) * z ^ (2 ^ j) + z ^ (2 ^ i) * y ^ (2 ^ j) + z ^ (2 ^ i + 2 ^ j) := by
  rw [pow_add, pow_add, pow_add,
      add_pow_char_pow y z 2 i, add_pow_char_pow y z 2 j]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf; simp [h2]

/-- **(S3.2b)** Cross-term for `2^i + 1` exponents. -/
theorem pow2_cross_term_one (y z : F) (i : ℕ) :
    (y + z) ^ (2 ^ i + 1) + y ^ (2 ^ i + 1) =
    y ^ (2 ^ i) * z + z ^ (2 ^ i) * y + z ^ (2 ^ i + 1) := by
  conv_lhs => rw [show (1 : ℕ) = 2 ^ 0 from by norm_num]
  rw [pow_add, pow_add, pow_add,
      add_pow_char_pow y z 2 i, add_pow_char_pow y z 2 0]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp only [pow_zero, pow_one]
  ring_nf; simp [h2]

/-
**(S3.2)** Full CCD cross-term difference: `C(y+z) + C(y)`.
-/
theorem ccd_cross_diff_expansion (k : ℕ) (y z : F) :
    ccdCrossTerm k (y + z) + ccdCrossTerm k y =
    (y ^ (2 ^ (2 * k)) * z ^ (2 ^ k) + z ^ (2 ^ (2 * k)) * y ^ (2 ^ k) +
     z ^ (2 ^ (2 * k) + 2 ^ k)) +
    (y ^ (2 ^ k) * z + z ^ (2 ^ k) * y + z ^ (2 ^ k + 1)) +
    (y ^ (2 ^ (2 * k)) * z + z ^ (2 ^ (2 * k)) * y + z ^ (2 ^ (2 * k) + 1)) := by
  simp only [ccdCrossTerm]
  have h1 := pow2_cross_term y z (2 * k) k
  have h2 := pow2_cross_term_one y z k
  have h3 := pow2_cross_term_one y z (2 * k)
  have h2char : (2 : F) = 0 := CharP.cast_eq_zero F 2
  -- All terms are additive; after expanding, it's a ring identity in char 2
  ring_nf
  ring_nf at h1 h2 h3
  grind

/-! ## S3.3: Kernel of M_k -/

theorem mk_ker_zero (k : ℕ) : linPolyM k (0 : F) = 0 := by
  simp [linPolyM]

theorem mk_ker_one (k : ℕ) : linPolyM k (1 : F) = 0 := by
  simp [linPolyM, one_pow, CharTwo.add_self_eq_zero]

/-- `M_k(x) = 0` iff `x^{2^k} = x`. -/
theorem mk_zero_iff (k : ℕ) (x : F) : linPolyM k x = 0 ↔ x ^ (2 ^ k) = x := by
  simp only [linPolyM]; rw [← CharTwo.sub_eq_add]; exact sub_eq_zero

/-
**(S3.3b)** Frobenius fixed points: `x^{2^k} = x` and `gcd(k,n) = 1` imply `x ∈ {0, 1}`.

    This follows because the set `{x : x^{2^k} = x}` is the subfield `GF(2^{gcd(k,n)})`.
    When `gcd(k,n) = 1`, this is `GF(2) = {0, 1}`.
    The proof uses the fact that `x^{2^k} - x` has at most `2^k` roots,
    and all elements of `GF(2^{gcd(k,n)})` are roots.
-/
theorem frob_fixed_in_GF2 (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (x : F) (hx : x ^ (2 ^ k) = x) :
    x = 0 ∨ x = 1 := by
  have h_root : ∀ m : ℕ, x ^ (2 ^ (m * k)) = x := by
    intro m; induction m <;> simp_all +decide [ Nat.succ_mul, pow_add, pow_mul' ] ;
  -- Since $k$ and $n$ are coprime, there exists an integer $m$ such that $mk \equiv 1 \pmod{n}$.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m * k ≡ 1 [MOD n] := by
    have := Nat.exists_mul_mod_eq_one_of_coprime hk;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ mul_comm, Nat.ModEq ];
    · exact ⟨ 0, by simp +decide ⟩;
    · exact ⟨ this.choose, this.choose_spec.2 ⟩;
  -- Since $mk \equiv 1 \pmod{n}$, we have $x^{2^{mk}} = x^{2^1} = x^2$.
  have h_exp : x ^ (2 ^ (m * k)) = x ^ 2 := by
    rw [ ← Nat.mod_add_div ( m * k ) n, hm ];
    have h_exp : x ^ (2 ^ n) = x := by
      rw [ ← hn, FiniteField.pow_card ];
    induction m * k / n <;> simp_all +decide [ pow_add, pow_mul ];
    · rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
    · rw [ ← pow_mul, mul_comm, pow_mul, h_exp ];
  grind

/-- **(S3.3)** Kernel of `M_k`: `M_k(x) = 0` implies `x ∈ {0, 1}`. -/
theorem mk_ker_eq_F2 (n k : ℕ) (hn : Fintype.card F = 2 ^ n) (hk : Nat.Coprime k n)
    (x : F) (hx : linPolyM k x = 0) : x = 0 ∨ x = 1 :=
  frob_fixed_in_GF2 n k hn hk x ((mk_zero_iff k x).mp hx)

/-! ## S3.4: L_k Properties and Main Assembly -/

theorem mk_eq_implies_diff_zero (k : ℕ) (a b : F)
    (hab : linPolyM k a = linPolyM k b) : linPolyM k (a + b) = 0 := by
  rw [linPolyM_add, hab, CharTwo.add_self_eq_zero]

theorem linPolyL_one (k : ℕ) : linPolyL k (1 : F) = 1 := by
  simp [linPolyL, one_pow]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ring_nf; simp [h2]

theorem linPolyL_zero (k : ℕ) : linPolyL k (0 : F) = 0 := by
  simp [linPolyL]

/-- If `L_k(z) = 1`, then `L_k(z + 1) = 0` (by additivity). -/
theorem lk_eq_one_implies_shifted_zero (k : ℕ) (z : F) (h : linPolyL k z = 1) :
    linPolyL k (z + 1) = 0 := by
  rw [linPolyL_add, h, linPolyL_one, CharTwo.add_self_eq_zero]

/-- **(S3.4a)** If `M_k(L_k(z)) = 0` and `gcd(k,n) = 1`, then `L_k(z) ∈ {0, 1}`. -/
theorem mk_lk_zero_implies_lk_01 (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (z : F) (h : linPolyM k (linPolyL k z) = 0) :
    linPolyL k z = 0 ∨ linPolyL k z = 1 :=
  mk_ker_eq_F2 n k hn hk _ h

/-- **(S3.4b)** `L_k(z) = 1` is incompatible with `z ∉ GF(2)` under CCD constraints.

    If `L_k(z) = 1`, then `L_k(z + 1) = 0`, so `z + 1 ∈ ker(L_k)`.
    The kernel of `L_k` when `gcd(k,n) = 1` has cardinality in `{1, 4}`:
    - If `|ker| = 1`: the only element is 0, so `z + 1 = 0`, i.e. `z = 1`.
      This contradicts `z ≠ 1`.
    - If `|ker| = 4` (when `3 | n`): additional CCD constraints rule out all
      nonzero kernel elements.

    This sub-lemma requires deep kernel analysis and is left sorry'd. -/
theorem lk_ne_one_from_ccd (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (y₂ z : F)
    (hccd : z ^ (2 ^ (3 * k)) + z = ccdCrossTerm k (y₂ + z) + ccdCrossTerm k y₂)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    linPolyL k z ≠ 1 := by
  sorry

/-- **Main Theorem: `ccd_crossterm_gives_linPolyL`**

From the CCD second derivative equation, conclude `L_k(z) = 0`. -/
theorem ccd_crossterm_gives_linPolyL (n k : ℕ) (hn : Fintype.card F = 2 ^ n)
    (hk : Nat.Coprime k n) (y₂ z : F)
    (hccd : z ^ (2 ^ (3 * k)) + z = ccdCrossTerm k (y₂ + z) + ccdCrossTerm k y₂)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    linPolyL k z = 0 := by
  -- LHS = M_k(L_k(z))
  have hmk_lk := mk_lk_factorization k z
  -- RHS = C(y₂+z) + C(y₂), and the CCD equation gives us M_k(L_k(z)) = RHS
  -- We need to show M_k(L_k(z)) = 0
  -- This requires the cross-term factorization (S3.2) and further analysis
  -- For now, assuming we can establish L_k(z) ∈ {0, 1}:
  sorry

end
import Mathlib
import ConjecturesMTupleTripleCount.MTuple.Count

/-!
# The unconditional m-tuple / triple count is FALSE

The old `MTupleCount.lean` proved `imgCount m f a c = 2^{(m-1)n - m}` only behind
the hypothesis `FlatSpectrum`, which forces all Walsh values to be `±2^{n/2}` and
is therefore **unsatisfiable for `n` odd** (it is `n`-odd that the whole Kasami
development is about).  Dropping it and keeping only `cᵢ ≠ 0` makes the statement
**false**.  This file gives two machine-checked refutations.

* `disproof_m2`: for **any** APN `f` and any nonzero `c₀`, taking all coefficients
  equal to `c₀` gives `imgCount 2 f a (fun _ => c₀) = 2^{n-1}`, which differs from
  the conjectured `2^{n-2}` (see `m_tuple_count_two_false`).

* `disproof_triple_cube`: for the cube (Gold/Kasami `k = 1`) map, which is APN,
  with `n` odd the equal-coefficient **triple** count is `0`, not `2^{2n-3}`
  (see `triple_count_cube_false`).

Both rest on the genuine `Vanish` condition failing — exactly the content the
`FlatSpectrum` hypothesis was hiding.
-/

set_option maxHeartbeats 1600000

namespace MTuple

open Finset Fintype BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## A general `m = 2` refutation (any APN function) -/

/--
With all coefficients equal to a nonzero `c₀`, the `m = 2` image count is the
size of the derivative image, `2^{n-1}`.
-/
theorem disproof_m2 (n : ℕ) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) (c0 : F) (hc0 : c0 ≠ 0) :
    imgCount 2 f a (fun _ => c0) = 2 ^ (n - 1) := by
  have h_card : (Finset.univ.filter (fun y : Fin 2 → F => y 0 ∈ derivImage f a ∧ y 1 ∈ derivImage f a ∧ y 0 + y 1 = 0)).card = (derivImage f a).card := by
    refine' Finset.card_bij ( fun y hy => y 0 ) _ _ _ <;> simp +decide [ Finset.mem_filter ];
    · exact fun _ _ _ _ => by assumption;
    · simp_all +decide [ funext_iff, Fin.forall_fin_two ];
      grind;
    · intro b hb
      use ![b, b];
      simp_all +decide [ CharTwo.add_self_eq_zero ];
  convert h_card using 1;
  · unfold imgCount; simp +decide [ Fin.sum_univ_two ] ;
    simp +decide only [← mul_add, mul_eq_zero, hc0, false_or, and_assoc];
  · rw [ ← derivImage_card n hcard f hf a ha ]

/--
**The unconditional `m`-tuple count is false** (at `m = 2`): the genuine value
`2^{n-1}` differs from the conjectured `2^{(2-1)n - 2} = 2^{n-2}` for `n ≥ 2`.
-/
theorem m_tuple_count_two_false (n : ℕ) (hn : 2 ≤ n) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) (c0 : F) (hc0 : c0 ≠ 0) :
    imgCount 2 f a (fun _ => c0) ≠ 2 ^ ((2 - 1) * n - 2) := by
  rw [ disproof_m2 n hcard f hf a ha c0 hc0 ];
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ pow_succ' ]

/-! ## The cube map is APN and refutes the triple count -/

omit [Fintype F] [DecidableEq F] in
/--
The cube derivative in characteristic two:
`Δ(x³)_a(x) = a·x² + a²·x + a³`.
-/
theorem cube_deriv (a x : F) :
    deriv (· ^ 3) a x = a * x ^ 2 + a ^ 2 * x + a ^ 3 := by
  unfold deriv;
  grind

/--
The cube map `x ↦ x³` is APN.
-/
theorem cube_isAPN : IsAPN (· ^ 3 : F → F) := by
  intro a ha b
  have h_eq : ∀ x y : F, (x + a) ^ 3 + x ^ 3 = b → (y + a) ^ 3 + y ^ 3 = b → x = y ∨ x = y + a := by
    grind;
  by_cases h : ∃ x : F, ( x + a ) ^ 3 + x ^ 3 = b <;> simp_all +decide [ Fintype.card_subtype ];
  obtain ⟨ x, hx ⟩ := h;
  exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun y => ( y + a ) ^ 3 + y ^ 3 = b ) Finset.univ ⊆ { x, x + a } by intros y hy; simpa using h_eq _ _ ( Finset.mem_filter.mp hy |>.2 ) hx ) ) ( Finset.card_insert_le _ _ )

/--
For `n` odd, `3 ∤ 2^n - 1` (since `2^n ≡ 2 [MOD 3]`).
-/
theorem three_not_dvd_two_pow_sub_one (n : ℕ) (hodd : Odd n) :
    ¬ (3 ∣ 2 ^ n - 1) := by
  obtain ⟨ k, rfl ⟩ := hodd; norm_num [ Nat.ModEq, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.dvd_iff_mod_eq_zero ] ;
  rw [ ← Nat.mod_add_div ( 4 ^ k * 2 ) 3 ] ; norm_num [ Nat.mul_mod, Nat.pow_mod ]

/--
For `n` odd, no three elements of the cube derivative image sum to zero.
-/
theorem cube_no_three_sum_zero (n : ℕ) (hodd : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (y0 y1 y2 : F)
    (h0 : y0 ∈ derivImage (· ^ 3) a) (h1 : y1 ∈ derivImage (· ^ 3) a)
    (h2 : y2 ∈ derivImage (· ^ 3) a) :
    y0 + y1 + y2 ≠ 0 := by
  intro h;
  -- Let `s = x0 + x1 + x2`. Then `a s^2 + a^2 s + a^3 = 0`, i.e. `a (s^2 + a s + a^2) = 0`; since `a ≠ 0`, `s^2 + a s + a^2 = 0`.
  obtain ⟨x0, x1, x2, hx0, hx1, hx2, hs⟩ : ∃ x0 x1 x2 : F, y0 = deriv (fun x => x ^ 3) a x0 ∧ y1 = deriv (fun x => x ^ 3) a x1 ∧ y2 = deriv (fun x => x ^ 3) a x2 ∧ (x0 + x1 + x2) ^ 2 + a * (x0 + x1 + x2) + a ^ 2 = 0 := by
    obtain ⟨x0, hx0⟩ : ∃ x0 : F, y0 = deriv (fun x => x ^ 3) a x0 := by
      unfold derivImage at h0; aesop;
    obtain ⟨x1, hx1⟩ : ∃ x1 : F, y1 = deriv (fun x => x ^ 3) a x1 := by
      unfold derivImage at h1; aesop;
    obtain ⟨x2, hx2⟩ : ∃ x2 : F, y2 = deriv (fun x => x ^ 3) a x2 := by
      unfold derivImage at h2; aesop;
    use x0, x1, x2;
    simp_all +decide [ deriv ];
    grind;
  -- Put `w = s * a⁻¹`. Then `a^2 (w^2 + w + 1) = 0`, so `w^2 + w + 1 = 0`.
  obtain ⟨w, hw⟩ : ∃ w : F, w ^ 2 + w + 1 = 0 := by
    use (x0 + x1 + x2) / a;
    grind;
  -- Since `w^3 = 1` and `w ≠ 0`, `w ≠ 1`, we have `orderOf w ∣ 3` and `orderOf w ≠ 1`.
  have h_order : orderOf w ∣ 3 ∧ orderOf w ≠ 1 := by
    simp_all +decide [ orderOf_dvd_iff_pow_eq_one ];
    grind;
  have h_order : orderOf w ∣ 2 ^ n - 1 := by
    rw [ ← hcard, orderOf_dvd_iff_pow_eq_one ];
    rw [ FiniteField.pow_card_sub_one_eq_one ] ; aesop;
  have := Nat.le_of_dvd ( by decide ) ( ‹orderOf w ∣ 3 ∧ orderOf w ≠ 1›.1 ) ; interval_cases orderOf w <;> simp_all +decide ;
  exact absurd h_order ( by simpa [ ← Int.natCast_dvd_natCast ] using three_not_dvd_two_pow_sub_one n hodd )

/--
For `n` odd, the equal-coefficient triple count of the cube map is `0`.
-/
theorem disproof_triple_cube (n : ℕ) (hodd : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (c0 : F) (hc0 : c0 ≠ 0) :
    imgCount 3 (· ^ 3) a (fun _ => c0) = 0 := by
  unfold imgCount;
  simp +decide [ Fin.sum_univ_three, Fin.forall_fin_succ ];
  intro x hx0 hx1 hx2; contrapose! hc0; simp_all +decide [ ← mul_add ] ;
  exact hc0.resolve_right ( cube_no_three_sum_zero n hodd hcard a ha _ _ _ hx0 hx1 hx2 )

/--
**The unconditional triple count is false**: for the APN cube map with `n` odd,
the triple count is `0`, not `2^{2n-3}`.
-/
theorem triple_count_cube_false (n : ℕ) (hodd : Odd n) (hcard : Fintype.card F = 2 ^ n)
    (a : F) (ha : a ≠ 0) (c0 : F) (hc0 : c0 ≠ 0) :
    imgCount 3 (· ^ 3) a (fun _ => c0) ≠ 2 ^ (2 * n - 3) := by
  exact ne_of_eq_of_ne ( disproof_triple_cube n hodd hcard a ha c0 hc0 ) ( by positivity )

end MTuple
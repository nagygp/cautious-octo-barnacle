/-
# AB implies APN — Main Theorem and Kasami Corollary

This file proves that Almost Bent (AB) functions are Almost Perfect Nonlinear (APN)
over finite fields of characteristic 2, and derives that Kasami functions are APN.

## Proof strategy (Chabaud-Vaudenay 1994)

1. **Character properties**: The additive character χ(x) = (-1)^{Tr(x)} is multiplicative
   over addition and satisfies character orthogonality.

2. **Parseval's identity**: ∑_a W_f(a,b)² = |F|² for all b.

3. **Global fourth moment identity**: ∑_{a,b} W_f(a,b)⁴ = |F|² · ∑_{a,b} δ_f(a,b)².
   This connects the Walsh spectrum to differential properties.

4. **AB fourth moment**: For AB functions, ∑_{a,b} W_f(a,b)⁴ = |F|³(3|F| − 2).

5. **Combinatorial lower bound**: For a ≠ 0, ∑_b δ_f(a,b)² ≥ 2|F|,
   because solutions pair up (x and x+a), forcing even multiplicities.

6. **Main argument**: The average of ∑_b δ² over a ≠ 0 equals 2|F| (from steps 3-4),
   and each term is ≥ 2|F| (from step 5), so each term equals 2|F|,
   which implies δ_f(a,b) ≤ 2 for all b, i.e., f is APN.

## References

* Chabaud, Vaudenay, "Links between Differential and Linear Cryptanalysis",
  Advances in Cryptology — EUROCRYPT '94, LNCS 950, pp. 356–365.
* Kasami, "The Weight Enumerators for Several Classes of Subcodes of the
  2nd Order Binary Reed-Muller Codes", Inform. and Control 18 (1971), 369–394.
-/
import RequestProject.Defs

open Finset BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

-- Notation for readability
local notation "q" => (Fintype.card F : ℤ)
local notation "qn" => Fintype.card F

/-! ## Section 1: Character Properties -/

lemma chi_zero : chi (0 : F) = 1 := by
  simp [chi, map_zero]

/-
The character χ is multiplicative: χ(x+y) = χ(x)·χ(y).
    This follows from the linearity of the trace and the sign rule in ZMod 2.
-/
lemma chi_add (x y : F) : chi (x + y) = chi x * chi y := by
  simp +decide [ chi, mul_add, add_mul ];
  cases Fin.exists_fin_two.mp ⟨ Algebra.trace ( ZMod 2 ) F x, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ Algebra.trace ( ZMod 2 ) F y, rfl ⟩ <;> simp +decide [ * ]

/-
χ(x)² = 1 since χ takes values in {1, −1}.
-/
lemma chi_sq (x : F) : chi x ^ 2 = 1 := by
  unfold chi;
  split_ifs <;> norm_num

/-
χ takes only the values 1 and −1.
-/
lemma chi_values (x : F) : chi x = 1 ∨ chi x = -1 := by
  -- By definition of chi, we have chi x = 1 if the trace of x is 0, and chi x = -1 otherwise.
  by_cases h_trace : (Algebra.trace (ZMod 2) F) x = 0;
  · exact Or.inl ( if_pos h_trace );
  · unfold chi; aesop;

/-- In characteristic 2, x + x = 0. -/
lemma CharTwo.add_self (x : F) : x + x = 0 := by
  have h : (2 : F) = 0 := CharP.cast_eq_zero F 2
  calc x + x = 2 * x := by ring
    _ = 0 * x := by rw [h]
    _ = 0 := by ring

/-
Character orthogonality: ∑_x χ(a·x) = |F| if a = 0, else 0.
-/
lemma sum_chi_mul (a : F) :
    ∑ x : F, chi (a * x) = if a = 0 then q else 0 := by
      split_ifs with ha;
      · simp +decide [ ha, chi_zero ];
      · -- Since $a \neq 0$, multiplication by $a$ is a bijection on $F$.
        have h_bij : Function.Bijective (fun x : F => a * x) := by
          exact ⟨ mul_right_injective₀ ha, mul_left_surjective₀ ha ⟩;
        have h_sum_zero : ∑ x : F, chi x = 0 := by
          -- Since the trace map is surjective, there exists some $y \in F$ such that $\text{Tr}(y) \neq 0$.
          obtain ⟨y, hy⟩ : ∃ y : F, (Algebra.trace (ZMod 2) F) y ≠ 0 := by
            exact not_forall.mp fun h => by simpa [ h ] using Algebra.trace_surjective ( ZMod 2 ) F 1;
          -- Since $\chi(y) \neq 1$, we have $\chi(y) = -1$.
          have h_chi_y : chi y = -1 := by
            unfold chi; aesop;
          -- Since $\chi(y) = -1$, we have $\sum_{x \in F} \chi(x + y) = \sum_{x \in F} \chi(x) \cdot \chi(y) = -\sum_{x \in F} \chi(x)$.
          have h_sum_shift : ∑ x : F, chi (x + y) = -∑ x : F, chi x := by
            rw [ ← Finset.sum_neg_distrib, Finset.sum_congr rfl ] ; intros ; rw [ chi_add ] ; aesop;
          rw [ show ∑ x : F, chi ( x + y ) = ∑ x : F, chi x from Equiv.sum_comp ( Equiv.addRight y ) fun x => chi x ] at h_sum_shift ; linarith;
        exact h_sum_zero ▸ Equiv.sum_comp ( Equiv.ofBijective _ h_bij ) _

/-! ## Section 2: Walsh Transform Basics -/

/-
W_f(a, 0) = |F| if a = 0, else 0.
-/
lemma walsh_b_zero (f : F → F) (a : F) :
    walshTransform f a 0 = if a = 0 then q else 0 := by
      convert sum_chi_mul a using 1;
      unfold walshTransform; aesop;

/-
Parseval's identity: ∑_a W_f(a,b)² = |F|² for every b.
    Proof: expand W² as a double sum, swap with ∑_a, apply character
    orthogonality on a, use x + x = 0 in char 2.
-/
lemma parseval_walsh (f : F → F) (b : F) :
    ∑ a : F, walshTransform f a b ^ 2 = q ^ 2 := by
      -- Expand $W_f(a,b)^2$ using the definition of the Walsh transform.
      have h_expand : ∑ a : F, (walshTransform f a b)^2 = ∑ x : F, ∑ y : F, chi (b * f x + b * f y) * ∑ a : F, chi (a * (x + y)) := by
        -- By definition of $W_f(a,b)$, we can expand $W_f(a,b)^2$ as follows:
        have h_expand : ∀ a : F, (walshTransform f a b)^2 = ∑ x : F, ∑ y : F, chi (b * f x + a * x) * chi (b * f y + a * y) := by
          unfold walshTransform;
          exact fun a => by rw [ sq, Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ;
        simp +decide only [h_expand, mul_add, Finset.mul_sum _ _ _];
        simp +decide only [chi_add, mul_comm];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) );
      -- Apply character orthogonality on a, use x + x = 0 in char 2.
      have h_ortho : ∀ x y : F, ∑ a : F, chi (a * (x + y)) = if x = y then (Fintype.card F : ℤ) else 0 := by
        intro x y;
        convert sum_chi_mul ( x + y ) using 1;
        · ac_rfl;
        · grind;
      simp_all +decide [ Finset.sum_ite, Finset.filter_eq, Finset.filter_ne ];
      simp +decide [ ← two_mul, sq, chi ];
      simp +decide [ show ( 2 : F ) = 0 by exact CharP.cast_eq_zero F 2 ]

/-! ## Section 3: Delta Count Properties -/

/-
The total count ∑_b δ_f(a,b) = |F|: each x contributes to exactly one b.
-/
lemma delta_sum (f : F → F) (a : F) :
    ∑ b : F, (deltaCount f a b : ℤ) = q := by
      norm_cast;
      simp +decide only [deltaCount];
      simp +decide only [card_filter];
      rw [ Finset.sum_comm ] ; aesop

/-
At a = 0: δ_f(0,0) = |F| and δ_f(0,b) = 0 for b ≠ 0 (char 2).
-/
lemma delta_at_zero (f : F → F) (b : F) :
    (deltaCount f 0 b : ℤ) = if b = 0 then q else 0 := by
      split_ifs <;> simp_all +decide [ deltaCount ];
      · simp +decide [ ← two_mul, CharTwo.two_eq_zero ];
      · grind

/-
Solutions pair up: if x solves f(x+a)+f(x)=b, so does x+a.
    Since a ≠ 0, these are distinct, so δ_f(a,b) is even.
-/
lemma delta_even (f : F → F) (a : F) (ha : a ≠ 0) (b : F) :
    2 ∣ deltaCount f a b := by
      -- Define the involution φ : F → F by φ(x) = x + a on the set S = {x ∈ F : f(x+a) + f(x) = b}.
      set S := Finset.filter (fun x => f (x + a) + f x = b) Finset.univ with hS_def
      have h_involution : ∀ x ∈ S, x + a ∈ S := by
        grind +ring
      have h_no_fixed_points : ∀ x ∈ S, x ≠ x + a := by
        aesop;
      -- Since φ is an involution on S, S can be partitioned into pairs {x, x + a}.
      have h_partition : ∃ T : Finset (Finset F), (∀ t ∈ T, t.card = 2) ∧ (∀ t ∈ T, ∀ x ∈ t, x ∈ S) ∧ (∀ x ∈ S, ∃ t ∈ T, x ∈ t) ∧ (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂) := by
        refine' ⟨ Finset.image ( fun x => { x, x + a } ) S, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
        · exact fun x hx => ⟨ x, hx, Or.inl rfl ⟩;
        · grind;
      obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := h_partition; rw [ show deltaCount f a b = S.card from rfl ] ; rw [ show S = Finset.biUnion T id from ?_ ] ; rw [ Finset.card_biUnion ] <;> aesop;
      grind

/-! ## Section 4: The Global Fourth Moment Identity

The key identity connecting Walsh spectrum to differential uniformity:
  ∑_{a,b} W_f(a,b)⁴ = |F|² · ∑_{a,b} δ_f(a,b)²

Proof sketch: Expand W_f(a,b)⁴ = (∑_x χ(bf(x)+ax))⁴ as a sum over 4-tuples
(x₁,x₂,x₃,x₄). Sum over a using character orthogonality to get the constraint
x₁+x₂+x₃+x₄=0. Sum over b to get f(x₁)+f(x₂)+f(x₃)+f(x₄)=0.
The resulting count equals ∑_{s,t} (#{x : f(x)+f(x+s)=t})² = ∑_{a,b} δ(a,b)².
-/

lemma fourth_moment_identity (f : F → F) :
    ∑ a : F, ∑ b : F, walshTransform f a b ^ 4 =
    q ^ 2 * ∑ a : F, ∑ b : F, ((deltaCount f a b : ℤ) ^ 2) := by
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ a : F, ∑ b : F, (walshTransform f a b) ^ 4 = ∑ x1 : F, ∑ y1 : F, ∑ x2 : F, ∑ y2 : F, ∑ b : F, (chi (b * (f x1 + f y1 + f x2 + f y2))) * (∑ a : F, (chi (a * (x1 + y1 + x2 + y2)))) := by
        have h_fubini : ∀ a b : F, (walshTransform f a b) ^ 4 = ∑ x1 : F, ∑ y1 : F, ∑ x2 : F, ∑ y2 : F, (chi (b * (f x1 + f y1 + f x2 + f y2))) * (chi (a * (x1 + y1 + x2 + y2))) := by
          intro a b
          have h_expand : (walshTransform f a b) ^ 4 = (∑ x : F, chi (b * f x + a * x)) * (∑ y : F, chi (b * f y + a * y)) * (∑ x : F, chi (b * f x + a * x)) * (∑ y : F, chi (b * f y + a * y)) := by
            ring!;
          simp +decide only [h_expand, Finset.sum_mul _ _ _, mul_sum];
          simp +decide only [chi_add, mul_add];
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
        simp +decide only [h_fubini, Finset.mul_sum _ _ _];
        simp +decide only [← sum_product'];
        apply Finset.sum_bij (fun x _ => (x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, x.2.1, x.1));
        · simp +decide;
        · grind;
        · simp +decide;
        · grind;
      -- By sum_chi_mul, we know that $\sum_{a} \chi(a \cdot s) = q \cdot [s = 0]$.
      have h_sum_a : ∀ s : F, ∑ a : F, (chi (a * s)) = (Fintype.card F : ℤ) * (if s = 0 then 1 else 0) := by
        intro s
        have := sum_chi_mul s
        simp_all +decide [ mul_comm ];
      -- Apply the result from h_sum_a to simplify the expression.
      have h_simplify : ∑ x1 : F, ∑ y1 : F, ∑ x2 : F, ∑ y2 : F, ∑ b : F, (chi (b * (f x1 + f y1 + f x2 + f y2))) * (Fintype.card F : ℤ) * (if x1 + y1 + x2 + y2 = 0 then 1 else 0) = (Fintype.card F : ℤ) * ∑ x1 : F, ∑ y1 : F, ∑ x2 : F, ∑ y2 : F, (if x1 + y1 + x2 + y2 = 0 then (if f x1 + f y1 + f x2 + f y2 = 0 then (Fintype.card F : ℤ) else 0) else 0) := by
        simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
        simp +decide [ ← Finset.sum_mul, h_sum_a ];
      -- Let's simplify the expression inside the sum.
      have h_simplify_inner : ∀ x1 y1 : F, ∑ x2 : F, ∑ y2 : F, (if x1 + y1 + x2 + y2 = 0 then (if f x1 + f y1 + f x2 + f y2 = 0 then (Fintype.card F : ℤ) else 0) else 0) = (Fintype.card F : ℤ) * ∑ s : F, (if f x1 + f (x1 + s) = f y1 + f (y1 + s) then 1 else 0) := by
        intro x1 y1
        have h_inner_sum : ∑ x2 : F, ∑ y2 : F, (if x1 + y1 + x2 + y2 = 0 then (if f x1 + f y1 + f x2 + f y2 = 0 then (Fintype.card F : ℤ) else 0) else 0) = ∑ x2 : F, (if f x1 + f y1 + f x2 + f (x2 + x1 + y1) = 0 then (Fintype.card F : ℤ) else 0) := by
          refine' Finset.sum_congr rfl fun x2 _ => _;
          rw [ Finset.sum_eq_single ( x2 + x1 + y1 ) ] <;> simp +decide [ add_eq_zero_iff_eq_neg ];
          · grind;
          · grind;
        rw [ h_inner_sum, Finset.mul_sum _ _ _ ];
        refine' Finset.sum_bij ( fun x2 _ => x2 + y1 ) _ _ _ _ <;> simp +decide [ add_comm, add_left_comm, add_assoc ];
        · exact fun b => ⟨ b - y1, by ring ⟩;
        · grind;
      -- Let's simplify the expression inside the sum further.
      have h_simplify_inner_final : ∑ x1 : F, ∑ y1 : F, ∑ s : F, (if f x1 + f (x1 + s) = f y1 + f (y1 + s) then 1 else 0) = ∑ s : F, ∑ t : F, (deltaCount f s t : ℤ) ^ 2 := by
        have h_simplify_inner_final : ∀ s : F, ∑ x1 : F, ∑ y1 : F, (if f x1 + f (x1 + s) = f y1 + f (y1 + s) then 1 else 0) = ∑ t : F, (deltaCount f s t : ℤ) ^ 2 := by
          intro s
          have h_simplify_inner_final_step : ∀ x1 : F, ∑ y1 : F, (if f x1 + f (x1 + s) = f y1 + f (y1 + s) then 1 else 0) = ∑ t : F, (if f x1 + f (x1 + s) = t then (deltaCount f s t : ℤ) else 0) := by
            intro x1
            simp [deltaCount];
            simp +decide only [add_comm, eq_comm];
          rw [ Finset.sum_congr rfl fun x1 _ => h_simplify_inner_final_step x1 ];
          rw [ Finset.sum_comm ];
          simp +decide [ sq, Finset.sum_ite ];
          simp +decide [ mul_comm, deltaCount ];
          simp +decide only [add_comm];
        rw [ ← Finset.sum_congr rfl fun s hs => h_simplify_inner_final s ];
        exact Eq.symm ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm ) );
      simp_all +decide only [← sum_mul, ← Finset.mul_sum _ _ _];
      simpa only [ mul_assoc, pow_two ] using h_simplify

/-! ## Section 5: AB Fourth Moment Computation -/

/-
For AB functions with b ≠ 0: each W(a,b)² ∈ {0, 2q}, so W(a,b)⁴ = 2q · W(a,b)².
    Therefore ∑_a W(a,b)⁴ = 2q · ∑_a W(a,b)² = 2q · q² = 2q³.
-/
lemma ab_walsh_fourth_per_b (f : F → F) (hAB : IsAB f) (b : F) (hb : b ≠ 0) :
    ∑ a : F, walshTransform f a b ^ 4 = 2 * q ^ 3 := by
      have := @hAB;
      have h_sum : ∀ a : F, walshTransform f a b ^ 4 = 2 * (Fintype.card F : ℤ) * (walshTransform f a b ^ 2) := by
        intro a; specialize this a b hb; rcases this with ( h | h ) <;> simp +decide [ h ] ; ring;
        · exact eq_zero_of_pow_eq_zero h;
        · linear_combination' h * h;
      rw [ Finset.sum_congr rfl fun a _ => h_sum a, ← Finset.mul_sum _ _ _, parseval_walsh ] ; ring

/-
For AB functions, the total fourth moment is |F|³(3|F| − 2).
    This combines the b=0 contribution (|F|⁴) with the b≠0 contributions (2|F|³ each).
-/
lemma ab_total_fourth_moment (f : F → F) (hAB : IsAB f) :
    ∑ a : F, ∑ b : F, walshTransform f a b ^ 4 =
    q ^ 3 * (3 * q - 2) := by
      -- Split the sum over b into b=0 and b≠0 using Finset.sum_eq_sum_compl_add_sum or similar.
      have h_split : ∑ b : F, ∑ a : F, walshTransform f a b ^ 4 = (∑ a : F, walshTransform f a 0 ^ 4) + ∑ b ∈ Finset.univ.erase 0, ∑ a : F, walshTransform f a b ^ 4 := by
        rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ 0 ), add_comm ];
      rw [ Finset.sum_comm, h_split ];
      rw [ Finset.sum_congr rfl fun b hb => ab_walsh_fourth_per_b f hAB b ( Finset.ne_of_mem_erase hb ) ] ; ring!;
      rw [ Finset.sum_congr rfl fun x hx => by rw [ walsh_b_zero ] ] ; norm_num ; ring;
      rw [ Nat.cast_pred ( Fintype.card_pos ) ] ; ring

/-! ## Section 6: Combinatorial Lower Bound -/

/-
Sum of δ²  at a = 0 contributes |F|².
-/
lemma delta_sq_at_zero (f : F → F) :
    ∑ b : F, ((deltaCount f 0 b : ℤ) ^ 2) = q ^ 2 := by
      rw [ Finset.sum_eq_single 0 ] <;> simp +decide [ delta_at_zero ]

/-
Key lower bound: for a ≠ 0, ∑_b δ(a,b)² ≥ 2|F|.

    Proof: Since solutions pair up (delta_even), write δ(a,b) = 2·e_b.
    Then ∑ e_b = |F|/2 and each e_b ≥ 0.
    Since e² ≥ e for non-negative integers,
    ∑ δ² = 4·∑ e² ≥ 4·∑ e = 4·|F|/2 = 2|F|.
-/
lemma delta_sq_lower_bound (f : F → F) (a : F) (ha : a ≠ 0) :
    2 * q ≤ ∑ b : F, (deltaCount f a b : ℤ) ^ 2 := by
      -- For any non-negative integer $n$ with $2 \mid n$, write $n = 2m$. Then $n^2 = 4m^2 \geq 4m = 2n$ (since $m^2 \geq m$ for $m \geq 0$, as $m(m-1) \geq 0$).
      have h_even : ∀ n : ℕ, 2 ∣ n → (n : ℤ) ^ 2 ≥ 2 * (n : ℤ) := by
        rintro ( _ | _ | n ) <;> simp_all +decide [ Nat.dvd_add_right ];
        exact fun h => by nlinarith;
      exact le_trans ( by simp +decide [ ← Finset.mul_sum _ _ _, delta_sum ] ) ( Finset.sum_le_sum fun b _ => h_even _ ( delta_even f a ha b ) )

/-
When ∑_b δ(a,b)² = 2|F| with all δ even and ∑δ = |F|,
    every δ(a,b) ≤ 2.

    Proof: If some e_b ≥ 2, then e_b² ≥ 2·e_b, making ∑e² > ∑e,
    so ∑δ² > 2|F|, contradiction.
-/
lemma delta_sq_eq_implies_apn (f : F → F) (a : F) (ha : a ≠ 0)
    (heq : ∑ b : F, (deltaCount f a b : ℤ) ^ 2 = 2 * q) :
    ∀ b : F, deltaCount f a b ≤ 2 := by
      intro b
      by_contra hb_contra
      have hb_ge_two : 4 ≤ deltaCount f a b := by
        exact Nat.le_of_not_lt fun h => hb_contra <| by have := delta_even f a ha b; interval_cases deltaCount f a b ; trivial;
      have h_contradiction : ∑ b : F, ((deltaCount f a b : ℤ) ^ 2 - 2 * (deltaCount f a b : ℤ)) > 0 := by
        refine' lt_of_lt_of_le _ ( Finset.single_le_sum ( fun x _ => _ ) ( Finset.mem_univ b ) );
        · nlinarith only [ hb_ge_two ];
        · by_cases hx : deltaCount f a x ≤ 2;
          · interval_cases _ : deltaCount f a x <;> simp_all +decide;
            exact absurd ( delta_even f a ha x ) ( by simp +decide [ * ] );
          · nlinarith only [ hx ];
      simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      exact h_contradiction.ne ( mod_cast delta_sum f a )

/-! ## Section 7: Main Theorem — AB implies APN -/

/-
**Almost Bent implies Almost Perfect Nonlinear** (Chabaud-Vaudenay 1994).

    For any function f : F → F over a finite field of characteristic 2,
    if f is AB then f is APN.

    The proof combines the global fourth moment identity with the
    combinatorial lower bound. From the AB condition, we compute
    ∑_{a,b} δ² = 3|F|² − 2|F|. Subtracting the a=0 contribution (|F|²),
    we get ∑_{a≠0} ∑_b δ² = 2|F|² − 2|F| = 2|F|(|F|−1).
    Since there are |F|−1 nonzero values of a and each inner sum is ≥ 2|F|,
    the only possibility is that each inner sum equals exactly 2|F|.
    This forces δ(a,b) ∈ {0, 2} for all b, i.e., f is APN.
-/
theorem ab_implies_apn (f : F → F) (hAB : IsAB f) : IsAPN f := by
  -- From the AB condition, we have ∑_{a,b} δ² = 3|F|² − 2|F|.
  have h_sum : ∑ a : F, ∑ b : F, (deltaCount f a b : ℤ) ^ 2 = 3 * (Fintype.card F : ℤ) ^ 2 - 2 * (Fintype.card F : ℤ) := by
    have := ab_total_fourth_moment f hAB;
    rw [ fourth_moment_identity ] at this;
    exact mul_left_cancel₀ ( pow_ne_zero 2 ( Nat.cast_ne_zero.mpr Fintype.card_ne_zero ) ) ( by linarith );
  -- Split off a=0:
  have h_split : ∑ a ∈ Finset.univ.erase 0, ∑ b : F, (deltaCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) := by
    rw [ Finset.sum_erase_eq_sub ( Finset.mem_univ 0 ) ] ; rw [ delta_sq_at_zero ] at * ; linarith;
  -- For each a ≠ 0, delta_sq_lower_bound gives ∑_b δ(a,b)² ≥ 2q.
  have h_lower_bound : ∀ a ∈ Finset.univ.erase 0, ∑ b : F, (deltaCount f a b : ℤ) ^ 2 = 2 * (Fintype.card F : ℤ) := by
    have h_lower_bound : ∀ a ∈ Finset.univ.erase 0, ∑ b : F, (deltaCount f a b : ℤ) ^ 2 ≥ 2 * (Fintype.card F : ℤ) := by
      exact fun a ha => delta_sq_lower_bound f a ( Finset.ne_of_mem_erase ha );
    contrapose! h_split;
    refine' ne_of_gt ( lt_of_le_of_lt _ ( Finset.sum_lt_sum _ _ ) );
    rotate_left;
    use fun a => 2 * ( Fintype.card F : ℤ );
    · exact h_lower_bound;
    · exact ⟨ h_split.choose, h_split.choose_spec.1, lt_of_le_of_ne ( h_lower_bound _ h_split.choose_spec.1 ) h_split.choose_spec.2.symm ⟩;
    · simp +decide [ mul_comm ];
      rw [ Nat.cast_pred ( Fintype.card_pos ) ] ; linarith;
  exact fun a ha b => delta_sq_eq_implies_apn f a ha ( h_lower_bound a ( Finset.mem_erase_of_ne_of_mem ha ( Finset.mem_univ a ) ) ) b

/-! ## Section 8: Kasami Functions -/

/-- **Kasami functions are Almost Bent** (Kasami 1971, Dillon-Dobbertin 1999).

    The function f(x) = x^{2^{2k} − 2^k + 1} on GF(2^{2k+1}) is AB.
    This is a deep number-theoretic result whose proof involves the
    computation of cross-correlation functions of m-sequences and
    explicit evaluation of character sums over finite fields.

    The original APN property was shown by Kasami (1971) through
    weight distribution analysis. The stronger AB property was
    established by Dillon and Dobbertin (1999). -/
theorem kasami_is_ab (k : ℕ) (hk : k ≥ 1)
    (hcard : Fintype.card F = 2 ^ (2 * k + 1)) :
    IsAB (kasamiFunction k : F → F) := by sorry

/-- **Kasami functions are APN**: immediate from `ab_implies_apn` and `kasami_is_ab`. -/
theorem kasami_is_apn (k : ℕ) (hk : k ≥ 1)
    (hcard : Fintype.card F = 2 ^ (2 * k + 1)) :
    IsAPN (kasamiFunction k : F → F) :=
  ab_implies_apn _ (kasami_is_ab k hk hcard)
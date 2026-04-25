/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Walsh Transform — Properties

This module develops the theory of the Walsh–Hadamard transform over `GF(2)^n`
and proves key identities used in the analysis of APN and AB functions.

## Main Results

* `APN.signF2_sq` — `signF2(x)^2 = 1`
* `APN.walshCoeff_zero_zero` — `W_F(0, 0) = 2^n`
* `APN.parseval_bool` — Parseval's identity: `∑_a W_f(a)^2 = 2^(2n)`
* `APN.parseval_vectorial` — `∑_a W_F(a,b)^2 = 2^(2n)` for any fixed `b`
* `APN.character_sum_zero` — character orthogonality
-/

import RequestProject.APN.Defs

open Finset BigOperators

namespace APN

/-! ### Properties of `signF2` -/

@[simp]
theorem signF2_zero : signF2 0 = 1 := by
  simp [signF2]

@[simp]
theorem signF2_one : signF2 1 = -1 := by
  simp [signF2]

theorem signF2_sq (x : ZMod 2) : signF2 x ^ 2 = 1 := by
  native_decide +revert

theorem signF2_mul (x y : ZMod 2) : signF2 x * signF2 y = signF2 (x + y) := by
  native_decide +revert

theorem signF2_abs (x : ZMod 2) : |signF2 x| = 1 := by
  native_decide +revert

theorem signF2_ne_zero (x : ZMod 2) : signF2 x ≠ 0 := by
  native_decide +revert

/-! ### Walsh coefficient at zero -/

theorem walshCoeff_zero_zero {n : ℕ}
    (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) :
    walshCoeff F 0 0 = 2 ^ n := by
  unfold walshCoeff
  unfold innerProductF2; aesop

/-- For `b = 0`, the Walsh coefficient `W_F(a, 0)` counts a character sum. -/
theorem walshCoeff_b_zero {n : ℕ}
    (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    walshCoeff F a 0 = ∑ x : Fin n → ZMod 2, signF2 (innerProductF2 a x) := by
  exact Finset.sum_congr rfl fun _ _ => by
    rw [show innerProductF2 0 (F _) = 0 by exact Finset.sum_eq_zero fun _ _ => by simp +decide]
    simp +decide [signF2]

/-! ### Inner product properties -/

theorem innerProductF2_zero_left {n : ℕ} (x : Fin n → ZMod 2) :
    innerProductF2 0 x = 0 := by
  simp [innerProductF2]

theorem innerProductF2_zero_right {n : ℕ} (x : Fin n → ZMod 2) :
    innerProductF2 x 0 = 0 := by
  exact Finset.sum_eq_zero fun i _ => mul_zero _

theorem innerProductF2_add_left {n : ℕ} (a b x : Fin n → ZMod 2) :
    innerProductF2 (a + b) x = innerProductF2 a x + innerProductF2 b x := by
  unfold innerProductF2
  simp +decide [add_mul, Finset.sum_add_distrib]

theorem innerProductF2_comm {n : ℕ} (a b : Fin n → ZMod 2) :
    innerProductF2 a b = innerProductF2 b a := by
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-! ### Character orthogonality -/

/-- Character orthogonality for GF(2)^n: for `v ≠ 0`, `∑_a (-1)^{⟨a,v⟩} = 0`. -/
theorem character_sum_zero {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) :
    ∑ a : Fin n → ZMod 2, signF2 (innerProductF2 a v) = 0 := by
  set S := ∑ x : Fin n → ZMod 2, (-1 : ℤ) ^ (innerProductF2 x v).val
  have h_sum : S = ∏ i : Fin n, (∑ x : ZMod 2, (-1 : ℤ) ^ (x.val * v i).val) := by
    rw [Finset.prod_sum]
    refine' Finset.sum_bij (fun x _ => fun i _ => x i) _ _ _ _ <;> simp +decide
    · simp +decide [funext_iff]
    · exact fun b => ⟨fun i => b i (Finset.mem_univ i), rfl⟩
    · intro a; rw [Finset.prod_pow_eq_pow_sum]
      rw [← Nat.mod_add_div (∑ i, (a i * v i).val) 2]
      norm_num [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
      unfold innerProductF2
      rw [← ZMod.val_natCast]
      simp +decide [ZMod.val_add, ZMod.val_mul]
  obtain ⟨i, hi⟩ : ∃ i : Fin n, v i = 1 := by
    exact Function.ne_iff.mp hv |> Exists.imp fun i hi => by
      have := Fin.exists_fin_two.mp ⟨v i, rfl⟩; aesop
  convert h_sum using 1
  · exact Finset.sum_congr rfl fun x hx => by
      unfold signF2; rcases h : innerProductF2 x v with (_ | _ | k) <;> trivial
  · rw [Finset.prod_eq_zero (Finset.mem_univ i)]; aesop

/-- For `v = 0`, `∑_a (-1)^{⟨a,v⟩} = 2^n`. -/
theorem character_sum_eq_pow {n : ℕ} :
    ∑ a : Fin n → ZMod 2, signF2 (innerProductF2 a (0 : Fin n → ZMod 2)) = 2 ^ n := by
  rw [Finset.sum_congr rfl fun x hx => by rw [innerProductF2_zero_right]]
  simp +decide [signF2]

/-! ### Parseval's identity -/

/-- **Parseval's identity** for boolean functions:
    `∑_a W_f(a)^2 = 2^(2n)` = `|GF(2)^n|^2`. -/
theorem parseval_bool {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) :
    ∑ a : Fin n → ZMod 2, walshHadamard f a ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  have h_fubini : ∑ a : Fin n → ZMod 2,
      (∑ x : Fin n → ZMod 2, signF2 (f x + innerProductF2 a x)) ^ 2 =
      ∑ x : Fin n → ZMod 2, ∑ y : Fin n → ZMod 2,
      ∑ a : Fin n → ZMod 2,
        signF2 (f x + innerProductF2 a x) * signF2 (f y + innerProductF2 a y) := by
    simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  have h_inner : ∀ x y : Fin n → ZMod 2, x ≠ y →
      ∑ a : Fin n → ZMod 2,
        signF2 (f x + innerProductF2 a x) * signF2 (f y + innerProductF2 a y) = 0 := by
    have h_inner_simplified : ∀ x y : Fin n → ZMod 2, x ≠ y →
        ∑ a : Fin n → ZMod 2, signF2 (innerProductF2 a (x - y)) = 0 := by
      intros x y hxy
      have h_inner_sum : ∑ a : Fin n → ZMod 2, signF2 (innerProductF2 a (x - y)) =
          ∏ i : Fin n, (∑ a_i : ZMod 2, signF2 (a_i * (x - y) i)) := by
        rw [Finset.prod_sum]
        refine' Finset.sum_bij (fun a _ => fun i _ => a i) _ _ _ _ <;> simp +decide
        · simp +decide [funext_iff]
        · exact fun b => ⟨fun i => b i (Finset.mem_univ i), rfl⟩
        · intro a; rw [show innerProductF2 a (x - y) = ∑ i, a i * (x i - y i) by rfl]
          induction' (Finset.univ : Finset (Fin n)) using Finset.induction <;>
            simp_all +decide [Finset.prod_insert, Finset.sum_insert]
          rw [← ‹signF2 (∑ i ∈ _, a i * (x i - y i)) =
            ∏ i ∈ _, signF2 (a i * (x i - y i))›, signF2_mul]
      obtain ⟨i, hi⟩ : ∃ i : Fin n, (x - y) i ≠ 0 := by
        exact Function.ne_iff.mp (sub_ne_zero.mpr hxy)
      rw [h_inner_sum, Finset.prod_eq_zero (Finset.mem_univ i)]
      cases Fin.exists_fin_two.mp ⟨(x - y) i, rfl⟩ <;> simp_all +decide
    intros x y hxy
    have h_inner_eq : ∀ a : Fin n → ZMod 2,
        signF2 (f x + innerProductF2 a x) * signF2 (f y + innerProductF2 a y) =
        signF2 (f x + f y + innerProductF2 a (x - y)) := by
      intros a
      simp [signF2_mul, innerProductF2]
      simp +decide [mul_sub, add_assoc, add_left_comm, Finset.sum_add_distrib]
      grind
    simp_all +decide [signF2_mul]
    convert congr_arg (fun z => z * signF2 (f x + f y))
      (h_inner_simplified x y hxy) using 1 <;> ring
    rw [Finset.sum_mul _ _ _]; congr; ext; rw [← signF2_mul]; ring
  convert h_fubini using 1
  rw [Finset.sum_congr rfl fun x hx =>
    Finset.sum_eq_single x (fun y hy => by by_cases h : x = y <;> aesop) (by aesop)]
  simp +decide [← sq, signF2_sq]

/-- **Parseval's identity** for vectorial functions:
    For any fixed `b`, `∑_a W_F(a, b)^2 = |GF(2)^n|^2 = 2^(2n)`. -/
theorem parseval_vectorial {n : ℕ}
    (F : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (b : Fin n → ZMod 2) :
    ∑ a : Fin n → ZMod 2, walshCoeff F a b ^ 2 = (2 ^ n : ℤ) ^ 2 := by
  convert parseval_bool (componentFunction F b) using 1

end APN

/-
  Foundations, Layer 2 — exponent arithmetic for the Kasami exponent.

  Integrated from `dobbertin-kasami-power.zip`.  Grounded in Mathlib's
  `Nat`/`ZMod` API; everything is proved.
-/
import Mathlib
import RequestProject.DobbertinKasami.Blueprint

open scoped BigOperators

namespace DobbertinKasami

variable {n : ℕ}

/-- The value of the Kasami exponent `d = 2^{2k} − 2^k + 1`. -/
lemma kasamiExp_eq (k : ℕ) : kasamiExp k = 2 ^ (2 * k) - 2 ^ k + 1 := rfl

/-- **gcd identity** `gcd(2^k − 1, 2^n − 1) = 2^{gcd(k,n)} − 1`
(a classical fact about repunits in base 2; Mathlib:
`Nat.pow_sub_one_gcd_pow_sub_one`). -/
lemma gcd_pow_two_sub_one (k m : ℕ) :
    Nat.gcd (2 ^ k - 1) (2 ^ m - 1) = 2 ^ (Nat.gcd k m) - 1 :=
  Nat.pow_sub_one_gcd_pow_sub_one 2 k m

/-- If `gcd(k,n) = 1` then `2^k − 1` and `2^n − 1` are **coprime**; hence the
inverse `(2^k − 1)⁻¹ (mod 2^n − 1)` used in the proof of Theorem 1 exists. -/
lemma coprime_pow_two_sub_one {k m : ℕ} (h : Nat.Coprime k m) :
    Nat.Coprime (2 ^ k - 1) (2 ^ m - 1) := by
  simp +decide [ *, Nat.Coprime ]

/-- Since `gcd(k,n) = 1`, `k` is a **unit mod n**, so `k' ≡ k⁻¹ (mod n)` exists:
`k · k⁻¹ = 1` in `ZMod n`. -/
lemma coe_mul_inv_of_coprime {k m : ℕ} [NeZero m] (h : Nat.Coprime k m) :
    (k : ZMod m) * (k : ZMod m)⁻¹ = 1 := by
  rw [ ZMod.mul_inv_eq_gcd ];
  rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ]

/-- Two coprime naturals are **not both even** — this is why a generalized Kasami
permutation polynomial always exists (`k'` and `n` cannot both be even). -/
lemma not_both_even_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    ¬ (2 ∣ a ∧ 2 ∣ b) := by
  exact fun h' => by have := Nat.dvd_gcd h'.1 h'.2; simp_all +decide ;

end DobbertinKasami

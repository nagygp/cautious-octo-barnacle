/-
  Theorem 1 and Corollary 2 of

    Hans Dobbertin, "Kasami Power Functions, Permutation Polynomials and
    Cyclic Difference Sets" (Kluwer, 1999), §2.

  This file states the two headline results **faithfully** against the genuine
  definitions in `KasamiPoly.lean` and records the proof decomposition.  The
  elementary pieces are discharged; the genuinely new algebraic core (the
  linearized-polynomial root count of Dobbertin's proof) is isolated as a single
  named `sorry` leaf, `genKasami_injective_of_odd`.

  See `Docs/DobbertinTheorem1Assessment.md` for the module-readiness assessment
  that this file accompanies.
-/
import Mathlib
import RequestProject.DobbertinKasami.Blueprint
import RequestProject.DobbertinKasami.Foundations.Trace
import RequestProject.DobbertinKasami.Foundations.Exponent
import RequestProject.DobbertinKasami.KasamiPoly

open scoped BigOperators

namespace DobbertinKasami

variable {n : ℕ}

/-- On a finite type, a self-map is a permutation iff it is injective. -/
theorem isPermutation_iff_injective {F : Type*} [Finite F] (f : F → F) :
    IsPermutation f ↔ Function.Injective f := by
  constructor
  · exact fun h => h.injective
  · exact fun h => (Finite.injective_iff_bijective).1 h

/-! ## Theorem 1, "only if" direction (elementary) -/

/-
**Theorem 1, "only if".**  If `q_α` is a permutation then `k' + α·n` is odd.
The contrapositive is the computation `q_α(1) = k' + α·Tr(1) = 0 = q_α(0)`
(Dobbertin's one-line observation): if `k' + α·n ≡ 0`, then `q_α` sends both `0`
and `1` to `0`, so it is not injective.
-/
theorem genKasami_permutation_only_if (hn : n ≠ 0) (k kp : ℕ) (α : ZMod 2)
    (h : IsPermutation (genKasami (n := n) k kp α)) :
    (kp : ZMod 2) + α * (n : ZMod 2) = 1 := by
  by_contra h_contra;
  obtain ⟨x, hx⟩ : ∃ x : Lfield n, genKasami (n := n) k kp α x = genKasami (n := n) k kp α 1 ∧ x ≠ 1 := by
    use 0; simp_all +decide [ genKasami_zero, genKasami_one ] ;
    convert ( show ( 0 : Lfield n ) = algebraMap ( ZMod 2 ) ( Lfield n ) ( ( kp : ZMod 2 ) + α * ( n : ZMod 2 ) ) from ?_ ) using 1;
    · simp +decide [ map_add, map_mul ];
    · cases Fin.exists_fin_two.mp ⟨ kp + α * n, rfl ⟩ <;> aesop;
  exact hx.2 ( h.injective hx.1 )

/-! ## Theorem 1, "if" direction

The hard direction.  Dobbertin shows that for each fixed `c ∈ L`, the equation
`(1)  c·x^{2^k+1} = ∑_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)`
has **at most one** solution, whence `q_α` is injective, hence (finite field) a
permutation.  The core argument passes to the linearized polynomial
`ℓ(x) = c^{2^k}·x^{2^{2k}} + x^{2^k} + c·x + 1`, whose homogeneous part is an
`𝔽₂`-linear map with kernel of dimension ≤ 2, and splits into

* **Case 1** `c ∉ {γ^{2^k+1}+γ}` : `ℓ` has a unique root;
* **Case 2** `c = γ^{2^k+1}+γ` : `ℓ` has two or four roots, of which exactly one
  solves (1) (via the auxiliary quantities `Δ, λ, μ` of eqns (3)–(7)).

All the Mathlib primitives needed for this (Frobenius `𝔽₂`-linearity, finite
kernels/`Module.finrank`, `Finite.injective_iff_bijective`, the trace API in
`Foundations/Trace.lean`) are available; the transcription of this root count is
the single remaining mathematical input. -/

/-- **Core algebraic input of Theorem 1 (the "if" direction).**  When
`k' + α·n` is odd, the generalized Kasami map `q_α` is injective.  This isolates
Dobbertin's linearized-polynomial root count (Cases 1 & 2 of the proof). -/
theorem genKasami_injective_of_odd (hn : n ≠ 0) (k kp : ℕ) (hk_lt : k < n)
    (hcop : Nat.Coprime k n) (hkp : (k * kp) % n = 1) (α : ZMod 2)
    (hodd : (kp : ZMod 2) + α * (n : ZMod 2) = 1) :
    Function.Injective (genKasami (n := n) k kp α) := by
  sorry

/-! ## Theorem 1 (full statement) -/

/-- **Theorem 1 (Dobbertin).**  A generalized Kasami polynomial `q_α` is a
permutation polynomial on `L = 𝔽_{2ⁿ}` if and only if `k' + α·n ≡ 1 (mod 2)`.
Here `kp = k'` is a natural-number representative of `k⁻¹ (mod n)`. -/
theorem theorem_1 (hn : n ≠ 0) (k kp : ℕ) (hk_lt : k < n)
    (hcop : Nat.Coprime k n) (hkp : (k * kp) % n = 1) (α : ZMod 2) :
    IsPermutation (genKasami (n := n) k kp α) ↔
      (kp : ZMod 2) + α * (n : ZMod 2) = 1 := by
  rw [isPermutation_iff_injective]
  constructor
  · intro h
    exact genKasami_permutation_only_if hn k kp α ((isPermutation_iff_injective _).2 h)
  · intro hodd
    exact genKasami_injective_of_odd hn k kp hk_lt hcop hkp α hodd

/-! ## Corollary 2

Kasami power functions are APN.  Dobbertin's proof: pick `α` so that `q := q_α`
is a permutation (possible since `k'` and `n` are not both even), then the
"routine computation" gives `p(t) := (t+1)^d + t^d + 1 = (1/c)·q(t^{2^k}+t)`,
and `t ↦ t^{2^k}+t` is two-to-one (as `gcd(k,n)=1`); a permutation precomposed
with a two-to-one map is two-to-one, i.e. `x ↦ x^d` is APN.

The APN *conclusion* for the regime `n` odd is **already proved from first
principles** elsewhere in this project as `Kasami.Headlines.kasami_is_apn`
(via the equivalent Dempwolff–Müller MCM permutation input `theorem_3_2`); the
statement below is the faithful all-`n` form against `DobbertinKasami.IsAPN`. -/

/-- **Corollary 2 (Dobbertin).**  Kasami power functions `x ↦ x^d`,
`d = 2^{2k} − 2^k + 1`, are almost perfect nonlinear on `L = 𝔽_{2ⁿ}`. -/
theorem corollary_2 (hn : n ≠ 0) (k : ℕ) (hk : 0 < k) (hk_lt : k < n)
    (hcop : Nat.Coprime k n) :
    IsAPN (fun x : Lfield n => x ^ kasamiExp k) := by
  sorry

end DobbertinKasami
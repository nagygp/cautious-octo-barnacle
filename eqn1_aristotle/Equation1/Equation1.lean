import Dobbertin1999MVP.Equation1.Defs
import Dobbertin1999MVP.Equation1.Setup
import Dobbertin1999MVP.Equation1.FiniteFieldPrereqs
import Dobbertin1999MVP.Equation1.Theorem5
import Dobbertin1999MVP.Equation1.Theorem8Trace
import Dobbertin1999MVP.Equation1.Theorem8C1
import Dobbertin1999MVP.Equation1.Q1General
import Dobbertin1999MVP.Equation1.Equation1

/-!
# Equation (1) of Theorem 1's proof — self-contained MVP (entry point)

This folder is a **self-contained extract** of the `RequestProject`/`Dobbertin1999MVP`
development carrying exactly the material needed, end to end from first principles
(`Mathlib` only), for **equation (1)** in the proof of Dobbertin's *Theorem 1*
(Dobbertin 1999, pp. 135–136):
```
   c·x^{2^k+1} = Σ_{i=1}^{k'} x^{2^{ik}} + α·Tr(x)                     (1)
```

## Module layout

* `Equation1/Defs.lean` — the pure definitions (`Tr`, `qKasami` = `q_α`, `eqn1`,
  `ell`, `ell0`, `Qmap`); depends only on `Mathlib`.
* `Equation1/Setup.lean` — the **elementary opening** of the proof, *before*
  equations (1)/(2), engine-free (`Mathlib` + `Defs` only):
    * `mersenne_coprime` / `inv_mod_exists` — `(2^k − 1)⁻¹ (mod 2ⁿ−1)` exists
      when `gcd(k, n) = 1`;
    * `qKasami_zero` — `q_α(0) = 0` (the `0/0 = 0` convention);
    * `Tr_one`, `qKasami_one` — `Tr(1) = n`, `q_α(1) = k' + α·n`;
    * `qKasami_one_eq_zero_iff` — the **"only if"** part `q_α(1) = 0 ↔ k'+α·n even`.
* `Equation1/FiniteFieldPrereqs.lean` — the minimal `DempwolffMueller` finite-field
  lemmas on the dependency path (Frobenius + truncated trace).
* `Equation1/Theorem5.lean`, `Theorem8Trace.lean`, `Theorem8C1.lean`,
  `Q1General.lean` — the minimal library lemmas from `Theorem5`, `Theorem8`,
  `Theorem8C1`, `Q1General` used by the equation-(1) argument (only the ones on
  the dependency path are retained).
* `Equation1/Equation1.lean` — the equation-(1) thread itself: `theorem_1`, the
  first substantive step `eqn2_of_eqn1` ((1) ⟹ (2)), and the two cases
  `theorem_1_case1` / `ell_eq_Q` / `theorem_1_case2` showing (1) has at most one
  (nonzero) solution.

Every declaration is `sorry`-free and rests only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Dobbertin1999.Equation1.Headlines

/-- Equation (1): `q_α(x) = c` cleared of denominators. -/
alias eqn1 := Dobbertin1999.Paper.eqn1

/-- `(2^k − 1)⁻¹ (mod 2ⁿ−1)` exists when `gcd(k, n) = 1`. -/
alias inv_mod_exists := Dobbertin1999.Paper.inv_mod_exists

/-- `q_α(0) = 0` (the `0/0 = 0` convention). -/
alias qKasami_zero := Dobbertin1999.Paper.qKasami_zero

/-- The "only if" part: `q_α(1) = 0 ↔ k' + α·n ≡ 0 (mod 2)`. -/
alias qKasami_one_eq_zero_iff := Dobbertin1999.Paper.qKasami_one_eq_zero_iff

/-- Theorem 1: `q_α` is a permutation of `L` iff `k' + α·n ≡ 1 (mod 2)`. -/
alias theorem_1 := Dobbertin1999.Paper.theorem_1

/-- The first substantive step of the proof: (1) ⟹ (2), i.e. `ℓ(x) = 0`. -/
alias eqn2_of_eqn1 := Dobbertin1999.Paper.eqn2_of_eqn1

/-- Case 1 of the "if" part: `ℓ(x) = 0` has exactly one solution. -/
alias theorem_1_case1 := Dobbertin1999.Paper.theorem_1_case1

/-- Case 2 of the "if" part: exactly one nonzero solution of equation (1). -/
alias theorem_1_case2 := Dobbertin1999.Paper.theorem_1_case2

end Dobbertin1999.Equation1.Headlines

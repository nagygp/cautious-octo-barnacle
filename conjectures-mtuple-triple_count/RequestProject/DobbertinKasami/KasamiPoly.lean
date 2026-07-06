/-
  Layer 5 — genuine definitions of the generalized Kasami polynomial `q_α`
  and generalized MCM polynomial `P_β`, transcribed from the display formulae
  recovered in `TRANSCRIPTION_OCR.md` (shipped with `dobbertin-kasami-power.zip`):

    * `P_β(z) = (∑_{i=0}^{k-1} z^{2^i} + β·Tr z)^{2^k+1} / z^{2^k}`
    * `q_α(x) = (∑_{i=1}^{k'} x^{2^{ik}} + α·Tr x) / x^{2^k+1}`

  The paper's substitution `1/z^{m} ↦ z^{(2ⁿ−1)−m}` (which turns these quotients
  into genuine polynomials) is realised here directly via the field inverse
  `(·)⁻¹`, using Lean's `0⁻¹ = 0` convention — exactly Dobbertin's `0/0 = 0`
  convention, and agreeing with the substitution for all `z ≠ 0`.
-/
import Mathlib
import RequestProject.DobbertinKasami.Blueprint
import RequestProject.DobbertinKasami.Foundations.Trace

open scoped BigOperators

namespace DobbertinKasami

variable {n : ℕ}

/-- The `𝔽₂`-element `β·Tr(z)` embedded into `L = 𝔽_{2ⁿ}`. -/
noncomputable def traceTerm (b : ZMod 2) (z : Lfield n) : Lfield n :=
  algebraMap (ZMod 2) (Lfield n) (b * Tr n z)

/-- **Generalized MCM polynomial** `P_β`:
`P_β(z) = (∑_{i=0}^{k-1} z^{2^i} + β·Tr z)^{2^k+1} / z^{2^k}`. -/
noncomputable def genMCM (k : ℕ) (β : ZMod 2) (z : Lfield n) : Lfield n :=
  (∑ i ∈ Finset.range k, z ^ (2 ^ i) + traceTerm β z) ^ (2 ^ k + 1) * (z ^ (2 ^ k))⁻¹

/-- **Generalized Kasami polynomial** `q_α`:
`q_α(x) = (∑_{i=1}^{k'} x^{2^{ik}} + α·Tr x) / x^{2^k+1}`.
Here `kp = k'` is the chosen natural-number representative of `k⁻¹ (mod n)`. -/
noncomputable def genKasami (k kp : ℕ) (α : ZMod 2) (x : Lfield n) : Lfield n :=
  (∑ i ∈ Finset.range kp, x ^ (2 ^ ((i + 1) * k)) + traceTerm α x) * (x ^ (2 ^ k + 1))⁻¹

/-- `traceTerm b 0 = 0`. -/
@[simp] lemma traceTerm_zero (b : ZMod 2) : traceTerm b (0 : Lfield n) = 0 := by
  simp [traceTerm]

/-- **`q_α(0) = 0`** (Dobbertin's `0/0 = 0` convention). -/
@[simp] lemma genKasami_zero (k kp : ℕ) (α : ZMod 2) :
    genKasami (n := n) k kp α 0 = 0 := by
  unfold genKasami;
  cases k <;> cases kp <;> simp_all +decide

/-- **`P_β(0) = 0`**. -/
@[simp] lemma genMCM_zero (k : ℕ) (β : ZMod 2) :
    genMCM (n := n) k β 0 = 0 := by
  by_cases hk : k = 0 <;> simp_all +decide [ genMCM ]

/-- **`q_α(1) = k' + α·Tr(1)`** as an element of `L` (Theorem 1's "only if"
computation): `q_α(1) = (kp : L) + α·(n mod 2)`. -/
lemma genKasami_one (hn : n ≠ 0) (k kp : ℕ) (α : ZMod 2) :
    genKasami (n := n) k kp α 1 =
      (kp : Lfield n) + algebraMap (ZMod 2) (Lfield n) (α * (n : ZMod 2)) := by
  unfold genKasami;
  simp +decide [ traceTerm, Tr_one hn ]

end DobbertinKasami

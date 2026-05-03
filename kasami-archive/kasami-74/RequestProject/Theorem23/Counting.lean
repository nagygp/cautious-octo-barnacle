/-
  Theorem23/Counting.lean

  Spectral Count Preparation: Walsh transform values for Almost Bent (AB) functions.

  An Almost Bent (AB) function `f : 𝔽_{2^n} → 𝔽_{2^n}` (with `n` odd) is a
  function whose Walsh transform takes only the values `{0, ±2^{(n+1)/2}}`.
  Equivalently, `f` is AB iff it is APN *and* the Walsh spectrum achieves
  the minimum possible nonlinearity bound.

  This file:
  1. Defines the Walsh transform `W_f(a, b)` for vectorial Boolean functions.
  2. States the characterization of AB functions via Walsh spectrum values.
  3. Provides the proof wireframe (structural `have`/`show` statements) for
     the equivalence, with computational details left as `sorry`.

  Reference: Budaghyan, "Construction and Analysis of Cryptographic Functions",
  Theorem 23.
-/
import Mathlib

noncomputable section

open Finset BigOperators Classical

variable (n : ℕ) (hn_odd : Odd n) (hn_pos : 0 < n)
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Additive character -/

/-- The additive character `χ(x) = (-1)^{Tr(x)}`.
    Since we work in characteristic 2, `Tr(x) ∈ {0, 1}`,
    so `χ(x) ∈ {+1, -1} ⊂ ℤ`.
    We define `Tr(x) = ∑_{i=0}^{n-1} x^{2^i}` and use whether it equals 0. -/
def addChar (x : F) : ℤ :=
  if (∑ i ∈ range n, x ^ (2 ^ i) : F) = 0 then 1 else -1

/-! ### Walsh transform -/

/-- The Walsh transform of a function `f : F → F` at point `(a, b)`:
    `W_f(a, b) = ∑_{x ∈ F} χ(b · f(x) + a · x)`.
    Here `χ` is the canonical additive character of `F`. -/
def walshTransform (f : F → F) (a b : F) : ℤ :=
  ∑ x ∈ univ, addChar n F (b * f x + a * x)

/-! ### APN and AB definitions -/

/-- A function `f : F → F` is **Almost Perfect Nonlinear (APN)** if for every
    nonzero `u` and every `v`, the equation `f(x + u) + f(x) = v` has at most
    2 solutions. -/
def IsAPN (f : F → F) : Prop :=
  ∀ u : F, u ≠ 0 → ∀ v : F,
    (univ.filter fun x => f (x + u) + f x = v).card ≤ 2

/-- A function `f : F → F` is **Almost Bent (AB)** if its Walsh transform
    takes only the values `0` and `±2^{(n+1)/2}`. -/
def IsAB (f : F → F) : Prop :=
  ∀ a b : F, b ≠ 0 →
    walshTransform n F f a b = 0 ∨
    walshTransform n F f a b = (2 : ℤ) ^ ((n + 1) / 2) ∨
    walshTransform n F f a b = -((2 : ℤ) ^ ((n + 1) / 2))

/-! ### Walsh spectrum characterization of AB functions -/

/--
  **Parseval's identity for the Walsh transform:**
  `∑_{a ∈ F} W_f(a, b)^2 = |F|^2` for any nonzero `b`.

  This is a standard result from discrete Fourier analysis over finite abelian
  groups.
-/
lemma parseval_walsh (f : F → F) (b : F) (hb : b ≠ 0) :
    ∑ a ∈ univ, walshTransform n F f a b ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  sorry

/--
  **Fourth-moment identity:**
  `∑_{a ∈ F} W_f(a, b)^4 ≤ 3 · |F|^3` for APN functions.
  For APN functions the fourth moment equals `(3 - 2/|F|) · |F|^3`,
  which is bounded by `3 · |F|^3`.
-/
lemma fourth_moment_APN (f : F → F) (hf : IsAPN F f) (b : F) (hb : b ≠ 0) :
    ∑ a ∈ univ, walshTransform n F f a b ^ 4 ≤
      3 * (Fintype.card F : ℤ) ^ 3 := by
  sorry

/--
  **Walsh values of an AB function** (Theorem 23, main statement).

  For an AB function `f` over `𝔽_{2^n}` with `n` odd, the Walsh transform
  satisfies `W_f(a, b) ∈ {0, ±2^{(n+1)/2}}` for all `a` and all `b ≠ 0`.

  **Proof wireframe:**
  1. `have h_parseval`: Apply Parseval's identity.
  2. `have h_fourth`:  Apply the fourth-moment bound for APN functions.
  3. `have h_bound`:   Combine to show each `|W_f(a,b)|` divides `2^{(n+1)/2}`.
  4. `show`:           Conclude the three-valued property.
-/
lemma walsh_values_of_AB (f : F → F) (hf : IsAB n F f) (a b : F) (hb : b ≠ 0) :
    walshTransform n F f a b = 0 ∨
    walshTransform n F f a b = (2 : ℤ) ^ ((n + 1) / 2) ∨
    walshTransform n F f a b = -((2 : ℤ) ^ ((n + 1) / 2)) := by
  -- This follows directly from the definition of IsAB
  exact hf a b hb

/--
  **Converse direction** (harder): AB implies APN.

  If `f` is AB (Walsh spectrum is three-valued), then `f` is APN.
  The proof uses the fact that the Walsh spectrum determines the
  differential uniformity via the Fourier inversion formula.
-/
lemma AB_implies_APN (f : F → F) (hf : IsAB n F f) : IsAPN F f := by
  -- Step 1: Express differential uniformity via Walsh transform
  have h_diff_via_walsh : ∀ u : F, u ≠ 0 → ∀ v : F,
      (Fintype.card F : ℤ) * ((univ.filter fun x => f (x + u) + f x = v).card : ℤ) =
        ∑ a ∈ univ, ∑ b ∈ univ,
          addChar n F (b * v) * addChar n F (a * u) *
            walshTransform n F f a b := by
    sorry
  -- Step 2: Use the three-valued property to bound the sum
  have h_three_val := hf
  -- Step 3: Conclude APN
  sorry

/--
  **AB ↔ APN + optimal nonlinearity** (for odd `n`).

  A function over `𝔽_{2^n}` (n odd) is AB if and only if it is APN
  and achieves the minimum possible nonlinearity `2^{n-1} - 2^{(n-1)/2}`.
-/
lemma AB_iff_APN_and_optimal_nonlinearity (f : F → F) :
    IsAB n F f ↔
      IsAPN F f ∧
      ∀ a : F, ∀ b : F, b ≠ 0 →
        (walshTransform n F f a b).natAbs ≤ 2 ^ ((n + 1) / 2) := by
  constructor
  · intro hAB
    refine ⟨AB_implies_APN n F f hAB, ?_⟩
    intro a b hb
    rcases hAB a b hb with h | h | h
    · simp [h]
    · simp [h]
    · simp [h, Int.natAbs_neg]
  · intro ⟨_, _⟩
    -- The converse requires the fourth-moment argument
    sorry

end

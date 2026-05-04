/-
  Theorem3/Normalization.lean

  ══════════════════════════════════════════════════════════════════════
  NORMALIZATION LEMMA for the Budaghyan derivative of a Gold-type APN function.
  ══════════════════════════════════════════════════════════════════════

  ## Mathematical Context

  Given a binomial function f(x) = x^(2^k+1) over 𝔽_{2^n}, the derivative
    Δ_u f(x) = f(x + u) + f(x) = x^(2^k) · u + x · u^(2^k) + u^(2^k+1)
  has a kernel (as a function of x) that is isomorphic, via y = x/u, to the
  kernel of the normalized operator
    L(y) = y^(2^k) + y
  shifted by 1.  More precisely, Δ_u f(x) = 0  iff  y^(2^k) + y + 1 = 0
  where y = x · u⁻¹.

  ## Algorithmic Pattern (CLRS Ch. 34 — Reductions)

  This file performs a *problem reduction*: the question "how many roots does
  Δ_u f have?" is reduced to "how many roots does Lnorm have?" via an
  invertible substitution. This is the algebraic analogue of a polynomial-time
  reduction in complexity theory.

  ## Category Theory Pattern

  The kernel isomorphism is a *natural isomorphism* between two functors
  F* → Set:  u ↦ ker(Δ_u f)  and  u ↦ u · ker(Lnorm). The substitution
  y = x · u⁻¹ is the natural transformation component at u.

  ## Type Theory Pattern

  The `↔` (iff) in `kernel_iso_normalized` is a *logical equivalence*,
  which in the Curry-Howard correspondence is a pair of functions
  (forward, backward) — an *isomorphism* in the category of propositions.

  ## Functional Programming Principle

  Every definition here is a *pure function* — no mutable state, no side effects.
  `goldFun`, `deltaGold`, `linPart`, `Lnorm` are all referentially transparent.

  ## Reference
  Bracken–Byrne–Markin–McGuire, "Fourier Spectra of Binomial APN Functions",
  Theorem 3; Budaghyan, "Construction and Analysis of Cryptographic Functions".
-/

import Mathlib

/-!
  ## Design Decision: `noncomputable section`

  We enter a noncomputable section because definitions over abstract finite fields
  require classical logic (e.g., decidability of field operations, inverse elements).
  In Lean's type theory, `noncomputable` marks terms that use `Classical.choice`
  and cannot be evaluated by the kernel.

  **Lean Best Practice:** Prefer marking individual `def`s as `noncomputable` rather
  than whole sections, to make the computability boundary explicit. Here we use a
  section for convenience since *all* definitions involve the abstract field F.
-/
noncomputable section

open Finset Classical

variable {n : ℕ}
variable (k : ℕ) (hk : 0 < k)

/-!
  ## Design Decision: Typeclass-Bounded Variables

  The variable declaration below uses Lean's *typeclass system* to constrain F.
  Each bracket `[...]` is an *instance argument* — Lean's elaborator will
  automatically search for these instances.

  **Type Theory Pattern:** This is a *bounded polymorphism* — the function works
  for any type F satisfying the given constraints, analogous to System F with
  subtyping.

  **Category Theory Pattern:** `[Field F]` makes F an object in the category
  **Field** of fields; `[CharP F 2]` restricts to the subcategory of char 2 fields.
-/
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The Gold exponent: `d = 2^k + 1`.

  **Beautiful Pattern 🌟:** The Gold exponent is the simplest non-trivial power-of-two
  exponent that produces an APN function. It sits at the intersection of:
  - Number theory (Mersenne-like structure: 2^k + 1)
  - Galois theory (Frobenius orbit structure)
  - Coding theory (Kasami codes, BCH bounds)

  **CLRS Connection:** This is a *key parameter* analogous to the FFT's
  choice of primitive root of unity (CLRS Ch. 30). -/
def goldExp (k : ℕ) : ℕ := 2 ^ k + 1

/-! ### The Gold function and its derivative

  **Functional Programming Pattern:** We build complex functions by *composing*
  simpler ones: goldFun → deltaGold → linPart. Each layer adds one concept.
  This is the *composition over inheritance* principle.
-/

/-- Gold function `f(x) = x ^ (2^k + 1)`.

  **Category Theory:** This is a morphism in the category of F-sets (not F-linear!).
  Its non-linearity is precisely what makes it cryptographically useful.

  **Universal Property:** Among all monomial functions x^d, the Gold function is
  *universal* for the APN property in the sense that it achieves the minimum
  possible differential uniformity for power functions when gcd(k, n) = 1. -/
def goldFun (x : F) : F := x ^ goldExp k

/-- Budaghyan derivative `Δ_u f(x) = f(x + u) + f(x)`.

  **CLRS Connection (Ch. 4 — Divide & Conquer):** The derivative "divides"
  the function by looking at how it changes under translation by u.

  **Category Theory:** This is the *difference kernel* — the equalizer of
  `f` and `f ∘ (· + u)` in the category of F-sets.

  **Beautiful Pattern 🌟:** In char 2, addition IS subtraction, so this is
  simultaneously a forward difference and a backward difference. The char 2
  self-duality makes the derivative symmetric. -/
def deltaGold (u x : F) : F :=
  goldFun k F (x + u) + goldFun k F x

/-- The linearized part: `L_u(x) = x^(2^k) · u + x · u^(2^k)`.

  **Key Insight:** In characteristic 2, the Frobenius endomorphism x ↦ x^(2^k)
  is *additive*: (x+y)^(2^k) = x^(2^k) + y^(2^k). This means the derivative
  of the Gold function splits into a *linear* part (this definition) plus a
  *constant* (u^(2^k+1)).

  **Higher Operad Connection:** L_u is a *bilinear operation* — linear in x
  (via Frobenius linearity) and polynomial in u. This bilinearity is an
  operation in the *2-colored operad* of linearized polynomials. -/
def linPart (u x : F) : F :=
  x ^ (2 ^ k) * u + x * u ^ (2 ^ k)

/-- **Key identity in characteristic 2:**
  `Δ_u f(x) = x^(2^k) · u + x · u^(2^k) + u^(2^k+1)`.

  ## Proof Steps:
  1. Unfold definitions of `deltaGold`, `linPart`, `goldFun`, `goldExp`
  2. Apply the **Frobenius endomorphism**: `(x+u)^(2^k) = x^(2^k) + u^(2^k)` in char 2
     — this is `add_pow_char_pow`, the additive property of the Frobenius
  3. Multiply out `(x^(2^k) + u^(2^k)) · (x + u)` and cancel terms
  4. The `ring` tactic handles the polynomial arithmetic; `grind` closes edge cases

  **CLRS Connection (Ch. 30):** This is *polynomial expansion* — the same operation
  as evaluating a polynomial at a point, but done symbolically.

  **Type Theory Pattern:** The proof term witnesses the *propositional equality*
  between two well-typed expressions. The `erw` tactic performs *rewriting* —
  substituting equals for equals, which is the elimination rule for the
  identity type in Martin-Löf type theory. -/
lemma delta_eq_lin_plus_const (u x : F) :
    deltaGold k F u x = linPart k F u x + u ^ goldExp k := by
  unfold deltaGold linPart goldExp goldFun;
  unfold goldExp; ring;
  erw [ add_pow_char_pow ];
  grind

/-! ### The normalized operator via y = x / u

  **Design Pattern:** We define `Lnorm` as a standalone function rather than
  inline. This follows the *Extract Function* refactoring pattern — giving a
  name to a meaningful sub-expression improves readability and reusability.
-/

/-- Normalized linearized operator: `Lnorm(y) = y^(2^k) + y + 1`.

  **Beautiful Pattern 🌟:** This is an *Artin–Schreier equation* shifted by 1.
  The Artin–Schreier map y ↦ y^p + y (here p = 2^k via iterated Frobenius)
  is the fundamental tool of class field theory in characteristic p.
  Adding the constant 1 corresponds to looking at a *non-trivial coset*
  of the Artin–Schreier cover.

  **HoTT Connection:** The Artin–Schreier map is a *covering space* in the
  étale topology. The fiber over 1 (i.e., Lnorm = 0) is a *torsor* for
  the kernel of L₀ = y^(2^k) + y. -/
def Lnorm (y : F) : F :=
  y ^ (2 ^ k) + y + 1

/-- **Normalization Lemma.**  For `u ≠ 0`, the equation `Δ_u f(x) = 0` is
  equivalent to `Lnorm(y) = 0` where `y = x · u⁻¹`.

  ## Proof Steps:
  1. **Forward direction** (Δ_u f(x) = 0 → Lnorm(y) = 0):
     a. Rewrite Δ using `delta_eq_lin_plus_const`
     b. Substitute x = y · u where y = x · u⁻¹
     c. Factor out u^(2^k+1) (which is nonzero since u ≠ 0)
     d. Cancel to obtain Lnorm(y) = 0

  2. **Backward direction** (Lnorm(y) = 0 → Δ_u f(x) = 0):
     a. Multiply Lnorm(y) = 0 by u^(2^k+1)
     b. Expand to recover the original equation

  **Category Theory:** This is a *natural isomorphism* — the map y = x · u⁻¹
  is the component at u of a natural transformation between kernel functors.

  **CLRS Ch. 34 (Reductions):** This lemma *reduces* the root-counting problem
  for Δ_u f to the root-counting problem for Lnorm, which is independent of u.
  The reduction is invertible (bijective), so root counts are preserved.

  **Lean Best Practice:** The `set y := x * u⁻¹ with hy_def` introduces a local
  abbreviation and records the definition for later rewriting. This is cleaner
  than carrying `x * u⁻¹` through the proof. -/
lemma kernel_iso_normalized (u : F) (hu : u ≠ 0) (x : F) :
    deltaGold k F u x = 0 ↔ Lnorm k F (x * u⁻¹) = 0 := by
  set y := x * u⁻¹ with hy_def
  have hu_pow : u ^ goldExp k ≠ 0 := pow_ne_zero _ hu
  constructor
  · -- Forward direction: Δ_u f(x) = 0 → Lnorm(y) = 0
    -- Step 1: Rewrite using the linearization identity
    intro hΔ
    rw [delta_eq_lin_plus_const] at hΔ
    -- Step 2: Substitute x = y · u
    have hx : x = y * u := by
      rw [ hy_def, mul_assoc, inv_mul_cancel₀ hu, mul_one ]
    rw [hx] at hΔ
    -- Step 3: Factor and cancel u^(2^k+1)
    simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ];
    unfold linPart Lnorm goldExp at *;
    exact mul_left_cancel₀ ( pow_ne_zero ( 2 ^ k + 1 ) hu ) ( by linear_combination' hΔ )
  · -- Backward direction: Lnorm(y) = 0 → Δ_u f(x) = 0
    -- Step 1: Multiply by u^(2^k+1) to recover the original scale
    intro hL
    rw [delta_eq_lin_plus_const]
    unfold Lnorm linPart goldExp at *;
    convert congr_arg ( · * u ^ ( 2 ^ k + 1 ) ) hL using 1 <;> ring;
    simp +zetaDelta at *;
    field_simp [hu_pow]
    ring;
    simp +decide [ hu_pow ]

/-- The kernel of `Δ_u f` (as a set) is the image of ker(Lnorm) under scaling by u.

  ## Proof Steps:
  1. Show set extensionality: x ∈ LHS ↔ x ∈ RHS
  2. Forward: given Δ_u f(x) = 0, produce y = x · u⁻¹ with Lnorm(y) = 0 and y · u = x
  3. Backward: given y with Lnorm(y) = 0, show Δ_u f(y · u) = 0

  **Category Theory:** This establishes ker(Δ_u f) as the *image* of ker(Lnorm)
  under the multiplication-by-u functor. The image is a *colimit* construction.

  **Functional Programming:** The proof uses `Set.mem_image` — the characteristic
  predicate of the image of a function. This is the *map* operation on sets,
  analogous to `List.map` or `Array.map`.

  **Beautiful Pattern 🌟:** The proof of the backward direction uses `rintro ⟨y, hy, rfl⟩`,
  which simultaneously destructs the existential and substitutes `x := y * u`.
  This is *pattern matching on dependent pairs* — a core operation in dependent
  type theory. -/
lemma kernel_deltaGold_eq_image (u : F) (hu : u ≠ 0) :
    {x : F | deltaGold k F u x = 0} =
      (fun y => y * u) '' {y : F | Lnorm k F y = 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨x * u⁻¹, ?_, ?_⟩
    · rwa [← kernel_iso_normalized k F u hu]
    · field_simp
  · rintro ⟨y, hy, rfl⟩
    rwa [kernel_iso_normalized k F u hu, mul_assoc, mul_inv_cancel₀ hu, mul_one]

/-- **Cardinality bound:** The number of roots of `Lnorm` in `F` is at most `2^k`.

  ## Proof Steps:
  1. Construct the polynomial `p = X^(2^k) + X + 1 ∈ F[X]`
  2. Show that roots of Lnorm in F correspond to roots of p
  3. Apply `Polynomial.card_roots'`: a polynomial of degree d has ≤ d roots
  4. Verify that natDegree(p) = 2^k

  **CLRS Ch. 30 (Polynomials & FFT):** This is the *fundamental theorem of algebra*
  for finite fields — a polynomial of degree d has at most d roots. This is the
  same principle that makes polynomial evaluation/interpolation work in O(n log n)
  via the FFT.

  **Category Theory:** The set of roots is the *fiber* of the evaluation morphism
  `ev : F → F` (sending y to p(y)) over 0. The degree bound is a bound on the
  *fiber cardinality*, analogous to the degree of a finite morphism in algebraic
  geometry.

  **Lean Best Practice:** The `set p := ... with hp_def` pattern names the polynomial
  and records its definition, making subsequent reasoning cleaner. -/
lemma card_roots_Lnorm_le :
    (univ.filter fun y : F => Lnorm k F y = 0).card ≤ 2 ^ k := by
  -- Step 1: Construct the polynomial p(X) = X^(2^k) + X + 1
  set p : Polynomial F := Polynomial.X ^ (2 ^ k) + Polynomial.X + 1;
  -- Step 2: Bound the number of roots of p using degree bound
  have h_deg : p.roots.toFinset.card ≤ 2 ^ k := by
    refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
    rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
    norm_num +zetaDelta at *;
    intro m hm; rw [ Polynomial.coeff_X, Polynomial.coeff_one ] ; split_ifs <;> simp_all +decide ;
    · norm_cast at hm; aesop;
    · norm_cast at hm;
  -- Step 3: Show that {y | Lnorm(y) = 0} ⊆ roots(p), then apply the bound
  convert h_deg using 2;
  ext y; simp [p, Lnorm];
  exact fun _ => ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide )

end

/-
  Theorem3/Factorization.lean

  ══════════════════════════════════════════════════════════════════════
  BRACKEN–MCGUIRE FACTORIZATION of the linearized polynomial arising from
  the derivative of a Gold-type APN function.
  ══════════════════════════════════════════════════════════════════════

  ## Mathematical Context

  The normalized operator `Lnorm(y) = y^(2^k) + y + 1` can be related to
  the composition of two Gold-type (Frobenius-linear) operators. The additive
  polynomial `y ↦ y^(2^k) + y` factors through the Frobenius endomorphism,
  and its kernel has size at most `2^k`.

  ## Algorithmic Pattern (CLRS Ch. 4 — Divide & Conquer)

  The factorization L₁ ∘ L₂ = L₀ is a *recursive decomposition*: the degree-2^k
  operator L₀ is decomposed into a degree-2 operator L₁ composed with a
  degree-2^(k-1) operator L₂. This mirrors the FFT's recursive halving of
  polynomial evaluation (CLRS §30.2).

  ## Category Theory Pattern

  L₁, L₂, L₀ are morphisms in the category of F-vector spaces (they are all
  𝔽₂-linear). The factorization is a commutative triangle in this category:
      L₂         L₁
  F ——→ F ——→ F
   \___________/
        L₀

  ## Higher Operad Connection

  The factorization is a *composition* in the operad of linearized polynomials
  over 𝔽₂. Each linearized polynomial is an operation, and function composition
  is the operadic composition. The factorization is a *corolla* — a tree with
  one internal vertex (L₁) and one leaf (L₂).

  ## Reference
  Bracken–Byrne–Markin–McGuire, Theorem 3 (Factorization step).
-/

import Mathlib

/-!
  ## Noncomputable Section

  **Lean Best Practice:** We use `noncomputable section` because the abstract
  field F requires classical logic for decidability of operations. All
  definitions in this section produce terms that cannot be evaluated by
  Lean's kernel — they exist only as mathematical objects in the logic.

  **Type Theory Pattern:** The `noncomputable` annotation is a *modality* —
  it marks terms that live in the "classical" fragment of the type theory,
  as opposed to the "constructive" fragment where computation is possible.
-/
noncomputable section

open Polynomial Finset Classical

variable (k : ℕ)
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ### Frobenius properties in characteristic 2

  **Beautiful Pattern 🌟:** The Frobenius endomorphism φ(x) = x^p is perhaps
  the single most important map in positive-characteristic algebra. It is:
  - A *ring homomorphism* (because char p: (x+y)^p = x^p + y^p)
  - An *endofunctor* on the category of F-algebras
  - The *generator* of the Galois group Gal(F/𝔽_p) ≅ ℤ/nℤ
  - A *natural transformation* Id → (·)^p between identity and power functors

  **HoTT Connection:** The Frobenius is a *loop* in the space of endomorphisms
  of F. The Galois group is the *fundamental group* π₁(BEnd(F)).
-/

/-- The Frobenius endomorphism `φ(x) = x^2` is a ring homomorphism in char 2.

  **Type Theory:** `F →+* F` is a *bundled morphism* — a dependent pair of a
  function and proofs that it preserves ring operations. This is a Σ-type
  `Σ (f : F → F), IsRingHom f`.

  **Category Theory:** This is an *endomorphism* in the category **Ring**. -/
def frob2 : F →+* F := frobenius F 2

/-- The iterated Frobenius `φ^k(x) = x^(2^k)`.

  **CLRS Connection (Ch. 31 — Repeated Squaring):** Iterated Frobenius is
  computed by repeated squaring: φ^k = φ ∘ φ ∘ ... ∘ φ (k times), which is
  equivalent to computing x^(2^k) by k successive squarings. This is exactly
  the *repeated squaring* algorithm for modular exponentiation (CLRS §31.6).

  **Category Theory:** This is the k-fold power of an endomorphism in the
  *endomorphism monoid* End(F). The monoid structure (with composition as
  multiplication) is captured by `(frobenius F 2) ^ k`. -/
def frobIter : F →+* F := (frobenius F 2) ^ k

/-- `frobIter k x = x ^ (2^k)`.

  ## Proof Steps:
  1. Induction on k
  2. Base case (k=0): φ^0(x) = x = x^(2^0) = x^1
  3. Inductive step: φ^(k+1)(x) = φ(φ^k(x)) = (x^(2^k))^2 = x^(2^(k+1))

  **Functional Programming:** This proof uses *structural recursion* on the
  natural number k — the canonical elimination principle for inductive types. -/
lemma frobIter_apply (x : F) : frobIter k F x = x ^ (2 ^ k) := by
  induction' k with k ih
  · aesop
  · convert congr_arg (fun y => y ^ 2) ih using 1 <;> ring
    unfold frobIter; rw [pow_add, pow_one]; norm_cast

/-! ### The linearized operator and its factorization

  **Design Pattern (Single Responsibility):** Each operator (L₀, L₁, L₂) has
  exactly one job. L₀ is the "target" operator, L₁ is the Artin-Schreier map,
  and L₂ is the partial Frobenius trace. The factorization theorem connects them.
-/

/-- The linearized (additive) operator `L₀(y) = y^(2^k) + y`.

  **Beautiful Pattern 🌟:** L₀ is the *Artin-Schreier map* in characteristic 2.
  Its kernel ker(L₀) = {y ∈ F | y^(2^k) = y} = 𝔽_{2^gcd(k,n)} is a *subfield*
  of F — the fixed field of the k-th Frobenius. This connects differential
  cryptanalysis to Galois theory!

  **Higher Category Theory:** L₀ is a 1-morphism in the 2-category of
  correspondences between 𝔽₂-vector spaces. The kernel and image give a
  factorization through a sub-correspondence. -/
def L₀ (y : F) : F := y ^ (2 ^ k) + y

/-- `L₀` is additive (𝔽₂-linear): `L₀(a + b) = L₀(a) + L₀(b)`.

  ## Proof Steps:
  1. Unfold L₀
  2. Expand (a+b)^(2^k) using the Frobenius: (a+b)^(2^k) = a^(2^k) + b^(2^k)
  3. Rearrange terms

  **Category Theory:** This proves that L₀ is a *morphism* in the category
  of 𝔽₂-vector spaces (not just a set map). The additivity is the
  *linearity condition*.

  **Functional Programming:** An additive function is a *homomorphism* — it
  preserves the algebraic structure. This is the FP analogue of a *functor*
  preserving composition. -/
lemma L₀_add (a b : F) : L₀ k F (a + b) = L₀ k F a + L₀ k F b := by
  unfold L₀
  induction' k with k ih <;> simp_all +decide [pow_succ, pow_mul]
  · ring
  · grind

/-- **First Gold-type operator.** `L₁(y) = y^2 + y` (the Artin–Schreier map).

  **Beautiful Pattern 🌟:** L₁ is the *simplest* Artin-Schreier map — it maps
  y to y² + y. Its kernel is {0, 1} = 𝔽₂ ⊂ F. The cokernel F/im(L₁) classifies
  *Artin-Schreier extensions* of F — degree-2 extensions of characteristic-2 fields.

  **Universal Arrow:** L₁ is the *universal* additive polynomial of degree 2.
  Any additive polynomial of degree 2 over 𝔽₂ is a scalar multiple of L₁. -/
def L₁ (y : F) : F := y ^ 2 + y

/-- **Second Gold-type operator.**
  `L₂(y) = ∑_{i=0}^{k-1} y^(2^i)` — the partial Frobenius trace.

  **CLRS Connection (Ch. 30 — Polynomial Evaluation):** L₂ evaluates a
  *linearized polynomial* ∑ X^(2^i) at y. This is a sum of Frobenius powers,
  analogous to evaluating a polynomial at roots of unity in the FFT.

  **Category Theory:** L₂ is the *trace map* from F to the fixed field of the
  k-th Frobenius. In the Galois extension F/𝔽_{2^gcd(k,n)}, the trace is the
  *norm* in the symmetric monoidal category of Galois modules.

  **Functional Programming:** The `∑ i ∈ range k, y ^ (2 ^ i)` uses Finset.sum,
  which is a *fold* (catamorphism) over the finite set `range k`. This is the
  canonical way to compute finite sums in Lean — type-safe and total. -/
def L₂ (y : F) : F :=
  ∑ i ∈ range k, y ^ (2 ^ i)

/-- **Factorization identity:** `L₁(L₂(y)) = L₀(y) = y^(2^k) + y`.

  ## Proof Steps:
  1. Unfold L₁, L₂, L₀
  2. Induction on k:
     - Base (k=0): L₁(L₂(y)) = L₁(0) = 0 = L₀(y)
     - Step (k+1): Use L₂(k+1, y) = L₂(k, y) + y^(2^k) and the Frobenius
  3. The `grind` tactic handles the algebraic simplification

  **CLRS Ch. 4 (Divide & Conquer) / Ch. 30 (FFT):** This factorization is the
  *telescoping* identity for the sum ∑ y^(2^i). Just as the FFT factors the
  DFT matrix into a product of sparse matrices, here L₀ factors into L₁ ∘ L₂.

  **Higher Operad Connection:** In the operad of linearized polynomials, this
  is a *composition*: the operation L₀ of arity 2^k equals L₁ ∘ L₂ where
  L₁ has arity 2 and L₂ has arity 2^(k-1). This is a 2-level tree in the operad.

  **Beautiful Pattern 🌟:** The factorization is *telescoping* in disguise:
    L₁(L₂(y)) = (∑ y^(2^i))² + ∑ y^(2^i)
               = ∑ y^(2^(i+1)) + ∑ y^(2^i)
               = y^(2^k) + y                    (everything else cancels!) -/
lemma L₁_comp_L₂ (y : F) : L₁ F (L₂ k F y) = L₀ k F y := by
  unfold L₁ L₂ L₀
  induction' k with k ih <;> simp_all +decide [pow_succ, pow_mul, Finset.sum_range_succ]
  · grind
  · grind

/-! ### Kernel bounds from the factorization

  **CLRS Connection (Appendix C — Counting):** These lemmas count elements of
  finite sets defined by polynomial equations. The key tool is the *degree bound*:
  a polynomial of degree d has at most d roots over any field.

  **Amortized Analysis Pattern (CLRS Ch. 17):** The factorization L₁ ∘ L₂ = L₀
  lets us bound |ker L₀| ≤ |ker L₁| · |ker L₂| (by the rank-nullity theorem
  applied to the factorization). But we actually use a simpler direct argument:
  L₀ has degree 2^k as a polynomial, so it has ≤ 2^k roots.
-/

/-- The kernel of `L₁` has at most 2 elements.

  ## Proof Steps:
  1. Show that y² + y = 0 implies y ∈ {0, 1} (by factoring: y(y+1) = y(y-1) = 0 in char 2)
  2. The filter set is a subset of {0, 1}
  3. |{0, 1}| ≤ 2

  **Lean Best Practice:** The proof cleanly separates the mathematical content
  (roots are 0 or 1) from the set-theoretic bookkeeping (subset, cardinality).
  Use `have` to state the key mathematical fact, then `exact` to close the goal.

  **Type Theory:** The proof of `y = 0 ∨ y = 1` is a *sum type introduction* —
  we construct an element of `A ∨ B` by providing either `inl : A` or `inr : B`. -/
lemma card_ker_L₁ :
    (univ.filter fun y : F => L₁ F y = 0).card ≤ 2 := by
  -- Key mathematical fact: the only roots are 0 and 1
  have h_roots_bound : ∀ y : F, y ^ 2 + y = 0 → y = 0 ∨ y = 1 := by grind
  -- The filter set is contained in {0, 1}
  exact le_trans (Finset.card_le_card
    (show Finset.filter (fun y => y ^ 2 + y = 0) Finset.univ ⊆ {0, 1} by aesop_cat))
    (Finset.card_insert_le _ _)

/-- The kernel of `L₂` has at most `2^(k-1)` elements (requires `k ≥ 1`).

  ## Proof Steps:
  1. Construct the polynomial `p = ∑_{i=0}^{k-1} X^(2^i)` ∈ F[X]
  2. Show that {y | L₂(y) = 0} ⊆ roots(p).toFinset
  3. Apply the chain: |filter| ≤ |roots.toFinset| ≤ |roots| ≤ natDegree(p)
  4. Show natDegree(p) = 2^(k-1) (the leading term is X^(2^(k-1)))

  **CLRS Ch. 30:** This uses the fundamental theorem that a polynomial of degree d
  has at most d roots, which is also the basis for polynomial interpolation.

  **Category Theory:** The roots form the *fiber* of the evaluation map
  ev_0 : F → F (evaluating p at each point) over 0 ∈ F. The degree bound is
  a bound on the *fiber cardinality* of a finite morphism. -/
lemma card_ker_L₂ (hk : 0 < k) :
    (univ.filter fun y : F => L₂ k F y = 0).card ≤ 2 ^ (k - 1) := by
  -- Step 1: Construct the polynomial
  set p : Polynomial F := ∑ i ∈ Finset.range k, Polynomial.X ^ (2 ^ i);
  -- Step 2: Roots of L₂ are roots of p
  have h_roots : Finset.filter (fun y : F => L₂ k F y = 0) (Finset.univ : Finset F) ⊆ p.roots.toFinset := by
    intro y hy; simp_all +decide [ Polynomial.eval_finset_sum ] ;
    refine' ⟨ _, _ ⟩;
    · simp +zetaDelta at *;
      exact ne_of_apply_ne ( fun p => p.coeff ( 2 ^ ( k - 1 ) ) ) ( by cases k <;> simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] );
    · rw [ Polynomial.eval_finset_sum, show L₂ k F y = ∑ i ∈ Finset.range k, y ^ ( 2 ^ i ) from rfl ] at * ; aesop;
  -- Step 3: Chain of inequalities: |filter| ≤ |toFinset| ≤ |roots| ≤ natDegree
  refine' le_trans ( Finset.card_le_card h_roots ) ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
  -- Step 4: natDegree(p) = 2^(k-1)
  rw [ Polynomial.natDegree_sum_eq_of_disjoint ];
  · simp +zetaDelta at *;
    exact fun i hi => pow_le_pow_right₀ ( by decide ) ( Nat.le_pred_of_lt hi );
  · intro i hi j hj hij; contrapose hij; aesop;

/-- **Root count for `L₀`:** `|{y ∈ F : y^(2^k) + y = 0}| ≤ 2^k`.

  ## Proof Steps:
  1. The polynomial p(X) = X^(2^k) + X has degree 2^k
  2. It is nonzero (the leading coefficient is 1)
  3. By the degree bound: roots ≤ degree = 2^k

  **CLRS Ch. 30 (Polynomials):** Direct application of the fundamental
  root-counting theorem for polynomials over fields.

  **Beautiful Pattern 🌟:** The proof that p is nonzero uses `natDegree_add_eq_left`
  — when two polynomials have different degrees, the degree of their sum equals the
  larger degree. This is the *ultrametric inequality* for the degree valuation. -/
lemma card_roots_L₀_le (hk : 0 < k) :
    (univ.filter fun y : F => L₀ k F y = 0).card ≤ 2 ^ k := by
  -- Step 1: Construct the polynomial p(X) = X^(2^k) + X
  set p : Polynomial F := Polynomial.X ^ (2 ^ k) + Polynomial.X;
  -- Step 2: Bound roots using degree
  have h_roots_bound : (p.roots.toFinset).card ≤ 2 ^ k := by
    refine' le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ );
    rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num [ hk ];
    grind +splitImp;
  -- Step 3: Show the filter set is contained in the root set
  refine' le_trans ( Finset.card_le_card _ ) h_roots_bound;
  intro y hy; simp_all +decide [ L₀ ] ;
  exact ⟨ ne_of_apply_ne Polynomial.natDegree ( by erw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num ; linarith [ Nat.pow_le_pow_right two_pos hk ] ), by aesop ⟩

/-- **Root count for the shifted operator:**
  `|{y ∈ F : y^(2^k) + y + 1 = 0}| ≤ 2^k`.

  ## Proof Steps:
  1. The polynomial X^(2^k) + X + 1 has degree 2^k
  2. It is nonzero (evaluates to 1 at 0)
  3. Apply the degree bound

  **Lean Best Practice:** This lemma follows the exact same pattern as
  `card_roots_L₀_le`. In production code, consider extracting a general
  `card_roots_of_poly` lemma to avoid the duplication (see ANALYSIS.md §10.2).

  **Refactoring Opportunity (CLRS Ch. 15 — Dynamic Programming):**
  The three root-counting lemmas share the same proof skeleton. Extract the
  shared structure into a reusable "root-counting template" — this is the
  DP principle of *optimal substructure*: identify the common sub-problem
  and solve it once. -/
lemma card_roots_shifted_le (hk : 0 < k) :
    (univ.filter fun y : F => y ^ (2 ^ k) + y + 1 = 0).card ≤ 2 ^ k := by
  -- Step 1: Embed into polynomial roots
  have h_roots : (Finset.filter (fun y : F => y ^ 2 ^ k + y + 1 = 0) Finset.univ).card ≤ (Polynomial.X ^ 2 ^ k + Polynomial.X + 1 : Polynomial F).roots.toFinset.card := by
    refine Finset.card_le_card ?_;
    simp +decide [ Finset.subset_iff ];
    exact fun x hx => ⟨ by exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by simp +decide [ hx ] ), hx ⟩;
  -- Step 2: Apply degree bound
  refine' le_trans h_roots ( le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) _ ) );
  rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> norm_num;
  · linarith;
  · linarith

end

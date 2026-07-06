import RequestProject.Steiner.Walsh

/-!
# CCZ-equivalence (Section 2.2)

We transcribe Definition 2.3 (graph and CCZ-equivalence) and the Walsh-transform
relation for CCZ-equivalent functions (Eq. (6)–(10)).
-/

open scoped BigOperators

namespace Flystel

variable {Fq : Type*} [Field Fq] [Fintype Fq]

/-- **Definition 2.3 (1)** (Graph).
The graph of `F : Fqⁿ → Fqᵐ` is `Γ_F = { (x, F x) | x ∈ Fqⁿ }`. -/
def graph {n m : ℕ} (F : (Fin n → Fq) → (Fin m → Fq)) :
    Set ((Fin n → Fq) × (Fin m → Fq)) :=
  Set.range (fun x => (x, F x))

/-- An affine permutation of `Fqⁿ × Fqᵐ`, written `A(z) = A·z + c`.
We package the linear part as a (block) matrix acting on `Fq^(n+m)` and the
constant `c`, together with bijectivity. -/
structure AffinePerm (N : ℕ) (Fq : Type*) [Field Fq] where
  /-- The invertible linear part. -/
  matrix : Matrix (Fin N) (Fin N) Fq
  /-- The translation part. -/
  const : Fin N → Fq
  /-- The induced map is a bijection. -/
  bijective : Function.Bijective (fun z : Fin N → Fq => matrix.mulVec z + const)

/-- The underlying map `z ↦ A z + c` of an affine permutation. -/
def AffinePerm.toFun {N : ℕ} (A : AffinePerm N Fq) : (Fin N → Fq) → (Fin N → Fq) :=
  fun z => A.matrix.mulVec z + A.const

/-- **Definition 2.3 (2)** (CCZ-equivalence).
`F` and `G : Fqⁿ → Fqᵐ` are CCZ-equivalent if there exists an affine
permutation `A` of `Fqⁿ × Fqᵐ` such that `Γ_F = A(Γ_G)`.

We identify `Fqⁿ × Fqᵐ` with `Fq^(n+m)` via the obvious appending of
coordinates. -/
def CCZEquiv {n m : ℕ} (F G : (Fin n → Fq) → (Fin m → Fq)) : Prop :=
  ∃ A : AffinePerm (n + m) Fq,
    -- `Γ_F = A (Γ_G)` under the identification `Fqⁿ × Fqᵐ ≃ Fq^(n+m)`.
    (graph F : Set _) =
      (fun p : (Fin n → Fq) × (Fin m → Fq) =>
        (let z := A.toFun (Fin.append p.1 p.2);
          (fun i : Fin n => z (Fin.castAdd m i), fun j : Fin m => z (Fin.natAdd n j)))) ''
        graph G

/-
**Eq. (6)–(10)** (Walsh transform under CCZ-equivalence).
Let `F, G : Fqⁿ → Fqᵐ` be CCZ-equivalent via the affine permutation
`A(x) = A·x + c` with block decomposition `A = [[A₁, A₂], [A₃, A₄]]`.  Then for
`a ∈ Fqⁿ`, `b ∈ Fqᵐ`,
`W_F(ψ, a, b) = ψ(⟨(a,b), c⟩) · W_G(ψ, A₁ᵀ a + A₂ᵀ b, A₃ᵀ a + A₄ᵀ b)`,
so that the absolute values of the Walsh spectra of `F` and `G` are related by a
linear change of the linear-approximation masks.

We transcribe the *consequence* used in the paper: the absolute value of the
Walsh spectrum of `F` is obtained from that of `G` by an invertible linear
substitution of the masks.
-/
theorem walsh_of_CCZEquiv {n m : ℕ} (ψ : AddChar Fq ℂ)
    (F G : (Fin n → Fq) → (Fin m → Fq)) (h : CCZEquiv F G)
    (a : Fin n → Fq) (b : Fin m → Fq) :
    ∃ (a' : Fin n → Fq) (b' : Fin m → Fq),
      ‖walshTransform ψ F a b‖ = ‖walshTransform ψ G a' b'‖ := by
  obtain ⟨ A, hA ⟩ := h;
  -- Let $e : (Fin n → Fq) → (Fin n → Fq)$ be the bijection given by $e y = x$ such that $(x, F x) = D(y, G y)$.
  obtain ⟨e, he⟩ : ∃ e : (Fin n → Fq) ≃ (Fin n → Fq), ∀ y, (e y, F (e y)) = (fun p => (let z := A.toFun (Fin.append p.1 p.2); (fun i => z (Fin.castAdd m i), fun j => z (Fin.natAdd n j)))) (y, G y) := by
    have h_bij : ∀ y : Fin n → Fq, ∃! x : Fin n → Fq, (x, F x) = (fun p => (let z := A.toFun (Fin.append p.1 p.2); (fun i => z (Fin.castAdd m i), fun j => z (Fin.natAdd n j)))) (y, G y) := by
      intro y
      obtain ⟨x, hx⟩ : ∃ x : Fin n → Fq, (x, F x) = (fun p => (let z := A.toFun (Fin.append p.1 p.2); (fun i => z (Fin.castAdd m i), fun j => z (Fin.natAdd n j)))) (y, G y) := by
        exact hA.symm.subset ⟨ _, Set.mem_range_self _, rfl ⟩
      use x
      simp [hx];
      grind +extAll;
    choose e he using fun y => ExistsUnique.exists ( h_bij y );
    refine' ⟨ Equiv.ofBijective e _, he ⟩;
    have h_surj : Function.Surjective e := by
      intro x;
      replace hA := Set.ext_iff.mp hA ( x, F x ) ; simp_all +decide [ graph ] ;
      exact ⟨ hA.choose, hA.choose_spec.1 ⟩;
    exact ⟨ Finite.injective_iff_surjective.mpr h_surj, h_surj ⟩;
  -- By definition of $e$, we know that $walshTransform ψ F a b = walshTransform ψ G a' b'$ for some $a'$ and $b'$.
  obtain ⟨a', b', h_eq⟩ : ∃ a' : Fin n → Fq, ∃ b' : Fin m → Fq, ∀ y : Fin n → Fq, ψ (dotProduct a (e y) + dotProduct b (F (e y))) = ψ (dotProduct a' y + dotProduct b' (G y) + dotProduct (Fin.append a b) A.const) := by
    have h_eq : ∀ y : Fin n → Fq, dotProduct a (e y) + dotProduct b (F (e y)) = dotProduct (Fin.append a b) (A.toFun (Fin.append y (G y))) := by
      intro y; specialize he y; simp_all +decide [ funext_iff, Fin.append ] ;
      simp +decide [ Fin.sum_univ_add, dotProduct, he ];
    have h_eq : ∀ y : Fin n → Fq, dotProduct (Fin.append a b) (A.toFun (Fin.append y (G y))) = dotProduct (Fin.append a b) (A.matrix.mulVec (Fin.append y (G y))) + dotProduct (Fin.append a b) A.const := by
      simp +decide [ AffinePerm.toFun, dotProduct_add ];
    have h_eq : ∀ y : Fin n → Fq, dotProduct (Fin.append a b) (A.matrix.mulVec (Fin.append y (G y))) = dotProduct (Matrix.mulVec (Matrix.transpose A.matrix) (Fin.append a b)) (Fin.append y (G y)) := by
      simp +decide [ Matrix.dotProduct_mulVec ];
      simp +decide [ Matrix.vecMul, dotProduct ];
      simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
    use fun i => (Matrix.mulVec (Matrix.transpose A.matrix) (Fin.append a b)) (Fin.castAdd m i), fun j => (Matrix.mulVec (Matrix.transpose A.matrix) (Fin.append a b)) (Fin.natAdd n j);
    simp_all +decide [ dotProduct, Fin.sum_univ_add ];
  use a', b';
  convert Flystel.Foundations.norm_charSum_add_const ψ ( fun y => a' ⬝ᵥ y + b' ⬝ᵥ G y ) ( Fin.append a b ⬝ᵥ A.const ) using 1;
  rw [ walshTransform_def ];
  rw [ ← Equiv.sum_comp e ];
  simp +decide only [h_eq, add_comm]

omit [Fintype Fq] in
/-- The linear part of an affine permutation is invertible: the underlying matrix
is a unit. -/
theorem AffinePerm.isUnit_matrix {N : ℕ} [DecidableEq (Fin N)]
    (A : AffinePerm N Fq) : IsUnit A.matrix := by
  have h_bijective : Function.Bijective (fun z : Fin N → Fq => A.matrix.mulVec z + A.const) := by
    exact A.bijective;
  convert Matrix.mulVec_injective_iff_isUnit.mp ( show Function.Injective ( fun z : Fin N → Fq => A.matrix.mulVec z ) from ?_ ) using 1;
  exact fun x y hxy => h_bijective.injective ( by simpa using hxy )

set_option maxHeartbeats 800000 in
/-- **Mask-tracking CCZ-invariance of the Walsh spectrum.** If `F` and `G` are
CCZ-equivalent, then for *every nonzero* linear-approximation mask `(a, b)` of `F`
there is a *nonzero* mask `(a', b')` of `G` with the same Walsh magnitude.  The
mask substitution is the invertible transpose of the affine permutation's linear
part, so it sends nonzero masks to nonzero masks; this is what makes the Walsh
*spectrum* (in particular the nonlinearity, the maximum over nonzero masks)
transfer across CCZ-equivalence. -/
theorem walsh_of_CCZEquiv_ne {n m : ℕ} (ψ : AddChar Fq ℂ)
    (F G : (Fin n → Fq) → (Fin m → Fq)) (h : CCZEquiv F G)
    (a : Fin n → Fq) (b : Fin m → Fq) (hab : (a, b) ≠ (0, 0)) :
    ∃ (a' : Fin n → Fq) (b' : Fin m → Fq), (a', b') ≠ (0, 0) ∧
      ‖walshTransform ψ F a b‖ = ‖walshTransform ψ G a' b'‖ := by
  obtain ⟨ A, hA ⟩ := h;
  refine' ⟨ fun i => ( A.matrix.transpose.mulVec ( Fin.append a b ) ) ( Fin.castAdd m i ), fun j => ( A.matrix.transpose.mulVec ( Fin.append a b ) ) ( Fin.natAdd n j ), _, _ ⟩ <;> simp_all +decide [ funext_iff ];
  · intro h
    have h_nonzero : Fin.append a b ≠ 0 := by
      exact fun h => by obtain ⟨ x, hx ⟩ := hab ( fun i => by simpa using congr_fun h ( Fin.castAdd m i ) ) ; exact hx ( by simpa using congr_fun h ( Fin.natAdd n x ) ) ;
    have h_nonzero' : A.matrix.transpose.mulVec (Fin.append a b) ≠ 0 := by
      have h_nonzero' : Function.Injective (Matrix.mulVec (A.matrix.transpose)) := by
        have := AffinePerm.isUnit_matrix A;
        rw [ Matrix.isUnit_iff_isUnit_det ] at this;
        exact fun x y hxy => by simpa [ this.ne_zero ] using congr_arg ( fun z => A.matrix.transpose⁻¹.mulVec z ) hxy;
      exact fun h => h_nonzero <| h_nonzero'.eq_iff.mp <| by simpa using h;
    have h_nonzero'' : ∃ x : Fin (n + m), A.matrix.transpose.mulVec (Fin.append a b) x ≠ 0 := by
      exact Function.ne_iff.mp h_nonzero'
    obtain ⟨x, hx⟩ := h_nonzero'';
    cases' x using Fin.addCases with x x <;> simp_all +decide [ Fin.append ];
    exact ⟨ x, hx ⟩;
  · -- By definition of $A$, we know that $F(x) = G(x')$ where $x'$ is such that $A(x') = (x, F(x))$.
    have h_eq : ∀ x : Fin n → Fq, ∃ x' : Fin n → Fq, A.toFun (Fin.append x' (G x')) = Fin.append x (F x) := by
      intro x
      have h_exists_x' : ∃ x' : Fin n → Fq, (fun i => A.toFun (Fin.append x' (G x')) (Fin.castAdd m i), fun j => A.toFun (Fin.append x' (G x')) (Fin.natAdd n j)) = (x, F x) := by
        replace hA := Set.ext_iff.mp hA ( x, F x ) ; simp_all +decide [ graph ] ;
      obtain ⟨ x', hx' ⟩ := h_exists_x';
      use x';
      ext i; cases i using Fin.addCases <;> simp_all +decide [ funext_iff ] ;
    choose f hf using h_eq;
    -- By definition of $f$, we know that $f$ is a bijection.
    have h_bij : Function.Bijective f := by
      have h_inj : Function.Injective f := by
        intro x y hxy; have := hf x; have := hf y; simp_all +decide [ Fin.append ] ;
        ext i; replace this := congr_fun this ( Fin.castAdd m i ) ; aesop;
      exact ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩;
    have h_sum_eq : ∀ x : Fin n → Fq, a ⬝ᵥ x + b ⬝ᵥ (F x) = (A.matrix.transpose.mulVec (Fin.append a b)) ⬝ᵥ (Fin.append (f x) (G (f x))) + (A.const ⬝ᵥ (Fin.append a b)) := by
      intro x
      have h_eq : (Fin.append a b) ⬝ᵥ (A.toFun (Fin.append (f x) (G (f x)))) = (A.matrix.transpose.mulVec (Fin.append a b)) ⬝ᵥ (Fin.append (f x) (G (f x))) + (A.const ⬝ᵥ (Fin.append a b)) := by
        simp +decide [ AffinePerm.toFun, Matrix.mulVec, dotProduct ];
        simp +decide only [mul_add, Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_mul];
        exact congrArg₂ ( · + · ) ( Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring ) ) ( Finset.sum_congr rfl fun _ _ => by ring );
      simp_all +decide [ dotProduct, Fin.sum_univ_add ];
    simp_all +decide [ dotProduct, Fin.sum_univ_add ];
    have h_sum_eq : ∑ x : Fin n → Fq, ψ (∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.castAdd m i) * f x i + ∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.natAdd n i) * G (f x) i + (∑ x, A.const (Fin.castAdd m x) * a x + ∑ x, A.const (Fin.natAdd n x) * b x)) = ∑ x : Fin n → Fq, ψ (∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.castAdd m i) * x i + ∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.natAdd n i) * G x i) * ψ (∑ x, A.const (Fin.castAdd m x) * a x + ∑ x, A.const (Fin.natAdd n x) * b x) := by
      have h_sum_eq : ∑ x : Fin n → Fq, ψ (∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.castAdd m i) * f x i + ∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.natAdd n i) * G (f x) i + (∑ x, A.const (Fin.castAdd m x) * a x + ∑ x, A.const (Fin.natAdd n x) * b x)) = ∑ x : Fin n → Fq, ψ (∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.castAdd m i) * x i + ∑ i, A.matrix.transpose.mulVec (Fin.append a b) (Fin.natAdd n i) * G x i + (∑ x, A.const (Fin.castAdd m x) * a x + ∑ x, A.const (Fin.natAdd n x) * b x)) := by
        conv_rhs => rw [ ← Equiv.sum_comp ( Equiv.ofBijective f ( by simpa [ Finset.ext_iff ] using h_bij ) ) ] ;
        rfl;
      convert h_sum_eq using 2;
      rw [ ← AddChar.map_add_eq_mul ];
    simp_all +decide [ ← Finset.sum_mul _ _ _ ]

end Flystel
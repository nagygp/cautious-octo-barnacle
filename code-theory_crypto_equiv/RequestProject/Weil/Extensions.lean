import RequestProject.Weil.PointCountBound
import RequestProject.Weil.Trace
import RequestProject.Weil.Amplification

/-!
# Point counts over extensions and the L-function link (the amplification input)

The descent to a *single* character in `weil_bound` runs the extension-field amplification: it needs
the point-count / character-sum bound **uniformly over every extension `𝔽_{q^k}`** with a constant
*independent of `k`*, plus the rationality (L-function) link that turns the family of extension sums
into a fixed finite list of reciprocal roots.  The base-field modules
(`Stepanov`, `PointCountBound`) only state the bound over `F` itself; this module supplies the
extension-uniform versions and the link, closing the last gap flagged in the roadmap.

Crucially, the Stepanov bound `abs_curvePointCount_sub_card_le` is *generic in the finite field*, so
it instantiates verbatim over each extension `E/F` — this module simply re-packages it as a family.

## Contents

* **Base change.**  `baseChange E f` lifts `f ∈ F[X]` to `E[X]`; `liftChar E ψ = ψ ∘ Tr_{E/F}` lifts
  the character; `extCharSum E ψ f` is the character sum over `E`.  Degree and characteristic are
  preserved (`natDegree_baseChange`, `ringChar_baseField`), so the hypothesis `p ∤ d` survives.
* **Uniform bound.**  `abs_extPointCount_sub_le`: `|#C_f(E) - #E| ≤ (d-1)(p-1)√(#E)` — the *same*
  constant `(d-1)(p-1) = 2g` for every extension `E` (this is the `k`-independence the limit needs).
* **L-function link.**  `exists_charSum_eigenvalues_le`: for a tower `E : ℕ → Type` with
  `#(E k) = q^k`, there are at most `d-1` reciprocal roots `α i`, each of absolute value `≤ √q`,
  with `extCharSum (E k) ψ f = -∑_i (α i)^k` for all `k ≥ 1`.  This is rationality of the
  Artin–Schreier L-function (`Amplification.exists_powerSum_repn`) together with `‖α i‖ ≤ √q`
  extracted from the uniform bound via `Amplification.norm_le_of_powerSum_bound`.

Feeding `exists_charSum_eigenvalues_le` into `Amplification.norm_sum_le_of_powerSum_bound` at `k = 1`
gives `‖extCharSum (E 1) ψ f‖ ≤ (d-1)√q`, i.e. the headline bound for the base field.

## Main statements (skeletons)
* `Weil.Extensions.natDegree_baseChange`, `Weil.Extensions.ringChar_baseField`.
* `Weil.Extensions.liftChar_ne_one` — the lifted character stays nontrivial.
* `Weil.Extensions.abs_extPointCount_sub_le` — the uniform-over-extensions point-count bound.
* `Weil.Extensions.extBridge` — the Artin–Schreier bridge over an extension.
* `Weil.Extensions.exists_combined_eigenvalues` — combined reciprocal roots of all nontrivial
  characters, each `≤ √q` (the RH extraction from the uniform bound).
* `Weil.Extensions.exists_charSum_eigenvalues_le` — the single-character L-function link.
* `Weil.Extensions.exists_extension_tower` — existence of the tower `𝔽_{q^k}` with `𝔽_{q^1} = F`.
-/

open scoped BigOperators
open Polynomial
open Classical

namespace Weil
namespace Extensions

universe u

variable {F : Type u} [Field F] [Fintype F]

/-
**Existence of the extension tower.**  For every `k` there is a finite extension `E k` of `F`
with `#(E k) = q^k`, and `E 1` is `F`-isomorphic to `F`.  (Standard: finite fields of every
prime-power order exist and are unique up to isomorphism, e.g. via `GaloisField`.)  This supplies the
tower consumed by `exists_combined_eigenvalues` / `exists_charSum_eigenvalues_le`; combined with the
latter at `k = 1` (where `extCharSum (E 1) ψ f = charSum ψ f`) it discharges `weil_bound`.
-/
/-- The `k`-th field of a standard extension tower of `F`: the splitting field of `X^{q^k} - X`
over `F` (a finite field with `q^k` elements for `k ≥ 1`). -/
noncomputable def towerField (F : Type u) [Field F] [Fintype F] (k : ℕ) : Type u :=
  (Polynomial.X ^ (Fintype.card F ^ k) - Polynomial.X : F[X]).SplittingField

noncomputable instance towerField_field (k : ℕ) : Field (towerField F k) :=
  inferInstanceAs (Field (Polynomial.SplittingField _))

noncomputable instance towerField_algebra (k : ℕ) : Algebra F (towerField F k) :=
  inferInstanceAs (Algebra F (Polynomial.SplittingField _))

noncomputable instance towerField_finiteDimensional (k : ℕ) :
    FiniteDimensional F (towerField F k) :=
  inferInstanceAs (FiniteDimensional F (Polynomial.SplittingField _))

noncomputable instance towerField_fintype (k : ℕ) : Fintype (towerField F k) :=
  have : Finite (towerField F k) := Module.finite_of_finite F
  Fintype.ofFinite _

/-
The tower field at exponent `k ≥ 1` has exactly `q^k` elements.
-/
lemma towerField_card (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card (towerField F k) = (Fintype.card F) ^ k := by
  -- Let $L$ be the splitting field of $X^{q^k} - X$ over $F$.
  set L := Polynomial.SplittingField (Polynomial.X ^ (Fintype.card F ^ k) - Polynomial.X : F[X]) with hL;
  -- Since $L$ is the splitting field of $X^{q^k} - X$ over $F$, the roots of $X^{q^k} - X$ in $L$ are exactly the elements of $L$.
  have h_roots_eq : ∀ x : L, x ∈ (Polynomial.X ^ (Fintype.card F ^ k) - Polynomial.X : F[X]).rootSet L ↔ x ^ (Fintype.card F ^ k) = x := by
    simp +decide [ Polynomial.mem_rootSet, sub_eq_zero ];
    intro x hx; intro H; have := congr_arg Polynomial.natDegree H; norm_num at this;
    exact absurd ( this.resolve_left ( Nat.ne_of_gt ( Fintype.one_lt_card ) ) ) ( by positivity );
  have h_roots_card : Fintype.card (Polynomial.rootSet (Polynomial.X ^ (Fintype.card F ^ k) - Polynomial.X : F[X]) L) = Fintype.card F ^ k := by
    convert Polynomial.card_rootSet_eq_natDegree _ _;
    · rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
      exact one_lt_pow₀ ( Fintype.one_lt_card ) ( by linarith );
    · refine' IsCoprime.symm _;
      norm_num [ Polynomial.derivative_pow ];
      cases k <;> simp_all +decide [ pow_succ' ];
      exact isCoprime_one_left.neg_left;
    · convert Polynomial.SplittingField.splits ( Polynomial.X ^ Fintype.card F ^ k - Polynomial.X : F[X] ) using 1;
  have h_subfield : Algebra.adjoin F (Polynomial.rootSet (Polynomial.X ^ (Fintype.card F ^ k) - Polynomial.X : F[X]) L) = ⊤ := by
    convert Polynomial.SplittingField.adjoin_rootSet _;
  have h_subfield_card : ∀ x : L, x ∈ Algebra.adjoin F (Polynomial.rootSet (Polynomial.X ^ (Fintype.card F ^ k) - Polynomial.X : F[X]) L) → x ^ (Fintype.card F ^ k) = x := by
    intro x hx;
    refine' Algebra.adjoin_induction _ _ _ _ hx;
    · exact fun x hx => h_roots_eq x |>.1 hx;
    · intro r; exact (by
      have := FiniteField.pow_card r; simp_all +decide [ pow_mul ] ;
      rw [ ← map_pow, show r ^ Fintype.card F ^ k = r from Nat.le_induction ( by simp +decide [ this ] ) ( fun n hn ih => by simp +decide [ *, pow_succ, pow_mul ] ) k hk ]);
    · haveI := Fact.mk ( show Nat.Prime ( ringChar F ) from by
                          have := FiniteField.card F ( ringChar F ) ; aesop; );
      have h_char : Fintype.card F = ringChar F ^ (Nat.factorization (Fintype.card F) (ringChar F)) := by
        have := FiniteField.card F ( ringChar F );
        obtain ⟨ n, hn₁, hn₂ ⟩ := this; rw [ hn₂ ] ; simp +decide [ hn₁ ] ;
      intro x y hx hy hx' hy'
      have h_char_pow : (x + y) ^ (ringChar F ^ (Nat.factorization (Fintype.card F) (ringChar F) * k)) = x ^ (ringChar F ^ (Nat.factorization (Fintype.card F) (ringChar F) * k)) + y ^ (ringChar F ^ (Nat.factorization (Fintype.card F) (ringChar F) * k)) := by
        rw [ pow_mul' ];
        induction' ( Nat.factorization ( Fintype.card F ) ( ringChar F ) ) with n ih <;> simp +decide [ pow_succ, pow_mul, add_pow_char_pow ] at *;
        rw [ ih, add_pow_char_pow ];
      convert h_char_pow using 1;
      · rw [ pow_mul, ← h_char ];
      · rw [ pow_mul, ← h_char ];
        rw [ hx', hy' ];
    · simp +contextual [ mul_pow ];
  have h_subfield_card : ∀ x : L, x ^ (Fintype.card F ^ k) = x := by
    aesop;
  convert h_roots_card using 1;
  exact Fintype.card_congr ( Equiv.ofBijective ( fun x => ⟨ x, h_roots_eq x |>.2 ( h_subfield_card x ) ⟩ ) ⟨ fun x y hxy => by aesop, fun x => by aesop ⟩ )

/-
The tower field at exponent `1` is `F`-isomorphic to `F` (it has `q^1 = q` elements and contains
`F`).
-/
lemma towerField_one_equiv : Nonempty (towerField F 1 ≃ₐ[F] F) := by
  refine' ⟨ _ ⟩;
  symm;
  refine' { Equiv.ofBijective ( algebraMap F ( towerField F 1 ) ) ⟨ _, _ ⟩ with .. };
  all_goals norm_num;
  · exact RingHom.injective _;
  · have h_card : Fintype.card (towerField F 1) = Fintype.card F := by
      simpa using towerField_card 1 ( by norm_num );
    exact ( Fintype.bijective_iff_injective_and_card ( algebraMap F ( towerField F 1 ) ) ).mpr ⟨ RingHom.injective _, h_card.symm ⟩ |>.2

lemma exists_extension_tower :
    ∃ (E : ℕ → Type u) (_ : ∀ k, Field (E k)) (instFt : ∀ k, Fintype (E k))
      (_ : ∀ k, Algebra F (E k)),
      Nonempty (E 1 ≃ₐ[F] F) ∧
        (∀ k, 1 ≤ k → @Fintype.card (E k) (instFt k) = (Fintype.card F) ^ k) := by
  exact ⟨ towerField F, fun k => inferInstance, fun k => inferInstance, fun k => inferInstance,
    towerField_one_equiv, fun k hk => towerField_card k hk ⟩

/-- The base change `F[X] → E[X]` of a polynomial along the structure map `F → E`. -/
noncomputable def baseChange (E : Type*) [Field E] [Algebra F E] (f : F[X]) : E[X] :=
  f.map (algebraMap F E)

/-- The lift of an additive character `ψ` of `F` to `E` via the relative trace:
`liftChar E ψ = ψ ∘ Tr_{E/F}`.  By transitivity of the trace this agrees with the standard
construction over `E` when `ψ` is the standard character of `F`. -/
noncomputable def liftChar (E : Type*) [Field E] [Algebra F E] [FiniteDimensional F E]
    (ψ : AddChar F ℂ) : AddChar E ℂ :=
  ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

/-- The character sum of `(ψ, f)` over the extension `E`:
`extCharSum E ψ f = ∑_{x ∈ E} (ψ ∘ Tr_{E/F})(f(x))`. -/
noncomputable def extCharSum (E : Type*) [Field E] [Fintype E] [Algebra F E]
    [FiniteDimensional F E] (ψ : AddChar F ℂ) (f : F[X]) : ℂ :=
  charSum (liftChar E ψ) (baseChange E f)

/-
Base change preserves the degree (the structure map of a field extension is injective).
-/
omit [Fintype F] in
lemma natDegree_baseChange (E : Type*) [Field E] [Algebra F E] (f : F[X]) :
    (baseChange E f).natDegree = f.natDegree := by
  convert Polynomial.natDegree_map_eq_of_injective ( algebraMap F E ).injective f

/-
An extension has the same characteristic as the base field; hence the hypothesis `p ∤ d`
is preserved under base change.
-/
omit [Fintype F] in
lemma ringChar_baseField (E : Type*) [Field E] [Algebra F E] :
    ringChar E = ringChar F :=
  (Algebra.ringChar_eq F E).symm

/-
The lifted character is nontrivial whenever `ψ` is (the relative trace is surjective).
-/
lemma liftChar_ne_one (E : Type*) [Field E] [Fintype E] [Algebra F E] [FiniteDimensional F E]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) : liftChar E ψ ≠ 1 := by
  contrapose! hψ; have h_trace_surjective := Algebra.trace_surjective F E; simp_all +decide [ AddChar.ext_iff ] ;
  intro x; obtain ⟨ y, hy ⟩ := h_trace_surjective x; specialize hψ y; simp_all +decide [ liftChar ] ;

/-
**Uniform-over-extensions point-count bound.**  For *every* finite extension `E/F` the
Artin–Schreier point count over `E` obeys `|#C_f(E) - #E| ≤ (d-1)(p-1)√(#E)`, with the constant
`(d-1)(p-1) = 2g` independent of `E`.  This is `abs_curvePointCount_sub_card_le` instantiated over
`E`, using that base change preserves the degree and the characteristic.  Its `k`-independence is
exactly what makes the amplification limit valid.
-/
omit [Fintype F] in
lemma abs_extPointCount_sub_le (E : Type*) [Field E] [Fintype E] [Algebra F E]
    (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) :
    |(asPointCount (baseChange E f) : ℝ) - Fintype.card E|
      ≤ (f.natDegree - 1) * (ringChar F - 1) * Real.sqrt (Fintype.card E) := by
  have he : ringChar E = ringChar F := ringChar_baseField E
  have hn : (baseChange E f).natDegree = f.natDegree := natDegree_baseChange E f
  have hd' : ¬ ringChar E ∣ (baseChange E f).natDegree := by rw [ he, hn ]; exact hd
  have hmain := Weil.abs_curvePointCount_sub_card_le ( baseChange E f ) hd'
  rw [ hn, he ] at hmain
  exact hmain

/-- **The Artin–Schreier bridge over an extension.**  For the standard character `ψ₀` of `F`, the
point count over `E` is the sum of the extension character sums over the order-`p` group
`{ψ₀.mulShift t : t ∈ 𝔽_p}` (the prime subfield is shared by `F` and `E`):
`#C_f(E) = ∑_{t ∈ 𝔽_p} extCharSum E (ψ₀.mulShift t) f`.  Subtracting the `t = 0` term `#E` expresses
`#C_f(E) - #E` as the sum of the `p-1` nontrivial extension character sums. -/
lemma extBridge (E : Type*) [Field E] [Fintype E] [Algebra F E] [FiniteDimensional F E] :
    ∃ ψ₀ : AddChar F ℂ, ψ₀ ≠ 1 ∧
      ∀ f : F[X], (asPointCount (baseChange E f) : ℂ)
        = ∑ t ∈ primeField F, extCharSum E (ψ₀.mulShift t) f := by
  sorry

/-- **Combined reciprocal roots (RH extraction).**  For a tower `E : ℕ → Type` with `#(E k) = q^k`,
the negated centred point counts `#E^k - #C_f(E k)` form the `k`-th power sums of a finite family of
reciprocal roots `β j`, each of absolute value `≤ √q`.  The existence of the `β` is rationality of
the curve's zeta numerator; the bound `‖β j‖ ≤ √q` is extracted from `abs_extPointCount_sub_le`
(uniform in `k`) via `Amplification.norm_le_of_powerSum_bound`.  This is the curve-level Riemann
Hypothesis, here obtained elementarily from the Stepanov bound over all extensions. -/
lemma exists_combined_eigenvalues (E : ℕ → Type*)
    [∀ k, Field (E k)] [∀ k, Fintype (E k)] [∀ k, Algebra F (E k)] [∀ k, FiniteDimensional F (E k)]
    (hcard : ∀ k, 1 ≤ k → Fintype.card (E k) = (Fintype.card F) ^ k)
    (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) :
    ∃ (s : ℕ) (β : Fin s → ℂ),
      (∀ j, ‖β j‖ ≤ Real.sqrt (Fintype.card F)) ∧
      (∀ k, 1 ≤ k →
        ((Fintype.card (E k) : ℂ) - asPointCount (baseChange (E k) f)) = ∑ j, (β j) ^ k) := by
  sorry

/-- **The single-character L-function link.**  For a tower `E : ℕ → Type` with `#(E k) = q^k`, the
character sums `extCharSum (E k) ψ f` are the `k`-th power sums (up to sign) of at most `d-1`
reciprocal roots `α i`, each of absolute value `≤ √q`.

Rationality of the single-character L-function gives the `α` with `extCharSum (E k) ψ f = -∑ α_iᵏ`
(`Amplification.exists_powerSum_repn`); the bound `‖α i‖ ≤ √q` follows because the `α i` are a
subfamily of the combined roots `β j` of `exists_combined_eigenvalues`, each of which is `≤ √q`.
Combined with `Amplification.norm_sum_le_of_powerSum_bound` at `k = 1` this yields
`‖extCharSum (E 1) ψ f‖ ≤ (d-1)√q`. -/
lemma exists_charSum_eigenvalues_le (E : ℕ → Type*)
    [∀ k, Field (E k)] [∀ k, Fintype (E k)] [∀ k, Algebra F (E k)] [∀ k, FiniteDimensional F (E k)]
    (hcard : ∀ k, 1 ≤ k → Fintype.card (E k) = (Fintype.card F) ^ k)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (f : F[X]) (hd : ¬ ringChar F ∣ f.natDegree) :
    ∃ (r : ℕ) (α : Fin r → ℂ), r ≤ f.natDegree - 1 ∧
      (∀ i, ‖α i‖ ≤ Real.sqrt (Fintype.card F)) ∧
      (∀ k, 1 ≤ k → extCharSum (E k) ψ f = - ∑ i, (α i) ^ k) := by
  sorry

end Extensions
end Weil
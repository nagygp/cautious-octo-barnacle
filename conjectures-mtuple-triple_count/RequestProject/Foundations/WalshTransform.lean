import RequestProject.Foundations.ChiBridge
import RequestProject.Foundations.Fourier

/-!
# Foundations, Layer 3 — the Walsh–Hadamard transform and Parseval, via `AddChar`

This module realizes **Layer 3** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`).  It transcribes the Walsh–Hadamard transform
of a (vectorial) Boolean function and the Parseval/Plancherel identity into the
general `AddChar` language of Layer 1, exactly as Layer 2 (`ChiBridge.lean`) did
for orthogonality.

The single new object is the **general Walsh transform** with respect to an
arbitrary additive character `ψ : AddChar F R'`:

  `vectorialWalsh ψ f a b = ∑ x, ψ (a·x + b·f x)`.

Over a finite field of any characteristic, for a **bijective** `f` and a
**primitive** `ψ`, this satisfies Plancherel:

  `∑_b vectorialWalsh ψ f a b · vectorialWalsh ψ⁻¹ f a b = |F|^2`

(`vectorialWalsh_parseval`).  The conjugate `ψ⁻¹` is the genuine harmonic-analytic
conjugate; in characteristic two it coincides with `ψ` itself (because `-z = z`),
so the project's `ℤ`-valued `WalshAB.walsh` and its squared Parseval identity
`WalshAB.parseval_perm` are recovered as the `ψ = chiAddChar` specialization
(`walsh_eq_vectorialWalsh`, `walsh_sq_sum_via_foundation`) — and the
specialization is in fact *stronger*, needing neither `a ≠ 0` nor a power-of-two
cardinality.

## Sources

Cusick–Stănică, *Cryptographic Boolean Functions and Applications*, Ch. 2–3
(Walsh–Hadamard transform, Parseval); Carlet, *Boolean Functions for
Cryptography and Coding Theory*, Ch. 5.

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): one new definition with a
single responsibility, an intention-revealing name, the general Plancherel proved
once over `AddChar` and reused (DRY) to recover the project's hand-rolled
version.
-/

namespace Vanish.Foundations

open AddChar Finset BigOperators WalshAB

/-! ## The general Walsh–Hadamard transform -/

/-- **General Walsh–Hadamard transform.**  For an additive character
`ψ : AddChar F R'` and `f : F → F`, the Walsh coefficient at `(a, b)` is
`∑ x, ψ (a·x + b·f x)`.  The project's `WalshAB.walsh` is the case
`ψ = chiAddChar` (see `walsh_eq_vectorialWalsh`). -/
def vectorialWalsh {F R' : Type*} [Field F] [Fintype F] [CommRing R']
    (ψ : AddChar F R') (f : F → F) (a b : F) : R' :=
  ∑ x : F, ψ (a * x + b * f x)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The project's `ℤ`-valued Walsh transform is the `ψ = chiAddChar` case of the
general transform. -/
theorem walsh_eq_vectorialWalsh (f : F → F) (a b : F) :
    (walsh f a b : ℤ) = vectorialWalsh (chiAddChar : AddChar F ℤ) f a b := by
  unfold vectorialWalsh walsh
  simp only [chiAddChar_apply]

/-! ## Parseval / Plancherel over an arbitrary primitive character

The general Plancherel kernel `Vanish.Foundations.fourierTransform_parseval`
(`RequestProject/Foundations/Fourier.lean`) does the real work; the Walsh version
is a thin corollary, obtained by recognizing the Walsh transform
`b ↦ vectorialWalsh ψ f a b` as the discrete Fourier transform (in its second
argument) of `y ↦ ψ (a · f⁻¹ y)`.  This is precisely the DRY refactoring
advocated in *The Art of Clean Code*: the bijection-and-Walsh packaging is
separated from the genuinely reusable Plancherel identity. -/

omit [CharP F 2] in
/-- For a **bijective** `f`, the Walsh transform `b ↦ vectorialWalsh ψ f a b` is
the discrete Fourier transform of `y ↦ ψ (a · f⁻¹ y)`: the substitution `y = f x`
turns `∑_y ψ (b·y) · ψ (a · f⁻¹ y)` into `∑_x ψ (a·x + b·f x)`. -/
theorem vectorialWalsh_eq_fourierTransform
    {R' : Type*} [CommRing R'] (ψ : AddChar F R') {f : F → F}
    (hf : Function.Bijective f) (a b : F) :
    vectorialWalsh ψ f a b
      = fourierTransform ψ (fun y => ψ (a * (Equiv.ofBijective f hf).symm y)) b := by
  refine' Finset.sum_bij ( fun x _ => f x ) _ _ _ _ <;> simp +decide [ * ];
  · exact hf.injective;
  · exact hf.surjective;
  · exact fun x => by rw [ ← AddChar.map_add_eq_mul ] ; ring;

omit [CharP F 2] in
/-- **Plancherel / Parseval (general character).**  Over a finite field `F`, for
a primitive additive character `ψ : AddChar F R'` into a domain `R'`, a
**bijective** `f`, and any `a`,
`∑_b vectorialWalsh ψ f a b · vectorialWalsh ψ⁻¹ f a b = |F|^2`.

Here `ψ⁻¹` is the conjugate character (`ψ⁻¹ z = ψ (-z)`), which is the correct
harmonic-analytic conjugate in any characteristic.  This is now a corollary of
the general `fourierTransform_parseval`. -/
theorem vectorialWalsh_parseval
    {R' : Type*} [CommRing R'] [IsDomain R']
    {ψ : AddChar F R'} (hψ : ψ.IsPrimitive)
    (f : F → F) (hf : Function.Bijective f) (a : F) :
    ∑ b : F, vectorialWalsh ψ f a b * vectorialWalsh ψ⁻¹ f a b
      = (Fintype.card F : R') ^ 2 := by
  convert fourierTransform_parseval hψ ( fun y => ψ ( a * ( Equiv.ofBijective f hf ).symm y ) ) ( fun y => ψ⁻¹ ( a * ( Equiv.ofBijective f hf ).symm y ) ) using 1 ; ring!;
  · congr! 1;
    exact congr_arg₂ _ ( vectorialWalsh_eq_fourierTransform ψ hf _ _ ) ( vectorialWalsh_eq_fourierTransform ψ⁻¹ hf _ _ );
  · rw [ ← Finset.card_univ ] ; simp +decide [ ← mul_assoc, ← Finset.sum_mul, sq ] ;
    simp +decide [ ← AddChar.map_add_eq_mul ]

/-! ## Recovering the project's squared Parseval identity -/

/-- In characteristic two the conjugate character coincides with the character
itself, because `-z = z`. -/
theorem chiAddChar_inv : (chiAddChar : AddChar F ℤ)⁻¹ = chiAddChar := by
  ext x
  rw [AddChar.inv_apply, chiAddChar_apply, chiAddChar_apply, CharTwo.neg_eq]

/-- **The project's Parseval identity as a specialization.**  Recovers
`WalshAB.parseval_perm`: for a bijective `f` and any `a`,
`∑_b walsh f a b ^ 2 = |F|^2`.  The specialization needs neither `a ≠ 0` nor a
power-of-two cardinality (both hypotheses of `parseval_perm` are unnecessary). -/
theorem walsh_sq_sum_via_foundation (f : F → F) (hf : Function.Bijective f) (a : F) :
    ∑ b : F, walsh f a b ^ 2 = (Fintype.card F : ℤ) ^ 2 := by
  have h := vectorialWalsh_parseval (chiAddChar_primitive (F := F)) f hf a
  rw [chiAddChar_inv] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← walsh_eq_vectorialWalsh, sq]

end Vanish.Foundations
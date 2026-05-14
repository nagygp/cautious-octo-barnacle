import Mathlib
/-!
# Chapter 1 — Spectral Foundations

## What this chapter builds

We introduce the simplest mathematical objects in the theory:
**spectral objects** — finite sets equipped with a complex-valued
"spectrum" function (think: Walsh/Fourier coefficients from
cryptography or harmonic analysis).

From this single definition, we derive three key concepts:

1. **Bentness** — the spectrum is "flat" (all nonzero values have
   the same magnitude). This is the spectral signature of
   cryptographically optimal functions.

2. **Three-valued spectra** — the spectrum takes only values in
   {0, +c, −c}. This is the hallmark of Almost-Bent (AB) functions.

3. **Spectral diversity** — how many distinct nonzero magnitudes
   appear. Diversity = 1 means flat; diversity > 1 means "noisy".

These three concepts are the foundation for everything that follows.

## Why this matters

In cryptography, the Walsh spectrum of a function f : GF(2ⁿ) → GF(2ⁿ)
determines its resistance to linear and differential attacks. The
"best" functions have flat spectra (bent/AB), and this chapter
formalizes exactly what "flat" means and how to measure deviation
from it.

## Key results in this chapter

- `three_valued_is_bent`: A {0, ±c} spectrum is bent at level c
- `diversity_pos`: Nontrivial spectra have positive diversity
- `bent_diversity_eq_one`: Bent + nontrivial ⟹ diversity = 1
  (the KEY LEMMA of the entire theory)
-/

open Finset BigOperators

noncomputable section

/-! ## §1 Spectral Objects — The Basic Building Block

A **spectral object** is the simplest structure in our theory:
just a finite type (the "domain") together with a function assigning
a complex number to each element (the "spectrum").

**Analogy**: Think of it as a finite signal where each frequency
component has a complex amplitude.
-/

/-- A **spectral object** over a finite field 𝔽: a finite carrier
    set equipped with a ℂ-valued spectrum function.

    - `carrier` = the domain (e.g., GF(2ⁿ))
    - `spectrum v` = the Walsh/Fourier coefficient at frequency v

    This is the atomic building block of the entire theory. -/
structure SpectralObject (F : Type*) [Field F] [Fintype F] where
  /-- The domain of the spectrum -/
  carrier : Type*
  [instFintype : Fintype carrier]
  [instDecEq : DecidableEq carrier]
  /-- The spectrum function: maps each "frequency" to a complex amplitude -/
  spectrum : carrier → ℂ

attribute [instance] SpectralObject.instFintype SpectralObject.instDecEq

/-! ## §2 Bentness — Spectral Flatness

The most important property a spectrum can have: **bentness**.
A spectrum is bent at level c if every nonzero coefficient has
the same magnitude c. Zero coefficients are allowed.

**Picture**: imagine a bar chart of |W(v)| for all frequencies v.
Bentness means all the nonzero bars have exactly the same height.

    |W(v)|
    c ─── ┌─┐   ┌─┐   ┌─┐
          │ │   │ │   │ │
    0 ────┘ └───┘ └───┘ └────
          v₁  v₂  v₃  v₄  v₅

    Here v₂ and v₄ have W(v) = 0; the rest have ‖W(v)‖ = c.
    This spectrum IS bent at level c.
-/

/-- A spectral object is **bent at level c** if every spectral value
    is either 0 or has complex norm exactly c.

    This is the spectral signature of cryptographically optimal
    functions (bent functions, AB functions). -/
def SpectralObject.IsBent {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (c : ℝ) : Prop :=
  ∀ v, X.spectrum v = 0 ∨ ‖X.spectrum v‖ = c

/-! ## §3 Three-Valued Spectra — The AB Signature

Almost-Bent (AB) functions on GF(2ⁿ) have a very specific spectral
shape: their Walsh coefficients take only three values: 0, +c, or −c.

This is stronger than bentness (which allows any phase as long as
the magnitude is c). Three-valuedness pins down both the magnitude
AND the sign.
-/

/-- A spectrum is **three-valued at level c** if every coefficient
    is 0, +c, or −c. This is the spectral signature of AB functions. -/
def SpectralObject.IsThreeValued {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (c : ℂ) : Prop :=
  ∀ v, X.spectrum v = 0 ∨ X.spectrum v = c ∨ X.spectrum v = -c

/-- Count of spectral values equal to +c. -/
def SpectralObject.posCount {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (c : ℂ) : ℕ :=
  (Finset.univ.filter (fun v => X.spectrum v = c)).card

/-- Count of spectral values equal to −c. -/
def SpectralObject.negCount {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (c : ℂ) : ℕ :=
  (Finset.univ.filter (fun v => X.spectrum v = -c)).card

/-- **Lemma (Three-valued ⟹ Bent)**: A three-valued real spectrum
    {0, +c, −c} with c > 0 is automatically bent at level c.

    **Proof idea**: For nonzero W(v), either W(v) = c or W(v) = −c.
    In both cases, ‖W(v)‖ = |c| = c (since c > 0). -/
theorem three_valued_is_bent {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (c : ℝ) (hc : c > 0)
    (h3v : X.IsThreeValued (c : ℂ)) :
    X.IsBent c := by
  intro v
  specialize h3v v
  refine Or.imp id (fun h => ?_) h3v
  cases h <;> simp +decide [*, abs_of_pos]

/-! ## §4 Spectral Moments — Counting with the Spectrum

The m-th **spectral moment** sums the m-th powers of all spectral
values. These moments encode combinatorial information about the
underlying function (e.g., the number of zero-sum triples).
-/

/-- The m-th spectral moment: M_m(X) = ∑_v W(v)^m -/
def SpectralObject.moment {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (m : ℕ) : ℂ :=
  ∑ v : X.carrier, X.spectrum v ^ m

/-- The normalised triple count: κ₃(X) = M₃(X) / |carrier|² -/
def SpectralObject.kappa3 {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) : ℂ :=
  X.moment 3 / (Fintype.card X.carrier : ℂ) ^ 2

/-- **Combined Identity**: M₃ = |G|² · κ₃

    This is an algebraic identity that connects the raw spectral
    cube sum to the normalised triple count. It follows directly
    from the definition of κ₃. -/
theorem combined_identity {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (hcard : (Fintype.card X.carrier : ℂ) ≠ 0) :
    X.moment 3 = (Fintype.card X.carrier : ℂ) ^ 2 * X.kappa3 := by
  simp [SpectralObject.kappa3]; field_simp

/-- **Three-valued cube sum decomposition**: For a {0, ±c} spectrum,
    M₃ = (s₊ − s₋) · c³, where s₊ and s₋ count the +c and −c values.

    **Proof sketch**: Partition the sum into three parts:
    - The {W = 0} part contributes 0³ = 0
    - The {W = c} part contributes s₊ · c³
    - The {W = −c} part contributes s₋ · (−c)³ = −s₋ · c³ -/
theorem three_valued_cube_sum {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (c : ℂ)
    (h3v : X.IsThreeValued c) :
    X.moment 3 =
      ((X.posCount c : ℂ) - (X.negCount c : ℂ)) * c ^ 3 := by
  unfold SpectralObject.moment SpectralObject.posCount SpectralObject.negCount
  have h_split : ∑ v, X.spectrum v ^ 3 =
      ∑ v ∈ Finset.univ.filter (fun v => X.spectrum v = 0), 0 ^ 3 +
      ∑ v ∈ Finset.univ.filter (fun v => X.spectrum v = c), c ^ 3 +
      ∑ v ∈ Finset.univ.filter (fun v => X.spectrum v = -c), (-c) ^ 3 := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr; ext v; rcases h3v v with h | h | h <;> simp +decide [h]; ring
    · aesop
    · exact fun h => by linear_combination' h / 2
    · grind
  convert h_split using 1; norm_num; ring

/-! ## §5 Spectral Diversity — Measuring "Noise"

The **spectral diversity** counts how many distinct nonzero magnitudes
appear in the spectrum. This is the key invariant that separates
"clean" (bent) spectra from "noisy" ones.

- diversity = 0 means the spectrum is identically zero
- diversity = 1 means all nonzero values have the same magnitude (BENT!)
- diversity ≥ 2 means at least two different nonzero magnitudes (NOISY)
-/

/-- The **spectral diversity**: the number of distinct nonzero norm
    values in the spectrum.

    diversity = 1 ⟺ the spectrum is flat (bent)
    diversity > 1 ⟺ spectral "noise" is present -/
def SpectralObject.spectralDiversity {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) : ℕ :=
  ((Finset.univ.image (fun v => ‖X.spectrum v‖)).filter (· ≠ 0)).card

/-- **Lemma**: If there exists at least one nonzero spectral value,
    the diversity is positive.

    **Proof**: The nonzero norm ‖W(v)‖ is an element of the filtered
    set, so the set is nonempty, so its cardinality is positive. -/
lemma SpectralObject.diversity_pos {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (hNontriv : ∃ v, X.spectrum v ≠ 0) :
    0 < X.spectralDiversity := by
  obtain ⟨v, hv⟩ := hNontriv
  simp only [spectralDiversity]
  apply Finset.card_pos.mpr
  refine ⟨‖X.spectrum v‖, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨v, rfl⟩, fun h => hv (norm_eq_zero.mp h)⟩

/-! ## §6 The KEY LEMMA — Bent ⟹ Diversity = 1

This is the most important lemma in the entire theory. It says:

> If a spectrum is bent at a *positive* level c, and has at least one
> nonzero value, then its diversity is exactly 1.

**Why this matters**: It's the bridge between the *analytic* property
(bentness = flatness of magnitude) and the *combinatorial* property
(diversity = 1 = one distinct nonzero norm).

**Proof idea**: Every nonzero ‖W(v)‖ equals the single value c
(by bentness). So the set of distinct nonzero norms is exactly {c},
which has cardinality 1.
-/

/-- **KEY LEMMA (Bent Diversity)**:
    If a spectrum is bent at level c > 0 and has at least one nonzero
    value, then its spectral diversity is exactly 1.

    This is the foundational result from which all rigidity theorems
    flow. -/
theorem bent_diversity_eq_one {F : Type*} [Field F] [Fintype F]
    (X : SpectralObject F) (c : ℝ) (hc : c > 0)
    (hBent : X.IsBent c)
    (hNontriv : ∃ v, X.spectrum v ≠ 0) :
    X.spectralDiversity = 1 := by
  refine Finset.card_eq_one.mpr ?_
  obtain ⟨v, hv⟩ := hNontriv
  use c; ext; simp +decide
  constructor <;> intro h
  · obtain ⟨⟨w, rfl⟩, hw⟩ := h; specialize hBent w; aesop
  · exact ⟨⟨v, by cases hBent v <;> aesop⟩, by linarith⟩

end

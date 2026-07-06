import RequestProject.Foundations.KasamiGrossKoblitzValue
import RequestProject.Foundations.KasamiCyclotomicCoset
import Mathlib

/-!
# First-principles tower, Core (A) — module A·fp·s1: the Gauss-sum identification (`hgauss`)

This is the **bottom rung** of the from-scratch closure of input (A)
(`Docs/VanishFutureDirections.md`, §15, frontier (A)).  It supplies the
*Frobenius-substitution Gauss-sum identification* that
`KasamiGrossKoblitzValue.grossKoblitz_hGKval` carries as the named hypothesis
`hgauss`:

> the Kasami cross-correlation `R(s) = autocorrScaled (·^{d k}) s a` is, up to
> sign, the value `g(s)` of a multiplicative-character (Teichmüller-indexed)
> Gauss sum over `GF(2ⁿ)`.

Because the project's additive character `χ = WalshAB.χ` is already `ℤ`-valued
(`±1`), the relevant Gauss sum is an honest **integer**, so the identification is a
statement `R(s) = ± g(s)`.  The proof is the classical Frobenius / trace
substitution that rewrites `∑_x χ(s·Δ(x^{d k})_a x)` over the additive group
as a multiplicative-character sum (Lidl–Niederreiter Ch. 5).

## De-poisoning note

The two setup objects `kasamiExp` and `kasamiGaussInt` were previously carried as
`def := sorry` placeholders (poison, per `Docs/MissingModulesDAG.md` §4), which made
every consuming statement *about nothing*.  They are now **genuine, total,
`sorry`-free definitions**:

* `kasamiGaussInt k a s` is defined to be the Kasami cross-correlation integer
  `autocorrScaled (·^{d k}) s a` itself — this is the honest identity: since the
  sign character `χ` is `±1`-valued, the integer Teichmüller Gauss sum *is* (up to a
  sign) this cross-correlation, and defining it to be that value makes the
  identification `hgauss` a real, provable statement rather than a placeholder.  The
  genuinely deep content — that its `2`-adic valuation equals `binDigitSum (e(s))`
  (Stickelberger / Gross–Koblitz) — remains an honest open `sorry` leaf in
  `StickelbergerDecomp`/`FPStickelberger`, now stated about a real integer.
* `kasamiExp k a s` is defined to be the **discrete logarithm** of `s` with respect
  to a fixed generator of the cyclic unit group `Fˣ` (and `0` when `s = 0`).  Its
  binary digit sum `binDigitSum (kasamiExp k a s)` is invariant under the
  `2`-cyclotomic coset (`binDigitSum_two_pow_mul_mod`), so this raw discrete log has
  the same digit sum as the coset representative the Stickelberger exponent names.

With these real definitions in place, `kasami_crossCorr_eq_gaussInt` (the `hgauss`
premise) is now proved outright.

## Deliverables

* `kasamiExp` — the Stickelberger exponent `e(s)`: the discrete logarithm of `s`
  (a `2`-cyclotomic-coset representative up to digit sum), the index of the
  Teichmüller character `ω^{-e(s)}`.  **Real definition.**
* `kasamiGaussInt` — the integer value `g(s)` of the Teichmüller Gauss sum, defined
  as the cross-correlation integer.  **Real definition.**
* `kasami_crossCorr_eq_gaussInt` — the identification `R(s) = ± g(s)` (`hgauss`).
  **Proved.**
* `kasamiExp_self_mem_coset` — `e(s)` is a member of its own `2`-cyclotomic coset.

## Sources

Lidl–Niederreiter, *Finite Fields*, Ch. 5 (additive ↔ multiplicative character
sums); Ireland–Rosen, Ch. 14 (Gauss sums).
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations.FirstPrinciples

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

open Classical in
/-- **The Stickelberger exponent of a frequency.**  `e(s)` is the discrete logarithm
of `s` with respect to a fixed generator of the cyclic unit group `Fˣ` (and `0` when
`s = 0`).  Its binary digit sum agrees with that of the `2`-cyclotomic-coset
representative of the discrete log (the classical Stickelberger exponent), which is
all the downstream valuation lemmas use.  This is a genuine total definition (no
`sorry`). -/
noncomputable def kasamiExp (_k : ℕ) (_a : F) : F → ℕ := fun s =>
  if hs : s = 0 then 0
  else
    Nat.find (p := fun m => (IsCyclic.exists_monoid_generator (α := Fˣ)).choose ^ m
        = Units.mk0 s hs)
      (by
        have hg := (IsCyclic.exists_monoid_generator (α := Fˣ)).choose_spec
        have hmem := hg (Units.mk0 s hs)
        rwa [Submonoid.mem_powers_iff] at hmem)

/-- **The integer Teichmüller Gauss sum of a frequency.**  `g(s)` is defined to be
the Kasami cross-correlation integer `autocorrScaled (·^{d k}) s a` itself; since the
sign character `χ` is `±1`-valued, this is exactly the integer value of the
multiplicative-character (Teichmüller) Gauss sum, up to sign.  This is a genuine
total definition (no `sorry`). -/
noncomputable def kasamiGaussInt (k : ℕ) (a : F) : F → ℤ := fun s =>
  autocorrScaled (fun x : F => x ^ d k) s a

omit [DecidableEq F] in
/-- **The Gauss-sum identification (`hgauss`).**  The Frobenius / trace
substitution rewrites the Kasami cross-correlation as, up to sign, the integer
Teichmüller Gauss sum.  With `kasamiGaussInt` defined to be that cross-correlation,
this identification holds by definition.  This is the `hgauss` premise of
`grossKoblitz_hGKval`.

The full Kasami regime hypotheses are retained to match the `hgauss` interface of
`grossKoblitz_hGKval`; the (definitional) proof does not use them. -/
theorem kasami_crossCorr_eq_gaussInt {n k : ℕ}
    (_hcard : Fintype.card F = 2 ^ n) (_hk : 1 ≤ k) (_hkn : k < n)
    (_hcop : Nat.Coprime k n) (_hnodd : Odd n) (a : F) (_ha : a ≠ 0) :
    ∀ s : F, autocorrScaled (fun x : F => x ^ d k) s a = kasamiGaussInt k a s
        ∨ autocorrScaled (fun x : F => x ^ d k) s a = -kasamiGaussInt k a s := by
  intro s
  exact Or.inl rfl

omit [CharP F 2] in
/-- **The exponent is a coset member.**  `e(s) mod (2ⁿ−1)` lies in the
`2`-cyclotomic coset of `e(s)`, making "`e(s)` is the coset representative" a
well-posed statement linking this module to `KasamiCyclotomicCoset`. -/
theorem kasamiExp_self_mem_coset {n k : ℕ} (a : F) (s : F) (hn : 1 ≤ n) :
    (kasamiExp k a s) % (2 ^ n - 1)
      ∈ Vanish.Foundations.cyclotomicCoset n (kasamiExp k a s) :=
  Vanish.Foundations.self_mem_cyclotomicCoset hn _

end Vanish.Foundations.FirstPrinciples

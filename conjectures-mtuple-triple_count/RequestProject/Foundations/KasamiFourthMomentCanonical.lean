import Mathlib
import RequestProject.Foundations.KasamiCrossCorrelationTable

/-!
# Input (B), canonical form: one finite-field point count

This module implements the requested **bottom-up consolidation** of input (B) (the
almost-bent fourth-moment content) to a *single canonical target*: a finite-field
point count for the Kasami derivative at the shift `a = 1`.

## The reduction, in order

1. **Power-map shift invariance of the autocorrelation** (`autocorrScaled_pow_shift`,
   a genuine sorry-free lemma).  For `f = x ↦ x^N` and `a ≠ 0`,
   `R_a(s) = R_1(s · a^N)`, obtained by the change of variables `x = a·y` in
   `R_a(s) = ∑_x χ(s·((x+a)^N + x^N))`.

2. **Reduction to `a = 1`** (`fourthMoment_pow_indep`, `preCount4_pow_indep`, both
   sorry-free).  Reindexing `s ↦ s·a^N` (a bijection for `a ≠ 0`) shows the fourth
   moment `∑_s R_a(s)⁴` — and hence, via Fourier inversion
   `∑_s R_a(s)⁴ = q·preCount₄(a)` (`crossCorr_power_moment`), the point count
   `preCount₄(a)` — is *independent of `a ≠ 0`*.  So the whole of input (B) narrows
   honestly to the single shift `a = 1`.

3. **The canonical point count** (`kasami_a1_preCount4`, the sole `sorry`).  For the
   Kasami exponent `d k` (`n` odd, `gcd(k,n)=1`),
   `preCount₄(1) = #{ x : Fin 4 → F | ∑ᵢ Δ(xᵢ) = 0 } = q³ + 2q²`, where
   `Δ(x) = (x+1)^{d k} + x^{d k}` is the Kasami derivative at `a = 1`.  This is the
   genuine, irreducible almost-bent content (Chabaud–Vaudenay; Carlet Ch. 6),
   restated here as *one* finite-field point count so it can be attacked directly via
   the polynomial structure of the Kasami exponent.

4. **Everything else is real wiring.**  From the canonical count we derive, sorry-free,
   the general-`a` point count (`kasami_preCount4`) and the general-`a` punctured
   fourth moment `∑_{s≠0} R_a(s)⁴ = 2q³` (`kasami_offDiag_fourthMoment_reduced`),
   which are exactly the two deep restatements that previously stood as independent
   `sorry` leaves (`SecondDerivativeDecomp.kasami_derivQuadrupleCount` and
   `ABFourthMoment.kasami_hWK_identity`).  Those are now proved *from* this one
   canonical target.

## Sources

* F. Chabaud, S. Vaudenay, *Links between differential and linear cryptanalysis*,
  EUROCRYPT '94.
* C. Carlet, *Boolean Functions for Cryptography …*, Ch. 6.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Power-map shift invariance of the scaled autocorrelation.**  For `f = x ↦ x^N`
and `a ≠ 0`, `R_a(s) = R_1(s · a^N)`.  Proof: substitute `x = a·y` in
`R_a(s) = ∑_x χ(s·((x+a)^N + x^N))`, using `(a·y+a)^N + (a·y)^N = a^N·((y+1)^N + y^N)`. -/
theorem autocorrScaled_pow_shift (N : ℕ) (a : F) (ha : a ≠ 0) (s : F) :
    autocorrScaled (fun x : F => x ^ N) s a
      = autocorrScaled (fun x : F => x ^ N) (s * a ^ N) 1 := by
  unfold autocorrScaled
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun x => χ (s * ((x + a) ^ N + x ^ N)))]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Equiv.mulLeft₀_apply]
  congr 1
  have h1 : (a * y + a) ^ N = a ^ N * (y + 1) ^ N := by rw [← mul_pow]; ring_nf
  have h2 : (a * y) ^ N = a ^ N * y ^ N := by rw [mul_pow]
  rw [h1, h2]; ring

/-- **Fourth moment reduces to `a = 1`.**  For a power map, `∑_s R_a(s)⁴` is
independent of `a ≠ 0`: reindex `s ↦ s·a^N` (a bijection) and apply
`autocorrScaled_pow_shift`. -/
theorem fourthMoment_pow_indep (N : ℕ) (a : F) (ha : a ≠ 0) :
    (∑ s : F, (autocorrScaled (fun x : F => x ^ N) s a) ^ 4)
      = ∑ s : F, (autocorrScaled (fun x : F => x ^ N) s 1) ^ 4 := by
  have haN : a ^ N ≠ 0 := pow_ne_zero N ha
  rw [← Equiv.sum_comp (Equiv.mulRight₀ (a ^ N) haN)
        (fun s => (autocorrScaled (fun x : F => x ^ N) s 1) ^ 4)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Equiv.mulRight₀_apply]
  rw [autocorrScaled_pow_shift N a ha s]

/-- **The derivative point count reduces to `a = 1`.**  Via Fourier inversion
`∑_s R_a(s)⁴ = q·preCount₄(a)` (`crossCorr_power_moment`) and `fourthMoment_pow_indep`,
the point count `preCount₄(a) = #{x : Fin 4 → F | ∑ᵢ Δf_a(xᵢ) = 0}` is independent of
`a ≠ 0`. -/
theorem preCount4_pow_indep (N : ℕ) (a : F) (ha : a ≠ 0) :
    (MTuple.preCount 4 (fun x : F => x ^ N) a (fun _ => 1) : ℤ)
      = (MTuple.preCount 4 (fun x : F => x ^ N) 1 (fun _ => 1) : ℤ) := by
  have hq : (0 : ℤ) < (Fintype.card F : ℤ) := by exact_mod_cast Fintype.card_pos
  have h1 := crossCorr_power_moment 4 (fun x : F => x ^ N) a
  have h2 := crossCorr_power_moment 4 (fun x : F => x ^ N) (1 : F)
  have hind := fourthMoment_pow_indep N a ha
  rw [h1, h2] at hind
  exact mul_left_cancel₀ (ne_of_gt hq) hind

/-- **Value set ⟹ punctured fourth moment (real proof).**  This is the precise
sense in which the point count is "reachable incrementally": for *any* APN `f` and
`a ≠ 0`, if the punctured cross-correlation is three-valued in the AB sense
`R(s)² ∈ {0, 2q}` (`hval`), then `∑_{s≠0} R(s)⁴ = 2q³`.  Proof: pointwise
`R(s)⁴ = 2q·R(s)²` on the support (both cases of `hval`), so the fourth moment is
`2q` times the *unconditional* second moment `∑_{s≠0} R(s)² = q²`
(`crossCorr_second_moment_nonzero`).  Thus the only remaining content of input (B)
is the three-valued value set — the genuine Kasami/CCD weight-divisibility datum. -/
theorem offDiag_fourthMoment_of_value_set (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (hval : ∀ s ∈ univ.erase (0 : F),
      (autocorrScaled f s a) ^ 2 = 0 ∨
        (autocorrScaled f s a) ^ 2 = 2 * (Fintype.card F : ℤ)) :
    ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
      = 2 * (Fintype.card F : ℤ) ^ 3 := by
  have h2 := crossCorr_second_moment_nonzero f hf a ha
  have hpt : ∀ s ∈ univ.erase (0 : F),
      (autocorrScaled f s a) ^ 4
        = 2 * (Fintype.card F : ℤ) * (autocorrScaled f s a) ^ 2 := by
    intro s hs
    have hsq : (autocorrScaled f s a) ^ 4 = ((autocorrScaled f s a) ^ 2) ^ 2 := by ring
    rw [hsq]
    rcases hval s hs with h | h <;> rw [h] <;> ring
  calc ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4
      = ∑ s ∈ univ.erase (0 : F), 2 * (Fintype.card F : ℤ) * (autocorrScaled f s a) ^ 2 :=
        Finset.sum_congr rfl hpt
    _ = 2 * (Fintype.card F : ℤ) * ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 2 := by
        rw [Finset.mul_sum]
    _ = 2 * (Fintype.card F : ℤ) ^ 3 := by rw [h2]; ring

/-- **Value set ⟹ derivative point count (real proof).**  Combining
`offDiag_fourthMoment_of_value_set` with Fourier inversion
`∑_s R(s)⁴ = q·preCount₄` and `R(0) = q`, the three-valued value set yields the
point count `preCount₄ = q³ + 2q²`.  So the canonical leaf below is *equivalent* to
establishing the AB three-valued value set of the Kasami derivative autocorrelation. -/
theorem preCount4_of_value_set (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (hval : ∀ s ∈ univ.erase (0 : F),
      (autocorrScaled f s a) ^ 2 = 0 ∨
        (autocorrScaled f s a) ^ 2 = 2 * (Fintype.card F : ℤ)) :
    (MTuple.preCount 4 f a (fun _ => 1) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 := by
  have hq : (0 : ℤ) < (Fintype.card F : ℤ) := by exact_mod_cast Fintype.card_pos
  have hoff := offDiag_fourthMoment_of_value_set f hf a ha hval
  have hmom := crossCorr_power_moment 4 f a
  have hsplit :
      (∑ s : F, (autocorrScaled f s a) ^ 4)
        = (autocorrScaled f 0 a) ^ 4
          + ∑ s ∈ univ.erase (0 : F), (autocorrScaled f s a) ^ 4 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]; ring
  rw [autocorrScaled_zero, hoff] at hsplit
  rw [hsplit] at hmom
  apply mul_left_cancel₀ (ne_of_gt hq)
  rw [← hmom]; ring

/-- **The canonical target of input (B): one finite-field point count.**  For the
Kasami exponent `d k` (`n` odd, `gcd(k,n)=1`), the number of ordered `4`-tuples of
field elements whose Kasami derivatives at `a = 1` sum to zero is `q³ + 2q²`:
`#{ x : Fin 4 → F | ∑ᵢ ((xᵢ+1)^{d k} + xᵢ^{d k}) = 0 } = q³ + 2q²`.

This is the genuine, irreducible almost-bent content (Chabaud–Vaudenay; Carlet Ch. 6):
every equivalent restatement of input (B) (the Wiener–Khinchin fourth-moment identity,
the punctured autocorrelation fourth moment `∑_{s≠0} R(s)⁴ = 2q³`, the derivative
additive-energy value `16·E = q³+2q²`, the second-derivative quadruple count) is now
derived *from* this single point count, for all `a ≠ 0`, by sorry-free wiring below.

It is stated at `a = 1` only, since `preCount4_pow_indep` reduces every `a ≠ 0` to
this case.  It is carried as the sole `sorry` of the module.

**WARNING — this statement is FALSE, and the `sorry` therefore cannot be filled.**
The additive energy of the *derivative image* is not an almost-bent invariant:
AB fixes only the Walsh spectrum `W(a,b)² ∈ {0, 2q}`, which does not force the
derivative-autocorrelation fourth moment to `2q³`.  Concretely,
`preCount 4 (·^{d k}) 1 (fun _ => 1) = q³ + 2q²` holds only for `n = 5, 7`, and
FAILS for every `n ≥ 9` (verified at `n = 9, 11, 13`, all genuinely AB) and for
the small degenerate case `n = 3`.  A fully machine-checked refutation over
`GF(8)` (`n = 3`, `k = 2`, where the true value is `1024 ≠ 640 = q³ + 2q²`) is
`Kasami.PreCount4Disproof.kasami_a1_preCount4_false` in
`RequestProject/Foundations/KasamiA1PreCount4Disproof.lean`.  Consequently the
Wiener–Khinchin bridge `hWK` cannot be discharged (not even from
`Kasami.Headlines.kasami_is_ab`), and the downstream results built on this leaf
(`kasami_preCount4`, `kasami_offDiag_fourthMoment_reduced`, …) inherit a false
hypothesis and are likewise not unconditionally establishable. -/
theorem kasami_a1_preCount4 {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) :
    (MTuple.preCount 4 (fun x : F => x ^ d k) 1 (fun _ => 1) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 := by
  sorry

/-- **General-`a` derivative point count (real proof).**  From the canonical `a = 1`
count and `preCount4_pow_indep`. -/
theorem kasami_preCount4 {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (MTuple.preCount 4 (fun x : F => x ^ d k) a (fun _ => 1) : ℤ)
      = (Fintype.card F : ℤ) ^ 3 + 2 * (Fintype.card F : ℤ) ^ 2 :=
  (preCount4_pow_indep (d k) a ha).trans
    (kasami_a1_preCount4 hcard hk hkn hcop hnodd hn)

/-- **The punctured autocorrelation fourth moment `∑_{s≠0} R_a(s)⁴ = 2q³` (real
proof).**  From the general-`a` point count `kasami_preCount4` via Fourier inversion
`∑_s R_a(s)⁴ = q·preCount₄(a)` and `R_a(0) = q`. -/
theorem kasami_offDiag_fourthMoment_reduced {n k : ℕ}
    (hcard : Fintype.card F = 2 ^ n) (hk : 1 ≤ k) (hkn : k < n)
    (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 1 ≤ n) (a : F) (ha : a ≠ 0) :
    (∑ s ∈ univ.erase (0 : F), (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
      = 2 * (Fintype.card F : ℤ) ^ 3 := by
  have hpc := kasami_preCount4 hcard hk hkn hcop hnodd hn a ha
  have hmom := crossCorr_power_moment 4 (fun x : F => x ^ d k) a
  rw [hpc] at hmom
  have hsplit :
      (∑ s : F, (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4)
        = (autocorrScaled (fun x : F => x ^ d k) 0 a) ^ 4
          + ∑ s ∈ univ.erase (0 : F), (autocorrScaled (fun x : F => x ^ d k) s a) ^ 4 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : F))]; ring
  rw [autocorrScaled_zero] at hsplit
  rw [hsplit] at hmom
  nlinarith [hmom]

end Vanish.Foundations

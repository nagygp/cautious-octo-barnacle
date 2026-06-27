import ConjecturesMTupleTripleCount.MTuple.Disproof
import ConjecturesMTupleTripleCount.Foundations.KasamiSpectrum

/-!
# Foundations, Layer 6 — evaluating the nonzero-frequency spectral sum

This module realizes **Layer 6** of the "Kasami is Vanish" roadmap
(`Docs/VanishFutureDirections.md`): given the spectral structure of an APN/AB
derivative (Layer 5), it **evaluates the nonzero-frequency spectral sum**
`∑_{t≠0} ∏_i R(t·cᵢ)` (with `R(s) = ∑_x χ(s·Δf_a x)` the scaled autocorrelation),
and uses that evaluation to **characterize exactly the coefficient tuples `c`**
for which it vanishes — the *admissible* tuples that feed
`MTuple.imgCount_of_vanish` / `MTuple.triple_count_of_vanish`.

## The evaluation

The Fourier-inversion identity `MTuple.card_mul_preCount`
(`q·preCount = ∑_t ∏_i R(t·cᵢ)`) together with the `t = 0` split
`MTuple.acSum_split` gives, unconditionally,

  `∑_{t≠0} ∏_i R(t·cᵢ) = q·preCount − qᵐ`   (`spectralSum_eq_preCount`).

So the nonzero-frequency spectral sum is, up to the affine normalization
`q·(·) − qᵐ`, the preimage m-tuple count.  For an APN derivative the preimage
count is `2ᵐ` times the **image** count (`MTuple.preCount_eq`, the two-to-one
fiber structure — the combinatorial shadow of the AB three-valued spectrum of
Layer 5, via Nyberg's APN ⟺ AB), so the spectral sum is a weighted count over
the derivative image.

## The admissibility characterization

Vanishing of the spectral sum is therefore equivalent to the image count
hitting its balanced value:

* `vanish_iff_preCount` — `Vanish ↔ preCount = q^{m-1}`;
* `vanish_iff_imgCount_pow` — `Vanish ↔ 2ᵐ·imgCount = q^{m-1}` (APN);
* `admissibleTriple_iff_vanish` — for `m = 3`, `Vanish ↔ imgCount = 2^{2n-3}`.

`AdmissibleTriple` packages the right-hand count condition; it is the explicit
form of the roadmap's admissible class, and `card_linear_tuple_of_vanish`
(Layer 1) / `MTuple.imgCount_of_vanish` already turn an admissible `c` into the
exact count.

## The order-3 obstruction

Some admissibility hypothesis on `c` is unavoidable: the equal-coefficient cube
map (`= ` the Kasami map at `k = 1`, since `d 1 = 3`) is **not** admissible for
`n` odd — its triple count is `0`, an instance of the `3 ∤ 2ⁿ−1` phenomenon
isolated in `MTuple/Disproof.lean`.  This is re-exposed here as
`cube_equal_not_admissible` / `cube_equal_not_vanish` and, for the Kasami map,
`kasami_one_equal_not_vanish`.

## Sources

Chabaud–Vaudenay §3 (the higher-moment / m-tuple count engine);
MacWilliams–Sloane (Pless power moments); Kasami (1971); Dobbertin (1999);
Canteaut–Charpin–Dobbertin (SIAM 2000).

## Design notes

Following *The Art of Clean Code* (Mayer, 2022): the genuine mathematics
(Fourier inversion, two-to-one structure, the order-3 obstruction) already lives
in `MTuple/Count.lean` and `MTuple/Disproof.lean`; this layer only *assembles* it
into the single evaluation lemma and the admissibility iff (DRY), each with a
single responsibility and an intention-revealing name.
-/

set_option maxHeartbeats 1600000

namespace Vanish.Foundations

open Finset BigOperators WalshAB MTuple CollisionAnalysis

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-! ## The evaluation of the nonzero-frequency spectral sum -/

/-
**Evaluation of the nonzero-frequency spectral sum** (unconditional).  The
sum over `t ≠ 0` of `∏_i R(t·cᵢ)` equals `q·preCount − qᵐ`.  Immediate from the
Fourier-inversion identity `MTuple.card_mul_preCount` and the `t = 0` split
`MTuple.acSum_split`.
-/
theorem spectralSum_eq_preCount (m : ℕ) (f : F → F) (a : F) (c : Fin m → F) :
    (∑ t ∈ univ.erase (0 : F), ∏ i : Fin m, autocorrScaled f (t * c i) a)
      = (Fintype.card F : ℤ) * (preCount m f a c : ℤ) - (Fintype.card F : ℤ) ^ m := by
  rw [ MTuple.card_mul_preCount m f a c, MTuple.acSum_split m f a c ] ; ring

/-! ## The vanishing ↔ count characterizations -/

/-
**Vanishing ↔ preimage count.**  `Vanish ↔ preCount = q^{m-1}`.  The forward
direction is `MTuple.preCount_of_vanish`; the converse follows from the
evaluation `spectralSum_eq_preCount`, since `q·q^{m-1} = qᵐ` for `m ≥ 1`.
-/
theorem vanish_iff_preCount (n m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (a : F) (c : Fin m → F) :
    Vanish m f a c ↔ preCount m f a c = 2 ^ ((m - 1) * n) := by
  constructor;
  · exact fun hv => preCount_of_vanish n m hm hcard f a c hv;
  · intro h;
    convert spectralSum_eq_preCount m f a c using 1;
    simp +decide [ Vanish, hcard, h ];
    rw [ ← pow_add, ← pow_mul ];
    grind

/-
**Vanishing ↔ image count** (APN form, subtraction-free).  For an APN
derivative, `Vanish ↔ 2ᵐ·imgCount = q^{m-1}`.  Combines `vanish_iff_preCount`
with the two-to-one structure `MTuple.preCount_eq`.
-/
theorem vanish_iff_imgCount_pow (n m : ℕ) (hm : 1 ≤ m)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (c : Fin m → F) :
    Vanish m f a c ↔ 2 ^ m * imgCount m f a c = 2 ^ ((m - 1) * n) := by
  rw [ Vanish.Foundations.vanish_iff_preCount n m hm hcard f a c, MTuple.preCount_eq m f hf a ha c ]

/-! ## Admissible coefficient triples -/

/-- The **admissible** coefficient triples for the derivative of `f` in direction
`a`: those whose balanced image-triple count equals `2^{2n-3}`.  By
`admissibleTriple_iff_vanish` this is exactly the class on which the
nonzero-frequency spectral sum vanishes (`MTuple.Vanish 3`), hence exactly the
class for which `MTuple.triple_count_of_vanish` applies. -/
def AdmissibleTriple (n : ℕ) (f : F → F) (a : F) (c : Fin 3 → F) : Prop :=
  imgCount 3 f a c = 2 ^ (2 * n - 3)

/-
**The admissibility characterization.**  For an APN derivative on `GF(2ⁿ)`
with `n ≥ 2`, a coefficient triple is admissible iff the nonzero-frequency
spectral sum vanishes.
-/
theorem admissibleTriple_iff_vanish (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0)
    (c : Fin 3 → F) :
    AdmissibleTriple n f a c ↔ Vanish 3 f a c := by
  rw [ Vanish.Foundations.vanish_iff_imgCount_pow ];
  any_goals assumption;
  · constructor <;> intro h <;> rw [ AdmissibleTriple ] at *;
    · rw [ h, ← pow_add, show 3 + ( 2 * n - 3 ) = 2 * n by omega ];
    · exact mul_left_cancel₀ ( pow_ne_zero 3 two_ne_zero ) ( by rw [ ← pow_add, Nat.add_sub_of_le ( by linarith ) ] ; exact h );
  · decide +revert

/-! ## The order-3 obstruction: equal coefficients are not admissible -/

/-
**Equal coefficients are not admissible for the cube map** (`n` odd).  Its
triple count is `0 ≠ 2^{2n-3}`, the `3 ∤ 2ⁿ−1` obstruction.
-/
theorem cube_equal_not_admissible (n : ℕ) (hodd : Odd n)
    (hcard : Fintype.card F = 2 ^ n) (a : F) (ha : a ≠ 0) (c0 : F) (hc0 : c0 ≠ 0) :
    ¬ AdmissibleTriple n (· ^ 3) a (fun _ => c0) := by
  convert MTuple.disproof_triple_cube n hodd hcard a ha c0 hc0 using 1;
  constructor <;> intro h <;> contrapose! h;
  · exact False.elim ( h ( MTuple.disproof_triple_cube n hodd hcard a ha c0 hc0 ) );
  · exact h.symm ▸ by positivity;

/-
**The spectral sum does not vanish for the equal-coefficient cube map**
(`n` odd, `n ≥ 2`, hence `n ≥ 3`).  Consequently an *unconditional* "Kasami is
Vanish" is false; some admissibility hypothesis on `c` is required.
-/
theorem cube_equal_not_vanish (n : ℕ) (hodd : Odd n) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (a : F) (ha : a ≠ 0) (c0 : F) (hc0 : c0 ≠ 0) :
    ¬ Vanish 3 (· ^ 3) a (fun _ => c0) := by
  intro hv;
  convert cube_equal_not_admissible n hodd hcard a ha c0 hc0 _;
  exact ( admissibleTriple_iff_vanish n hn hcard ( fun x => x ^ 3 ) MTuple.cube_isAPN a ha ( fun _ => c0 ) ).mpr hv

/-! ## Kasami specialization -/

variable {n k : ℕ}

/-- **Kasami admissibility characterization.**  For the Kasami map `x ↦ x^{d k}`
on `GF(2ⁿ)` (`1 ≤ k < n`, `gcd(k,n)=1`, `n` odd, `n ≥ 2`), a coefficient triple
is admissible iff the nonzero-frequency spectral sum vanishes. -/
theorem kasami_admissibleTriple_iff_vanish (hcard : Fintype.card F = 2 ^ n)
    (hk : 1 ≤ k) (hkn : k < n) (hcop : Nat.Coprime k n) (hnodd : Odd n) (hn : 2 ≤ n)
    (a : F) (ha : a ≠ 0) (c : Fin 3 → F) :
    AdmissibleTriple n (fun x : F => x ^ d k) a c
      ↔ Vanish 3 (fun x : F => x ^ d k) a c :=
  admissibleTriple_iff_vanish n hn hcard _
    (KasamiAB.kasami_is_apn_pred hcard k hk hkn hcop hnodd (by omega)) a ha c

/-
**The order-3 obstruction for Kasami at `k = 1`.**  Since `d 1 = 3`, the
Kasami map at `k = 1` is the cube map, whose equal-coefficient triple count is
`0`; hence the spectral sum does not vanish for `n` odd with `n ≥ 2`.
-/
theorem kasami_one_equal_not_vanish (hnodd : Odd n) (hn : 2 ≤ n)
    (hcard : Fintype.card F = 2 ^ n) (a : F) (ha : a ≠ 0) (c0 : F) (hc0 : c0 ≠ 0) :
    ¬ Vanish 3 (fun x : F => x ^ d 1) a (fun _ => c0) := by
  convert cube_equal_not_vanish n hnodd hn hcard a ha c0 hc0 using 1

end Vanish.Foundations
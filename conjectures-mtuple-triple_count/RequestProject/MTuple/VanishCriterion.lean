import RequestProject.MTuple.Count

/-!
# A true, computable admissibility criterion for the m-tuple count

This module supplies the **green core** that completes the m-tuple count proof
path *without* assuming any of the (false) literature-style spectral inputs that
the earlier development leaned on.

## Background: why the old bridge is dead

The earlier `k = 2` Kasami count reduced the image m-tuple count to a
"Wiener–Khinchin bridge" `hWK`, equivalently the value

  `∑_{s ≠ 0} R_a(s)⁴ = 2·q³`   (the *derivative-autocorrelation* fourth moment),

which was hoped to follow from the Kasami map being almost bent (AB).  **It does
not.**  AB pins only the *Walsh* spectrum `W(a,b) ∈ {0, ±2^{(n+1)/2}}`; it does
*not* force the *derivative autocorrelation* `R_a(s) = ∑_x χ(s·Δf_a x)` to be
three-valued.  Direct computation over `GF(2⁹)` shows that the Kasami map
`x ↦ x¹³` is genuinely AB there (its Walsh spectrum is `{0, ±32}`), yet its
derivative autocorrelation additionally takes the value `2·32 = 64`, so

  `∑_{s ≠ 0} R_1(s)⁴ ≠ 2·q³`   (it is `394264576`, not `268435456`).

Hence the `2q³` bridge — and the three-valued/`sign`-correlation characterization
of the admissible coefficient tuples that rests on it — is *false* for the very
functions the development is about (all genuine AB Kasami maps with `n ≥ 9`).  It
is not a vacuous hypothesis one may simply discharge; it is a wrong statement.

## The correct, computable criterion (this file)

Rather than route through the derivative autocorrelation's value set, we go
straight back to the two unconditional green facts already in
`RequestProject.MTuple.Count`:

* `card_mul_preCount` : `q · preCount = ∑_t ∏_i R(t·c_i)` (Fourier inversion);
* `acSum_split`       : `∑_t ∏_i R(t·c_i) = qᵐ + ∑_{t≠0} ∏_i R(t·c_i)`;
* `preCount_eq`       : for an APN `f`, `preCount = 2ᵐ · imgCount`.

Combining the first two, the genuine spectral condition
`Vanish` (`∑_{t≠0} ∏_i R(t·c_i) = 0`) is **exactly equivalent** to the
preimage count hitting its generic value:

  `Vanish m f a c  ⟺  preCount m f a c = q^{m-1}`   (`vanish_iff_preCount`).

The right-hand side is a *purely combinatorial*, `χ`-free, and **decidable**
count — no trace, no character, no fourth-moment input.  Feeding it through the
already-green `preCount_eq` gives the master equivalence

  `imgCount = 2^{(m-1)n − m}  ⟺  preCount = 2^{(m-1)n}  ⟺  Vanish`
  (`imgCount_eq_iff_preCount`, `imgCount_generic_iff`)

for any APN `f`.  This is the honest, bottom-up completion of the count: the
image m-tuple count attains its generic value **iff** the (computable) preimage
count does, and one checks that directly for any concrete instance, with **no**
literature hypothesis and **no** `sorry`.

An unconditional end-to-end instance (over `GF(8)`, no hypotheses at all) is
given in `RequestProject/MTuple/VanishInstance.lean`.
-/

set_option maxHeartbeats 1600000

namespace MTuple

open Finset Fintype BigOperators WalshAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **`Vanish` ⟺ the preimage count is generic.**  The genuine spectral condition
`Vanish` (the nonzero-frequency spectral sum vanishes) holds **iff** the preimage
m-tuple count equals its generic value `q^{m-1} = 2^{(m-1)n}`.  This is a purely
Fourier-inversion consequence of `card_mul_preCount` and `acSum_split`; it needs
no divisibility, no fourth moment, and no APN hypothesis. -/
theorem vanish_iff_preCount (n m : ℕ) (hm : 1 ≤ m) (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (a : F) (c : Fin m → F) :
    Vanish m f a c ↔ preCount m f a c = 2 ^ ((m - 1) * n) := by
  have hkey : (Fintype.card F : ℤ) * (preCount m f a c : ℤ)
      = (Fintype.card F : ℤ) ^ m
        + ∑ t ∈ univ.erase (0 : F), ∏ i : Fin m, autocorrScaled f (t * c i) a := by
    rw [card_mul_preCount, acSum_split]
  constructor
  · intro hv
    exact preCount_of_vanish n m hm hcard f a c hv
  · intro hp
    unfold Vanish
    have h2 : (Fintype.card F : ℤ) * ((2 ^ ((m - 1) * n) : ℕ) : ℤ)
        = (Fintype.card F : ℤ) ^ m
          + ∑ t ∈ univ.erase (0 : F), ∏ i : Fin m, autocorrScaled f (t * c i) a := by
      rw [← hp]; exact hkey
    have hmm : ((2 : ℤ) ^ n) ^ m = (2 : ℤ) ^ n * (2 ^ ((m - 1) * n)) := by
      rw [← pow_add, ← pow_mul]
      congr 1
      cases m with
      | zero => omega
      | succ k => simp only [Nat.succ_sub_one]; ring
    rw [hcard] at h2
    push_cast at h2
    rw [hmm] at h2
    linarith

/-- **The image count is generic ⟺ the preimage count is generic** (for APN `f`).
Since `preCount = 2ᵐ · imgCount` for an APN derivative (`preCount_eq`), the image
m-tuple count attains its generic value `2^{(m-1)n − m}` **iff** the preimage
count attains `2^{(m-1)n}`.  Purely combinatorial, `χ`-free, and decidable. -/
theorem imgCount_eq_iff_preCount (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) (c : Fin m → F) :
    imgCount m f a c = 2 ^ ((m - 1) * n - m)
      ↔ preCount m f a c = 2 ^ ((m - 1) * n) := by
  have hle : m ≤ (m - 1) * n := by
    calc m ≤ (m - 1) * 2 := by omega
      _ ≤ (m - 1) * n := Nat.mul_le_mul (le_refl (m - 1)) hn
  have hpow : (2 : ℕ) ^ ((m - 1) * n) = 2 ^ m * 2 ^ ((m - 1) * n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [preCount_eq m f hf a ha c]
  constructor
  · intro h
    rw [h, hpow]
  · intro h
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h

/-- **Master equivalence.**  For an APN `f`, the image m-tuple count attaining its
generic value is equivalent to the preimage count being generic *and* to the
genuine spectral condition `Vanish`:

  `imgCount = 2^{(m-1)n − m}  ⟺  preCount = 2^{(m-1)n}  ⟺  Vanish`.

The middle term is the true, computable admissibility criterion — the honest
replacement for the false three-valued/`2q³` bridge. -/
theorem imgCount_generic_iff (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hcard : Fintype.card F = 2 ^ n)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) (c : Fin m → F) :
    (imgCount m f a c = 2 ^ ((m - 1) * n - m)
      ↔ preCount m f a c = 2 ^ ((m - 1) * n))
    ∧ (preCount m f a c = 2 ^ ((m - 1) * n) ↔ Vanish m f a c) := by
  refine ⟨imgCount_eq_iff_preCount n m hn hm f hf a ha c, ?_⟩
  exact (vanish_iff_preCount n m (by omega) hcard f a c).symm

/-- **The count from the computable criterion** (no literature hypothesis).  For
an APN `f`, if the preimage m-tuple count is generic (`= 2^{(m-1)n}`, a decidable
condition), then the image m-tuple count is `2^{(m-1)n − m}`.  This is the
`χ`-free, `Vanish`-free entry point used to close concrete instances end-to-end. -/
theorem imgCount_of_preCount (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (f : F → F) (hf : IsAPN f) (a : F) (ha : a ≠ 0) (c : Fin m → F)
    (hp : preCount m f a c = 2 ^ ((m - 1) * n)) :
    imgCount m f a c = 2 ^ ((m - 1) * n - m) :=
  (imgCount_eq_iff_preCount n m hn hm f hf a ha c).mpr hp

end MTuple

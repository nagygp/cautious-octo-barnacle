import RequestProject.CodingTheory.SpherePacking

/-!
# Perfect codes and the binary repetition code

This module continues the sphere-packing development of
`RequestProject/CodingTheory/SpherePacking.lean`, transcribed from

* F. J. MacWilliams and N. J. A. Sloane,
  *The Theory of Error-Correcting Codes*, North-Holland, Amsterdam, 1977
  (Ch. 1, §7: perfect codes).

A code is **perfect** when the Hamming balls of radius `t = ⌊(d-1)/2⌋` about its
codewords *tile* the whole space, i.e. it meets the sphere-packing bound
`sphere_packing_bound_volume` with **equality**:
`|C| · V_q(n, t) = q^n`.

As a first worked example we prove that the **binary repetition code** — the
one-dimensional code spanned by the all-ones word over `F₂` — is perfect whenever
its length `n` is odd.  (The remaining classical perfect codes are the Hamming
and Golay codes.)

## Main definitions

* `IsPerfect C` — `C` meets the sphere-packing bound with equality.
* `repCode ι F` — the repetition code `span F {(1,…,1)}`.

## Main results

* `minDist_repCode_zmod2` — the binary repetition code has minimum distance `n`.
* `card_repCode_zmod2` — it has exactly `2` codewords.
* `repCode_isPerfect` — **the binary repetition code of odd length is perfect**,
  proved directly from the sphere-packing volume `V_2(n, (n-1)/2) = 2^{n-1}`.
-/

namespace CodingTheory

open scoped Classical
open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F] [Fintype F]

/-- A code is **perfect** when it meets the sphere-packing (Hamming) bound with
equality: the balls of radius `t = ⌊(d-1)/2⌋` about the codewords tile `Fⁿ`,
`|C| · V_q(n, t) = q^n`. -/
def IsPerfect (C : Submodule F (ι → F)) : Prop :=
  Fintype.card C
      * hammingBallVolume (Fintype.card ι) (Fintype.card F) ((minDist C - 1) / 2)
    = Fintype.card F ^ Fintype.card ι

/-- The **repetition code**: the one-dimensional code spanned by the all-ones
word `(1, …, 1)`. -/
def repCode (ι F : Type*) [Fintype ι] [Field F] : Submodule F (ι → F) :=
  Submodule.span F {fun _ : ι => (1 : F)}

/-
Membership in the repetition code: the codewords are exactly the constant
words `a • (1,…,1)`.
-/
theorem mem_repCode_iff {c : ι → F} :
    c ∈ repCode ι F ↔ ∃ a : F, c = fun _ => a := by
  simp +decide [ repCode, Submodule.mem_span_singleton ];
  simp +decide [ funext_iff, eq_comm ]

/-
The all-ones word has full Hamming weight `n`.
-/
theorem hammingNorm_ones :
    hammingNorm (fun _ : ι => (1 : F)) = Fintype.card ι := by
  unfold hammingNorm; aesop;

/-
Over `F₂`, the repetition code is `{0, (1,…,1)}`, so its minimum distance is
the length `n`.
-/
theorem minDist_repCode_zmod2 [Nonempty ι] :
    minDist (repCode ι (ZMod 2)) = Fintype.card ι := by
  refine' minDist_eq_minWeight ( repCode ι ( ZMod 2 ) ) ▸ le_antisymm _ _;
  · refine' Nat.sInf_le _;
    refine' ⟨ fun _ => 1, _, _, _ ⟩ <;> norm_num [ hammingNorm_ones ];
    · exact Submodule.subset_span ( Set.mem_singleton _ );
    · exact fun h => by simpa using congr_fun h ( Classical.arbitrary ι ) ;
  · refine' le_csInf _ _;
    · refine' ⟨ _, ⟨ fun _ => 1, _, _, rfl ⟩ ⟩;
      · exact Submodule.subset_span ( Set.mem_singleton _ );
      · exact fun h => by simpa using congr_fun h ( Classical.arbitrary ι ) ;
    · rintro _ ⟨ c, hc, hc', rfl ⟩;
      obtain ⟨ a, rfl ⟩ := mem_repCode_iff.mp hc;
      fin_cases a <;> simp_all +decide [ funext_iff ];
      convert hammingNorm_ones.ge;
      infer_instance

/-
Over `F₂` the repetition code has exactly two codewords.
-/
theorem card_repCode_zmod2 [Nonempty ι] :
    Fintype.card (repCode ι (ZMod 2)) = 2 := by
  convert Fintype.card_eq.mpr ?_;
  convert rfl;
  convert ZMod.card 2;
  refine' ⟨ _ ⟩;
  refine' Equiv.ofBijective ( fun x => x.val ( Classical.arbitrary ι ) ) ⟨ fun a b h => _, fun a => _ ⟩;
  · rcases a with ⟨ a, ha ⟩ ; rcases b with ⟨ b, hb ⟩ ; simp_all +decide [ funext_iff ];
    rw [ mem_repCode_iff ] at ha hb ; aesop;
  · exact ⟨ ⟨ fun _ => a, by rw [ mem_repCode_iff ] ; exact ⟨ a, rfl ⟩ ⟩, rfl ⟩

/-
**The binary repetition code of odd length is perfect.**  With `q = 2`,
`|C| = 2`, `t = (n-1)/2`, the ball volume is
`V_2(n, (n-1)/2) = Σ_{i≤(n-1)/2} C(n,i) = 2^{n-1}`, so
`|C| · V_2(n, t) = 2 · 2^{n-1} = 2^n = q^n`.
-/
theorem repCode_isPerfect (hodd : Odd (Fintype.card ι)) :
    IsPerfect (repCode ι (ZMod 2)) := by
  obtain ⟨ m, hm ⟩ := hodd;
  rcases isEmpty_or_nonempty ι with h | h <;> simp_all +decide [ IsPerfect ];
  rw [ minDist_repCode_zmod2, hm ] ; simp +decide [ pow_succ', hammingBallVolume ] ; ring;
  rw [ card_repCode_zmod2 ] ; ring;
  convert congr_arg ( · * 2 ) ( Nat.sum_range_choose_halfway m ) using 1 ; ring;
  norm_num [ pow_mul' ]

end CodingTheory
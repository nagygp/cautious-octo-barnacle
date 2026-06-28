import Mathlib

/-!
# Wide-trail infrastructure: Hamming weight, branch number, MDS, active S-boxes

A credible audit of a whole permutation (not just one S-box) lives at the level of
the *wide-trail strategy*: the diffusion layer `L` is chosen so that any
differential/linear trail activates many S-boxes.  The governing quantity is the
**branch number**

  `branchNumber L = min_{x ≠ 0} ( wt x + wt (L x) )`,

where `wt` is the Hamming weight (number of nonzero coordinates).  A linear layer
is **MDS** (maximum distance separable) when its branch number attains the maximal
value `n + 1`, and then every two-round trail activates at least `n + 1` S-boxes.

## Main results

* `branchNumber_le_succ` — the Singleton-type upper bound `branchNumber L ≤ n+1`.
* `branchNumber_le_active` — for every nonzero `x`, `branchNumber L ≤ wt x + wt (L x)`
  (the number of active S-boxes over two rounds is at least the branch number).
* `IsMDS.two_round_active` — for an MDS layer, every nonzero trail activates at
  least `n + 1` S-boxes.
* `branchNumber_id` — the identity layer has branch number `2`, hence is *not* MDS
  for `n ≥ 2`: the framework distinguishes genuine diffusion from none.
-/

open Finset

open scoped Classical

namespace PrimeFieldAudit

variable {F : Type*} [Field F] {n : ℕ}

/-- Hamming weight: the number of nonzero coordinates of a vector. -/
noncomputable def wt (x : Fin n → F) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- The Hamming weight never exceeds the number of coordinates. -/
lemma wt_le (x : Fin n → F) : wt x ≤ n := by
  unfold wt
  calc (Finset.univ.filter (fun i => x i ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-
A vector of positive weight is nonzero, and conversely.
-/
lemma wt_pos_iff (x : Fin n → F) : 0 < wt x ↔ x ≠ 0 := by
  -- We start by unfolding the definition of `wt`. The goal becomes 0 < (univ.filter (fun i => x i ≠ 0)).card ↔ x ≠ 0.
  unfold wt
  simp [Finset.card_pos, Finset.filter_nonempty_iff];
  simp +decide [ funext_iff ]

/-- The branch number of a (diffusion) map `L`: the least total weight
`wt x + wt (L x)` over all nonzero inputs `x`. -/
noncomputable def branchNumber (L : (Fin n → F) → (Fin n → F)) : ℕ :=
  sInf {k | ∃ x : Fin n → F, x ≠ 0 ∧ wt x + wt (L x) = k}

/-- **Wide-trail lower bound.** For every nonzero input, the number of active
S-boxes over two rounds `wt x + wt (L x)` is at least the branch number. -/
theorem branchNumber_le_active (L : (Fin n → F) → (Fin n → F))
    (x : Fin n → F) (hx : x ≠ 0) :
    branchNumber L ≤ wt x + wt (L x) := by
  apply Nat.sInf_le
  exact ⟨x, hx, rfl⟩

/-
**Singleton-type bound.** For `n ≥ 1`, the branch number is at most `n + 1`.
-/
theorem branchNumber_le_succ (L : (Fin n → F) → (Fin n → F)) (hn : 1 ≤ n) :
    branchNumber L ≤ n + 1 := by
  -- Choose any index `i0` such that `1 ≤ i0 ≤ n`.
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin n, True := by
    exact ⟨ ⟨ 0, hn ⟩, trivial ⟩
  generalize_proofs at *; (
  refine' le_trans ( Nat.sInf_le _ ) _;
  exact 1 + wt ( L ( Pi.single i0 1 ) );
  · refine' ⟨ Pi.single i0 1, _, _ ⟩ <;> simp +decide;
    exact Finset.card_eq_one.mpr ⟨ i0, by ext i; by_cases hi : i = i0 <;> aesop ⟩;
  · linarith [ wt_le ( L ( Pi.single i0 1 ) ) ])

/-- A diffusion layer is **MDS** when its branch number is maximal (`n + 1`). -/
def IsMDS (L : (Fin n → F) → (Fin n → F)) : Prop :=
  branchNumber L = n + 1

/-- **MDS two-round activity.** Through an MDS diffusion layer, every nonzero trail
activates at least `n + 1` S-boxes. -/
theorem IsMDS.two_round_active {L : (Fin n → F) → (Fin n → F)} (hL : IsMDS L)
    (x : Fin n → F) (hx : x ≠ 0) :
    n + 1 ≤ wt x + wt (L x) := by
  rw [← hL]
  exact branchNumber_le_active L x hx

/-
The identity diffusion layer has branch number `2` (each nonzero `x`
contributes `2·wt x ≥ 2`, attained at weight-one vectors).  Hence for `n ≥ 2` the
identity is *not* MDS: the framework detects the absence of diffusion.
-/
theorem branchNumber_id (hn : 1 ≤ n) :
    branchNumber (id : (Fin n → F) → (Fin n → F)) = 2 := by
  refine' le_antisymm _ _;
  · obtain ⟨i0, hi0⟩ : ∃ i0 : Fin n, True := by
      exact ⟨ ⟨ 0, hn ⟩, trivial ⟩;
    refine' Nat.sInf_le ⟨ fun i => if i = i0 then 1 else 0, _, _ ⟩ <;> simp +decide [ wt ];
    · exact fun h => by simpa using congr_fun h i0;
    · simp +decide [ Finset.filter_eq' ];
  · refine' le_csInf _ _;
    · exact ⟨ _, ⟨ fun _ => 1, fun h => by simpa using congr_fun h ⟨ 0, hn ⟩, rfl ⟩ ⟩;
    · simp +zetaDelta at *;
      exact fun x hx => by linarith [ show 1 ≤ wt x from Nat.pos_of_ne_zero fun h => hx <| by ext i; simp_all +decide [ wt ] ] ;

end PrimeFieldAudit
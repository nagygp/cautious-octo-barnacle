/-
# Almost Perfect Nonlinear (APN) and Almost Bent (AB) Function Theory
-/
import Mathlib
import RequestProject.TraceChar
import RequestProject.WalshHadamard
import RequestProject.SpectralIdentity

open Finset BigOperators
noncomputable section
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
attribute [local instance] ZMod.algebra

def kasamiExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

lemma kasamiExponent_one : kasamiExponent 1 = 3 := by norm_num [kasamiExponent]

def derivative (G : F → F) (a x : F) : F := G (x + a) + G x

def isAPN (G : F → F) : Prop :=
  ∀ (a : F), a ≠ 0 → ∀ (b : F),
    (Finset.univ.filter (fun x => derivative F G a x = b)).card ≤ 2

def nonzeroElems : Finset F := Finset.univ.filter (fun (b : F) => b ≠ 0)

def AlmostBentVanishing (S : Finset F) : Prop :=
  ∀ (c : F), c ≠ 0 → c ≠ 1 →
    (nonzeroElems F).sum (fun b =>
      walshCoeff F (indicator F S) b *
      walshCoeff F (indicator F S) (b * c) *
      walshCoeff F (indicator F S) (b * (1 + c))) = 0

def kasamiDelta (e : ℕ) : Finset F :=
  Finset.univ.image (fun b : F => b ^ e + (b + 1) ^ e + 1)

theorem P3_from_AB (S : Finset F) (hAB : AlmostBentVanishing F S)
    (hc : ∀ c : F, c ≠ 0 → c ≠ 1 → True) :
    ∀ (c : F), c ≠ 0 → c ≠ 1 →
      (Fintype.card F : ℤ) * tripleCount F S c = (S.card : ℤ) ^ 3 := by
  intro c hc0 hc1
  have hABc := hAB c hc0 hc1
  unfold nonzeroElems at hABc
  -- We need: ∑_b Ŝ(b)·Ŝ(bc)·Ŝ(b(1+c)) = |S|³
  -- Split sum into b=0 and b≠0
  -- b=0 gives Ŝ(0)³ = |S|³
  -- b≠0 gives 0 by AB vanishing
  rw [← spectral_identity]
  convert congr_arg ( fun x : ℤ => x + ( walshCoeff F ( indicator F S ) 0 * walshCoeff F ( indicator F S ) ( 0 * c ) * walshCoeff F ( indicator F S ) ( 0 * ( 1 + c ) ) ) ) hABc using 1 <;> norm_num [ Finset.filter_ne' ] ; ring;
  rw [ walshCoeff_indicator_zero ]

end
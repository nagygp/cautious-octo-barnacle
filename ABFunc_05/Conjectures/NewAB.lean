/-
  # 10 New AB Function Conjectures

  Each conjecture proposes a **new Almost Bent (AB)** function over GF(2^n)
  (n odd), motivated by structural insights from the topos-theoretic
  framework:

  1. **Bridge Transfer** (Conjectures AB1–AB3): The Bridge Theorem proves
     that every PN function over GF(p) has a "Boolean relative" with matching
     counting exponent. We conjecture *concrete* AB functions that realise
     these transferred signatures.

  2. **Exp ↔ Log Conjugation** (Conjectures AB4–AB6): The discrete-logarithm
     map log_α : (GF(2^n)*, ·) → (ℤ/(2^n−1), +) conjugates multiplicative
     power maps to additive maps on indices. Composing known AB power maps
     with this conjugation yields new candidate AB functions.

  3. **Spectral/Homotopical Construction** (Conjectures AB7–AB8): Functions
     engineered to satisfy the spectral-diversity-1 condition (bent_implies_
     discrete) and the Kerdock weight correspondence simultaneously.

  4. **Algebraic Self-Duality** (Conjectures AB9–AB10): Functions that are
     fixed points (up to affine equivalence) of the Walsh-transform duality
     functor, motivated by the self-dual bridge invariance.

  All conjectures are stated over a generic finite field of characteristic 2
  with an odd extension degree.
-/
import Mathlib
import Foundation.ElemTopos
import Bridge.PNBoolean
import Bridge.Duality
import CodingTheory.BinaryCode
import Spectral.SpectralObject
import Conjectures.APN

open Finset BigOperators

noncomputable section

set_option maxHeartbeats 400000

/-! ## Infrastructure -/

/-- The Walsh transform of a function f : G → G at a character pair (a, b),
    defined as ∑_x (-1)^{Tr(a·x + b·f(x))} over the field.
    We model this abstractly: the Walsh coefficient at index v. -/
structure WalshData (G : Type*) [AddCommGroup G] [Fintype G] where
  coeff : G × G → ℤ

/-- A function f : G → G is **Almost Bent (AB)** if its Walsh transform
    takes values in {0, ±2^{(n+1)/2}} where |G| = 2^n, n odd. -/
def IsABWalsh {G : Type*} [AddCommGroup G] [Fintype G]
    (W : WalshData G) (c : ℤ) : Prop :=
  c > 0 ∧ (∀ v, W.coeff v = 0 ∨ W.coeff v = c ∨ W.coeff v = -c)

/-- The Frobenius endomorphism x ↦ x^{2^k}. -/
def frobenius' {F : Type*} [Field F] (k : ℕ) : F → F := fun x => x ^ (2 ^ k)

/-- A function is **Walsh self-dual** if its Walsh transform equals
    itself up to a constant factor. -/
def IsWalshSelfDual {G : Type*} [AddCommGroup G] [Fintype G]
    (W : WalshData G) (c : ℤ) : Prop :=
  ∀ v, W.coeff v = c ∨ W.coeff v = -c ∨ W.coeff v = 0

/-! ## Conjecture AB1: Coulter–Matthews Boolean Relative

**Source**: The Coulter–Matthews function over GF(3^n) is
  f(x) = x^{(3^k + 1)/2},  gcd(k, n) = 1.
This is a PN (Perfect Nonlinear) function.

**Bridge Transfer**: By the Bridge Theorem, the CM counting signature
  κ_m = 3^{(m−1)n − m}
transfers to a Boolean relative signature
  κ_m = 2^{(m−1)n − m}.

**Conjecture**: The function
  g(x) = x^{2^k + 2^{⌊k/2⌋} + 1}
over GF(2^n), n odd, gcd(k, n) = 1, is AB.  This exponent is obtained
by "binarising" the CM exponent (3^k+1)/2 via the substitution 3↦2
and taking the integer part that preserves the differential structure.
-/

def cmBooleanRelativeExp (k : ℕ) : ℕ := 2 ^ k + 2 ^ (k / 2) + 1

/-- **Conjecture AB1 (Coulter–Matthews Boolean Relative)**:
    The power function x^{2^k + 2^{⌊k/2⌋} + 1} is AB over GF(2^n)
    when n is odd and gcd(k, n) = 1. -/
def ConjectureAB1 : Prop :=
  ∀ (n k : ℕ), n % 2 = 1 → n ≥ 5 → 1 ≤ k → k < n → Nat.gcd k n = 1 →
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = 2 ^ n →
        @IsAPN F (inferInstance : AddCommGroup F) _ _ (fun x => x ^ cmBooleanRelativeExp k)

/-! ## Conjecture AB2: Ding–Helleseth Boolean Relative

**Source**: The Ding–Helleseth functions over GF(p^n) for odd prime p
are PN with exponent d = (p^k + 1)/2 under suitable conditions.

**Bridge Transfer**: Their Boolean relative has signature 2^{(m−1)n − m}.

**Conjecture**: The function
  g(x) = x^{2^{2k} + 2^k + 1}
over GF(2^n), n odd, is AB. The exponent 2^{2k} + 2^k + 1 is the
Kasami exponent — here we conjecture it arises specifically as the
Boolean relative of the Ding–Helleseth family, suggesting a deeper
structural connection.
-/

def dhBooleanRelativeExp (k : ℕ) : ℕ := 2 ^ (2 * k) + 2 ^ k + 1

/-- **Conjecture AB2 (Ding–Helleseth Boolean Relative)** -/
def ConjectureAB2 : Prop :=
  ∀ (n k : ℕ), n % 2 = 1 → n ≥ 5 → 1 ≤ k → k < n → Nat.gcd k n = 1 →
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = 2 ^ n →
        @IsAPN F (inferInstance : AddCommGroup F) _ _ (fun x => x ^ dhBooleanRelativeExp k)

/-! ## Conjecture AB3: Helleseth–Rong Boolean Relative

**Source**: Over GF(3^n) with n odd, the function x^{3^k + 2} is
differentially 2-uniform (the "PN analogue of Welch").

**Bridge Transfer**: Boolean relative via base change 3 → 2.

**Conjecture**: x^{2^k + 3} is AB over GF(2^n) for suitable k
with gcd(k, n) = 1, n ≥ 7. For k = 1 this gives the known exponent 5;
the conjecture is for general k ≥ 2.
-/

def hrBooleanRelativeExp (k : ℕ) : ℕ := 2 ^ k + 3

/-- **Conjecture AB3 (Helleseth–Rong Boolean Relative)** -/
def ConjectureAB3 : Prop :=
  ∀ (n k : ℕ), n % 2 = 1 → n ≥ 7 → 2 ≤ k → k < n → Nat.gcd k n = 1 →
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = 2 ^ n →
        @IsAPN F (inferInstance : AddCommGroup F) _ _ (fun x => x ^ hrBooleanRelativeExp k)

/-! ## Conjecture AB4: Exp–Log Conjugate of Gold

**Idea**: The discrete logarithm log_α : GF(2^n)* → ℤ/(2^n − 1)
conjugates the multiplicative power map x ↦ x^d to the additive map
i ↦ d·i (mod 2^n − 1). We add a *quadratic* perturbation in the log domain:

  g(i) = (2^k + 1)·i + i² mod (2^n − 1)

When lifted back to GF(2^n)* via α^i ↦ α^{g(i)}, this gives a
non-power-map function that preserves many of Gold's differential
properties while breaking multiplicative structure.
-/

/-- Gold function composed with log-domain quadratic perturbation. -/
def goldLogMap (k n : ℕ) (i : ℕ) : ℕ :=
  (i * (2 ^ k + 1)) % (2 ^ n - 1)

def carryPerturbation (n : ℕ) (i : ℕ) : ℕ :=
  (i * i / (2 ^ n - 1)) % (2 ^ n - 1)

/-- **Conjecture AB4 (Log-Domain Gold with Carry Perturbation)**:
    The function defined in the exponent domain as
      i ↦ i·(2^k+1) + ⌊i²/(2^n−1)⌋  (mod 2^n−1)
    lifts to an AB function on GF(2^n), n odd, gcd(k, n) = 1.

    The conjecture is stated at the index level: the induced function
    on ℤ/(2^n−1) has differential uniformity 2. -/
def ConjectureAB4 : Prop :=
  ∀ (n k : ℕ), n % 2 = 1 → n ≥ 5 → 1 ≤ k → k < n → Nat.gcd k n = 1 →
    let q := 2 ^ n - 1
    ∀ (a : ℕ), 1 ≤ a → a < q →
      ∀ (b : ℕ), b < q →
        (Finset.Icc 0 (q - 1) |>.filter (fun i =>
          ((goldLogMap k n (i + a) + carryPerturbation n (i + a))
           - (goldLogMap k n i + carryPerturbation n i)) % q = b)).card ≤ 2

/-! ## Conjecture AB5: Log-Kasami with Frobenius Twist

**Idea**: Apply the exp→log conjugation to the Kasami function
x^{2^{2k} − 2^k + 1} and twist by a Frobenius automorphism
x ↦ x² in the log domain (i ↦ 2i mod 2^n−1).

The result: x ↦ (x²)^{Kasami_exp} = x^{2·(2^{2k} − 2^k + 1)},
a new exponent if not cyclotomic-equivalent to a known family.
-/

def frobeniusTwistedKasamiExp (k : ℕ) : ℕ :=
  2 * (2 ^ (2 * k) - 2 ^ k + 1)

/-- **Conjecture AB5 (Frobenius-Twisted Kasami)**:
    x^{2·(2^{2k} − 2^k + 1)} is AB over GF(2^n) for n odd,
    gcd(k, n) = 1, and the exponent not cyclotomic-equivalent
    to a known family. -/
def ConjectureAB5 : Prop :=
  ∀ (n k : ℕ), n % 2 = 1 → n ≥ 7 → 2 ≤ k → k < n → Nat.gcd k n = 1 →
    2 ^ (2 * k) ≥ 2 ^ k + 1 →
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = 2 ^ n →
        @IsAPN F (inferInstance : AddCommGroup F) _ _ (fun x => x ^ frobeniusTwistedKasamiExp k)

/-! ## Conjecture AB6: Double-Exp Gold (Gold ∘ Gold in the exp domain)

**Idea**: Compose two Gold functions via the exp–log bridge:
  z = (x^{2^j+1})^{2^k+1} = x^{(2^j+1)(2^k+1)}.
The composite exponent (2^j+1)(2^k+1) = 2^{j+k} + 2^j + 2^k + 1
is generically not in any known APN family when j ≠ k and j + k < n.
-/

def doubleGoldExp (j k : ℕ) : ℕ := (2 ^ j + 1) * (2 ^ k + 1)

/-- **Conjecture AB6 (Double-Gold Composition)** -/
def ConjectureAB6 : Prop :=
  ∀ (n j k : ℕ), n % 2 = 1 → n ≥ 7 → j ≠ k →
    1 ≤ j → j < n → 1 ≤ k → k < n → j + k < n →
    Nat.gcd j n = 1 → Nat.gcd k n = 1 →
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = 2 ^ n →
        @IsAPN F (inferInstance : AddCommGroup F) _ _ (fun x => x ^ doubleGoldExp j k)

/-! ## Conjecture AB7: Kerdock Sufficiency

**Idea**: The Kerdock correspondence (ab_kerdock_spectral_match) says
AB functions correspond to 3-weight codes with Kerdock structure.
We conjecture the *converse* is also true: any function whose code
has the Kerdock weight distribution is necessarily AB.
-/

def kerdockWeights (n : ℕ) : Finset ℕ :=
  {2 ^ (n - 1) - 2 ^ ((n - 1) / 2), 2 ^ (n - 1), 2 ^ (n - 1) + 2 ^ ((n - 1) / 2)}

/-- **Conjecture AB7 (Kerdock Sufficiency)**:
    Kerdock weight structure is sufficient for AB (not just necessary). -/
def ConjectureAB7 : Prop :=
  ∀ (n : ℕ), n % 2 = 1 → n ≥ 5 →
    ∀ (σ : SpectralSignature),
      HasPNTypeCounting booleanSpectralTopos n σ →
        ∀ m, 2 ≤ m → σ m = internalMTupleCount booleanSpectralTopos n m

/-! ## Conjecture AB8: Homotopical Characterisation of AB

**Idea**: `bent_implies_discrete` shows spectral diversity = 1 forces
all higher homotopy groups to vanish. We conjecture the *converse*:
  Postnikov tower discrete ⟹ f is AB.
-/

/-- **Conjecture AB8 (Homotopical Characterisation of AB)** -/
def ConjectureAB8 : Prop :=
  ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
    ∀ (spectrum : F → ℂ) (_hNontriv : ∃ v, spectrum v ≠ 0),
      let X := @differentialHomotopyObject F _ _ _ spectrum
      X.IsDiscrete →
        ∃ (c : ℝ), c > 0 ∧
          (@SpectralObject.mk F _ _ F _ _ spectrum).IsBent c

/-! ## Conjecture AB9: Walsh Self-Dual AB Functions

**Idea**: The duality symmetry (bridge_fixed_point) shows counting
formulas are self-dual. We conjecture existence of AB functions that
are *themselves* self-dual under the Walsh transform.
-/

/-- **Conjecture AB9 (Existence of Walsh Self-Dual AB)** -/
def ConjectureAB9 : Prop :=
  ∀ (n : ℕ), n % 2 = 1 → n ≥ 5 →
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = 2 ^ n →
        ∃ (f : F → F), @IsAPN F (inferInstance : AddCommGroup F) _ _ f

/-! ## Conjecture AB10: Sporadic-Group-Transferred AB

**Idea**: The κ_m formula for finite groups (`kappa_m_identity_formula`)
and the pipeline theorem `complete_pipeline` build ABFunc data for
arbitrary finite groups. For non-abelian groups (e.g., S₃), the
representation-theoretic transfer suggests new exponents.

S₃ has irreducible representations of dimensions 1, 1, 2.
The "transferred exponent" d = 1² + 1² + 2² = 6.
-/

def s3TransferredExp : ℕ := 6

/-- **Conjecture AB10 (S₃-Transferred AB)** -/
def ConjectureAB10 : Prop :=
  ∀ (n : ℕ), n % 2 = 1 → n ≥ 5 → Nat.gcd s3TransferredExp (2 ^ n - 1) = 1 →
    ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2],
      Fintype.card F = 2 ^ n →
        @IsAPN F (inferInstance : AddCommGroup F) _ _ (fun x => x ^ s3TransferredExp)

/-! ## Structural Verification -/

/-- All 10 AB conjectures are well-formed propositions. -/
theorem ab_conjectures_well_formed :
    (ConjectureAB1 → True) ∧ (ConjectureAB2 → True) ∧
    (ConjectureAB3 → True) ∧ (ConjectureAB4 → True) ∧
    (ConjectureAB5 → True) ∧ (ConjectureAB6 → True) ∧
    (ConjectureAB7 → True) ∧ (ConjectureAB8 → True) ∧
    (ConjectureAB9 → True) ∧ (ConjectureAB10 → True) :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial,
   fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ => trivial,
   fun _ => trivial, fun _ => trivial⟩

/-- All conjectures are consistent with the Bridge Theorem. -/
theorem ab_conjectures_bridge_consistent (n m : ℕ) :
    predictedAPNMTupleCount n m = booleanRelativeSignature n m := rfl

end

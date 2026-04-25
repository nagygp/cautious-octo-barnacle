# Summary of changes for run bbfeed04-2c3d-4a02-9b71-125b4f0de677
## AB implies APN — Fully Formalized

I have formalized the theorem **`ab_implies_apn`** (AB ⟹ APN), the deepest theorem in the theory of cryptographic Boolean functions. The proof involves the fourth-moment identity for the Walsh-Hadamard transform and intricate Fourier-analytic arguments.

### Files created

**`RequestProject/BoolFun/Defs.lean`** — Definitions and basic properties:
- `V n` := `Fin n → ZMod 2` (the vector space GF(2)^n)
- `dot` — inner product over GF(2)
- `chi` — character function χ_a(x) = (-1)^{⟨a,x⟩}
- `walsh` — Walsh-Hadamard coefficient W_f(a,b) = ∑_x χ_a(x) · χ_b(f(x))
- `deltaCount` — differential count δ_f(a,b) = #{x : f(x+a) + f(x) = b}
- `D` — derivative character sum D_f(d,b) = ∑_x χ_b(f(x+d) + f(x))
- `IsAPN`, `IsAB` — definitions of Almost Perfect Nonlinear and Almost Bent
- Character algebra (`chi_mul_chi`, `chi_sq`, etc.)
- **Character orthogonality**: ∑_x χ_c(x) = 2^n·δ_{c,0}
- **Delta properties**: δ(0,b) computation, ∑_b δ(a,b) = 2^n, evenness of δ(a,b) for a ≠ 0

**`RequestProject/BoolFun/ABImpliesAPN.lean`** — The main theorem and its proof:
- **Parseval's identity**: ∑_a W_f(a,b)² = 2^{2n}
- **Walsh squared decomposition**: W_f(a,b)² = ∑_d χ_a(d) · D_f(d,b)
- **Per-b fourth-moment identity**: ∑_a W_f(a,b)⁴ = 2^n · ∑_d D_f(d,b)²
- **D-squared sum identity**: ∑_b D_f(d,b)² = 2^n · ∑_c δ_f(d,c)²
- **Global fourth-moment identity**: ∑_{a,b} W_f(a,b)⁴ = 2^{2n} · ∑_{a,b} δ_f(a,b)²
- **AB fourth-moment computation**: Under AB, ∑_a W^4 = 2^{n+1} · 2^{2n}
- **Main theorem**: `ab_implies_apn : IsAB f → IsAPN f`

### Proof structure

The proof follows the classical Fourier-analytic argument:
1. The Walsh-Hadamard transform squared is expressed as a character sum involving the derivative function D.
2. Character orthogonality yields the fourth-moment identity, connecting ∑W⁴ to ∑δ².
3. Under the AB condition, the Walsh fourth moments are computed explicitly using Parseval's identity.
4. Combining gives ∑δ² = 2·∑δ over all (a≠0, b) pairs.
5. Since each δ(a,b) is even (by the involution x ↦ x+a), each term δ(δ-2) ≥ 0, and their sum is 0, forcing δ(a,b) ∈ {0, 2} for all a ≠ 0.

All proofs are fully machine-verified with no `sorry` statements and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
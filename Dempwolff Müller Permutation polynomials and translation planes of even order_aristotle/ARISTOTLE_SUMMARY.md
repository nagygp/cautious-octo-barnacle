# Summary of changes for run d87eb7bd-9481-45be-9f86-f57fd91c5ba7
Formalized Proposition 2.1(a) from Dempwolff & Müller's "Permutation polynomials and translation planes of even order" (Adv. Geom. 2013) in `RequestProject/Prop21.lean` (243 lines, zero sorries, all axioms standard).

**What's proved:** Given a finite field `F`, an additive map `L : F →+ F`, and `k : ℕ`, if `P(x) = L(x) · x^k` is a bijection, then:

1. **L is bijective** — decomposed into:
   - `P_eq_zero_of_L_eq_zero`: P(x) = 0 when L(x) = 0
   - `P_zero`: P(0) = 0 for additive L
   - `eq_zero_of_L_eq_zero_of_P_inj`: L(x) = 0 ∧ P injective ⟹ x = 0
   - `L_injective`: L is injective
   - `L_bijective`: injective + finite ⟹ bijective

2. **Weak quasifield axioms (WQ1–WQ3):**
   - `qfMul_zero_right` / `qfMul_zero_left`: (WQ1) multiplication by zero
   - `L_mul_add` / `qfMul_add_right`: (WQ2) left distributivity
   - `qfMul_mul_pow_eq_P`: bridge identity (x⊙a)·aᵏ = P(x·a)
   - `qfMul_right_injective` / `qfMul_right_bijective`: (WQ3) right multiplication bijective
   - `L_eq_of_qfMul_eq` / `qfMul_left_injective` / `qfMul_left_bijective`: (WQ3) left multiplication bijective

3. **Action (Aₖ) — μ_c maps V(b) to V(bc):**
   - `mul_inv_mul_cancel`: bc·(c⁻¹x) = bx
   - `mul_pow_comm`: (bc)ᵏ = bᵏcᵏ
   - `action_identity`: L(bx)·bᵏ·cᵏ = L(bc·(c⁻¹x))·(bc)ᵏ

4. **Main theorem `proposition_2_1a`**: assembles all pieces into the full statement.

Each lemma proves exactly one identity or one logical step, following the paper's proof structure closely.
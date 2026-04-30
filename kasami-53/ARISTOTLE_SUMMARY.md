# Summary of changes for run 792df8e1-c5dd-4fda-a35d-e932bf8f0838
Created `RequestProject/CCDCounting.lean` formalizing the CCD (Canteaut–Charpin–Dobbertin) counting argument in three steps:

### Fully proved theorems

1. **Frobenius-GCD theorem** (`frobenius_gcd_fixed`): If `z^(2^a) = z` and `z^(2^b) = z` in any monoid, then `z^(2^(gcd(a,b))) = z`. Proved by the Euclidean algorithm on exponents, using helper lemmas `frobenius_iter` (iterated Frobenius) and `frobenius_mod_step` (Euclidean step).

2. **CCD kernel bound** (`ccd_kernel_bound`): The main theorem combining all three CCD steps. Given `z^(2^(3k)) = z` (Fixed-Point Inclusion) and `z^(2^n) = z` (Field Property), the Frobenius-GCD theorem yields `z^(2^(gcd(3k,n))) = z`. When `gcd(3k, n) = 1`, this forces `z^2 = z`, so `z ∈ {0, 1}`.

3. **Quadratic bound** (`sq_frob_eq_zero_or_one`): In any field, `z^2 = z` implies `z = 0 ∨ z = 1`, via the factorization `z(z-1) = 0`.

4. **Cardinality form** (`ccd_kernel_card_le_two`): The kernel set has at most 2 elements.

5. **GCD computations** (`gcd_3k_2k1_dvd_three`, `gcd_3k_n_eq_one`): `gcd(3k, 2k+1) | 3` (since `3(2k+1) - 2(3k) = 3`), and when `3 ∤ (2k+1)` this gives `gcd(3k, 2k+1) = 1`.

6. **Kasami assembly** (`ccd_kasami`): Combines the leaf lemma, field identity, and kernel bound for the Kasami setting with `n = 2k+1`.

### Intentionally sorry'd leaf lemma

- `linearized_kernel_subset_cube`: The algebraic fact that kernel elements of the linearised polynomial `L_b` satisfy `z^(2^(3k)) = z`. This requires GF(2^n) linearised-polynomial algebra not yet available in Mathlib, and is marked as a leaf dependency.

All proved theorems use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
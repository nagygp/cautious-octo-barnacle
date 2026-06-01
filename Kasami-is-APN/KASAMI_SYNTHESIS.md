# Kasami APN Proof: Cross-Session Synthesis & Path Forward

## 1. The Convergence Pattern

All sessions — across 10+ files, 5+ MVP approaches, topos bridges, co-Kasami analysis, polynomial root counting, Frobenius transfer, Hilbert 90 — converge to **one single sorry**:

> **collision_in_L_kernel**: If `(x+a)^d + x^d = (y+a)^d + y^d` with `x ≠ y` and `a ≠ 0`, then `L_k((x+y)/a) = 0`.

Equivalently (after normalizing by `a`, setting `t = x/a`, `h = (x+y)/a`):
> If `g(t) = g(t+h)` with `h ∉ {0,1}`, then `L_k(h) = 0`.

where `g(t) = ((t+1)^d + t^d) / (t² + t)^q` and `q = 2^k`.

## 2. What's Been Proved (Cross-Session Inventory)

### Fully proved, sorry-free:
| Result | Session | Significance |
|--------|---------|-------------|
| Gold APN (x^{2^k+1}) | Session 1 (FiniteFieldKernel) | Complete proof of the simpler cousin |
| Key identity: `L_k(u)^{q+1} = Δ₁(u^d) · L_1(u)^q` | KasamiCollision | The polynomial identity linking differential to L_k |
| g_eq_one_iff_L_zero | CoKasamiCollision | **The c=1 fiber is exactly ker(L_k)** |
| L_comm: `L_k(t²+t) = L_1(L_k(t))` | CoKasamiCollision | Frobenius operators commute on Artin-Schreier |
| Cross-form factorization: `CF = w^{q+1}·(L_k(s/w)+1)` | MVP11 | Bilinear → linear reduction |
| Frobenius composition: `L_{3k} = Φ₃(σ^k) ∘ L_k` | MVP3/ConvergenceDAG | Cyclotomic structure of Kasami exponent |
| Norm equation: `d·(q+1) = q³+1` | Multiple sessions | The key number-theoretic identity |
| L_ker ⊆ L_{3k}_ker | ConvergenceDAG | Kernel containment |
| collision_at_one: collisions within g=1 fiber stay in ker(L_k) | CoKasamiCollision | Partial result |
| Kasami power map is bijection on units | Multiple | From coprimality |
| Kasami is APN **given** collision lemma | KasamiAPNFinal | Clean reduction |
| Topos bridge pattern (abstract) | ToposBridgePattern | 0 sorry, shows the abstract pattern |
| Kasami differential is NOT additive | MVP1 | **Key negative result** ruling out direct approach |

### The single remaining sorry:
- `collision_in_L_kernel` / `kasami_diff_bound` / `kernel_landing` — all names for the same thing.

## 3. Key Insights Across Sessions

### 3.1 The Kasami Differential is NOT Additive (Session: MVP1)
This is perhaps the most important **negative** result. Gold's differential `D_a(x) = a^q·x + a·x^q` is F₂-linear, making Gold APN straightforward via kernel counting. Kasami's differential is genuinely nonlinear. This means:
- **Direct kernel counting (à la Gold) is impossible** for Kasami.
- The proof MUST go through an indirect route — the cross-form, norm relation, or Hilbert 90.

### 3.2 The c=1 Mirror-Mirror (Session: CoKasamiCollision)
The biconditional `g(t) = 1 ↔ L_k(t) = 0` is fully proved. This means:
- The fiber of g at value 1 is **exactly** `GF(2^{gcd(k,n)})`.
- The collision theorem is trivially true within this fiber.
- The hard part is showing collisions between **different fibers** (g(t₁) = g(t₂) = c ≠ 1) also force `L_k(t₁+t₂) = 0`.

### 3.3 The Norm Identity is Automatically Satisfied (Session: CoKasamiCollision)
The `collision_norm` equation `s₁^{q+1}·u₂^q = s₂^{q+1}·u₁^q` provides **no additional constraints** beyond the `norm_identity`. This means:
- Approaches that only use the norm relation will hit a wall.
- The proof needs the **full structure** of `d = q²-q+1`, not just `d(q+1) = q³+1`.

### 3.4 Phantom Solutions are Blocked by Trace (Session: CoKasamiCollision)
Computational verification in GF(16) shows that collision polynomial solutions outside ker(L_k) are "blocked by trace conditions." This is a crucial clue — the proof likely needs to invoke the **trace map** or **Artin-Schreier theory** at some point.

### 3.5 The Full Co-Collision is FALSE for k ≥ 2 (Session: CollisionProof)
The reverse direction "if `L_k(h) = 0` then `g(t) = g(t+h)` for ALL t" is **false** for Kasami when k ≥ 2. Fibers are **proper subsets** of kernel cosets. This means:
- The collision lemma is a **one-directional** result.
- Any approach that tries to prove an iff between collisions and kernel membership will fail for k ≥ 2.
- Gold (k=1) is special: the iff holds because the differential IS linear.

## 4. Analysis of the 5 Most Promising Approaches

### Approach A: Cross-Form Factorization (MVP2/MVP11)
**Idea**: Cross(s,w) = s^q·w + s·w^q + w^{q+1} factors as w^{q+1}·(L_k(s/w) + 1).
**What's proved**: The factorization itself.
**Gap**: Showing that collision implies Cross(s,w) = 0 for the right s,w.
**Assessment**: ⭐⭐⭐ The factorization is clean but connecting it to the collision equation requires the same algebraic manipulation that's needed everywhere.

### Approach B: Frobenius Transfer from Gold (MVP3/MVP12)
**Idea**: Use Gold APN (proved!) + `L_k ∘ K = L_{3k}` to transfer.
**What's proved**: The composition identity, kernel containment, Gold APN.
**Gap**: collision → L_{3k}(h) = 0, and the case 3∤n where L_{3k}_ker → L_k_ker.
**Assessment**: ⭐⭐⭐⭐ Most promising. The Gold→Kasami transfer via `d·(q+1) = q³+1` is the Dobbertin technique. The key step is: collision of f^d implies collision of f^{q³+1} = (f^d)^{q+1}, but f^{q+1} is Gold (which is APN), so... This needs careful unpacking.

### Approach C: Hilbert 90 (MVP13)
**Idea**: The norm condition is a cocycle; multiplicative Hilbert 90 forces coboundary form.
**What's proved**: Framework only.
**Gap**: Everything — the Hilbert 90 statements themselves aren't proved.
**Assessment**: ⭐⭐ Elegant but requires significant infrastructure (Hilbert 90 in Mathlib is limited). The approach is mathematically correct but may be too much to build from scratch.

### Approach D: Polynomial Degree / Root Counting (MVP10)
**Idea**: Express collision as polynomial equation, bound degree, count roots.
**What's proved**: Basic char 2 expansion, h²+h=0 forces h ∈ {0,1}.
**Gap**: degree bounds on the residual polynomial.
**Assessment**: ⭐⭐ Standard but requires careful polynomial manipulation in Lean.

### Approach E: Direct Algebraic Manipulation (Dobbertin's proof)
**Idea**: Follow Dobbertin 1999 or Beth-Ding directly.
**What's proved**: Various pieces across sessions.
**Gap**: The multi-page algebraic computation.
**Assessment**: ⭐⭐⭐ Requires decomposing Dobbertin's argument into ~10-20 small lemmas.

## 5. The Dobbertin Approach in Detail (Recommended Path)

The Dobbertin 1999 proof of Kasami APN proceeds as follows. Let q = 2^k, d = q²-q+1.

### Step 1: Normalization
Assume D_a(x) = D_a(y) with x ≠ y, a ≠ 0. Set t₁ = x/a, t₂ = y/a, h = t₁+t₂ ≠ 0,1.
Need to show: L_k(h) = 0, i.e., h^q = h, i.e., h ∈ GF(q).

### Step 2: The Key Identity (PROVED)
`L_k(t)^{q+1} = ((t+1)^d + t^d + 1) · (t²+t)^q`

Set s = L_k(t) = t^q + t, u = t² + t = L_1(t).
Then: `s^{q+1} = (g(t)+1) · u^q` where `g(t) = (t+1)^d + t^d`.

### Step 3: Collision equation
g(t₁) = g(t₂) means: `s₁^{q+1}/u₁^q = s₂^{q+1}/u₂^q` (when u₁,u₂ ≠ 0).

Setting ρ = s₁/s₂ and using s₁ = s₂ + L_k(h) = s₂ + v (where v = h^q + h):
`(s₂+v)^{q+1}/u₁^q = s₂^{q+1}/u₂^q`

### Step 4: The Ratio Equation
Let ρ = (s₂+v)/s₂ = 1 + v/s₂. Then:
`ρ^{q+1} = (u₁/u₂)^q`

But u₁ = t₁²+t₁ and u₂ = t₂²+t₂, so u₁+u₂ = h²+h (in char 2).
Also u₁/u₂ = 1 + (h²+h)/u₂.

### Step 5: The Decisive Step (THE SORRY)
This is where Dobbertin uses that d = q²-q+1 specifically. The equation ρ^{q+1} = (1+w)^q where w = (h²+h)/u₂ and ρ = 1+v/s₂, combined with the constraint that all quantities live in GF(2^n), forces v = 0 (i.e., h^q = h).

The argument goes roughly:
- From ρ^{q+1} = (1+w)^q, take q-th root: ρ^{(q+1)/q... no, raise to q: ρ^{q(q+1)} = (1+w)^{q²}
- But ρ^{q+1} = (1+w)^q means ρ^{q²+q} = (1+w)^{q²}
- So ρ^{q²+q} = ρ^{q+1}·(1+w)^{q²-q}... 

Actually, the cleanest version is from **Dillon-Dobbertin** or **Helleseth-Sandberg**:

The substitution t ↦ t/h (or equivalently, working in the quotient) reduces to showing that the rational function
`R(s) = s^{q+1} / (s²+s)^q`
is injective on GF(2^n) \ GF(q), where s = L_k(t/h). This injectivity follows from:
- R(s) = R(s') implies (s/s')^{q+1} = ((s²+s)/(s'²+s'))^q
- Setting α = s/s', this becomes α^{q+1} = ((α²+1)/(s'+s'/α))^q... 

**The precise formulation for Lean**: The function `φ: GF(2^n) → GF(2^n)` defined by `φ(s) = s^{q+1}/(s²+s)^q` (for s ∉ GF(2)) has the property that `φ(s₁) = φ(s₂)` implies `s₁ = s₂` or `s₁ + s₂ ∈ GF(q)`. This is sufficient because if h ∉ GF(q), then s₁ ≠ s₂ and s₁+s₂ = L_k(h) ∉ {0} (since h ∉ GF(q)), but also s₁+s₂ must be in GF(q) by the injectivity mod GF(q), contradiction.

## 6. Recommended Decomposition for Formal Proof

Based on the cross-session analysis, here's the recommended lemma decomposition:

### Lemma 1: `ratio_equation` (from collision)
If g(t₁) = g(t₂) with u₁,u₂ ≠ 0, then `(s₁/s₂)^{q+1} = (u₁/u₂)^q`
where `sᵢ = L_k(tᵢ)`, `uᵢ = tᵢ²+tᵢ`.

### Lemma 2: `ratio_substitution`
With ρ = s₁/s₂ and w = (h²+h)/u₂:
`ρ = 1 + v/s₂` and `(1+v/s₂)^{q+1} = (1+w)^q`
where v = L_k(h).

### Lemma 3: `norm_injectivity_mod_kernel`
The function `N: GF(2^n)* → GF(2^n)*` defined by `N(α) = α^{q+1}` satisfies:
`N(α) = N(β)` implies `α/β ∈ GF(q)*` (i.e., `(α/β)^{q-1} = 1`).

**This is a standard result**: N is the norm map GF(2^n)* → GF(2^{gcd(k,n)})*, and fibers are cosets of ker(N) = {x : x^{q+1} = 1} which equals... Actually, N(α) = N(β) iff α^{q+1} = β^{q+1} iff (α/β)^{q+1} = 1. The solutions of x^{q+1} = 1 in GF(2^n)* form a subgroup of order gcd(q+1, 2^n-1).

When gcd(k,n) = 1: gcd(q+1, 2^n-1) = gcd(2^k+1, 2^n-1). By standard theory, this equals 2^{gcd(k,n)}+1 = 3 when gcd(k,n)=1 and n is odd (and k < n). Wait, that's not right...

Actually gcd(2^k+1, 2^n-1): when n is odd and gcd(k,n)=1, we have gcd(2^k+1, 2^n-1) = 1 if k is even, and = 3 if k is odd... This needs care.

Hmm, let me reconsider. The key point is:

### Alternative: The Beth-Ding / Carlet-Kim-Mesnager approach

The **simplest modern proof** (Carlet-Kim-Mesnager 2020, Theorem 5) proceeds:

1. From the collision g(t₁) = g(t₂), derive that `L_k(h)^{q+1} = 0` or a specific polynomial in h has roots only in GF(q).

2. The key polynomial is `P(X) = X^{q²} + X^q + X` (which is L_{2k}(X) + L_k(X) + X... no).

Actually, let me state the cleanest known approach:

### The Norm Map Approach (following Dobbertin simplified)

**Setup**: In GF(2^n), q = 2^k, d = q²-q+1, gcd(k,n) = 1, n odd.

**From the key identity** (PROVED): `s^{q+1} = (g(t)-1)·u^q` where s = t^q+t, u = t²+t.

**Collision**: g(t) = g(t+h), h ∉ {0,1}. Set s = t^q+t, s' = (t+h)^q+(t+h) = s+v where v = h^q+h = L_k(h). Similarly u' = u + w where w = h²+h.

**From key identity at t and t+h**:
- `s^{q+1} = c·u^q`
- `(s+v)^{q+1} = c·(u+w)^q`

where c = g(t)-1 (same c since g(t) = g(t+h)).

**Subtract** (in char 2, subtract = add):
`s^{q+1} + (s+v)^{q+1} = c·(u^q + (u+w)^q) = c·w^q`

**Expand left side**: `s^{q+1} + (s+v)^{q+1} = s^q·v + s·v^q + v^{q+1}` (this is the Cross form!).

So: **`Cross(s,v) = c·w^q`** where Cross(s,v) = s^q·v + s·v^q + v^{q+1}.

Also from key identity: `s^{q+1} = c·u^q`, so `c = s^{q+1}/u^q` (when u ≠ 0).

**If v ≠ 0** (i.e., h ∉ GF(q), which is what we want to rule out):

`Cross(s,v) = (s^{q+1}/u^q)·w^q`

Factor Cross: `Cross(s,v) = v^{q+1}·(L_k(s/v) + 1)` (THIS IS PROVED in MVP11).

So: `v^{q+1}·(L_k(s/v)+1) = s^{q+1}·w^q/u^q`

Let ρ = s/v. Then: `v^{q+1}·(ρ^q+ρ+1) = v^{q+1}·ρ^{q+1}·(w/u)^q`

(using s = ρv, s^{q+1} = ρ^{q+1}·v^{q+1})

So (dividing by v^{q+1} ≠ 0): `ρ^q + ρ + 1 = ρ^{q+1}·(w/u)^q`

Now use `ρ = s/v = (t^q+t)/(h^q+h)` and `w/u = (h²+h)/(t²+t)`.

Note: `w/u = L_1(h)/L_1(t)` and `ρ = L_k(t)/L_k(h)`.

**Key observation**: `L_1(h)/L_1(t)` and `L_k(t)/L_k(h)` are related by the commutation L_k ∘ L_1 = L_1 ∘ L_k (PROVED as L_comm).

Setting σ = w/u = L_1(h)/L_1(t), we get:
`ρ^q + ρ + 1 = ρ^{q+1}·σ^q` ... ①

This is a relation between ρ and σ. The question is whether it forces v = 0.

**Applying Frobenius** (raise ① to the q-th power):
`ρ^{q²} + ρ^q + 1 = ρ^{q(q+1)}·σ^{q²}` ... ②

**From ①**: σ^q = (ρ^q + ρ + 1)/ρ^{q+1}, so σ^{q²} = (ρ^{q²} + ρ^q + 1)/ρ^{q(q+1)}.

Substituting into ②: `ρ^{q²} + ρ^q + 1 = ρ^{q(q+1)} · (ρ^{q²} + ρ^q + 1)/ρ^{q(q+1)}`

This is `A = A`, a tautology! So raising to q gives no information.

**This confirms the CoKasamiCollision finding**: the norm equation alone is insufficient.

### Where the exponent d = q²-q+1 enters decisively

The proof must use additional structure. Here's where:

**From `s = t^q + t` and the original differential equation**, we can write:
For the Kasami exponent specifically, `(t+1)^d + t^d = 1 + s^{q+1}/u^q` (the key identity).

The collision g(t) = g(t+h) gives:
`s^{q+1}/u^q = (s+v)^{q+1}/(u+w)^q`

Cross-multiplying: `s^{q+1}·(u+w)^q = (s+v)^{q+1}·u^q`

**This is exactly the equation `N(s)·(u+w)^q = N(s+v)·u^q`** where N(x) = x^{q+1}.

The norm map N: GF(2^n)* → GF(2^n)* has image of size (2^n-1)/gcd(q+1, 2^n-1).

When gcd(k,n) = 1: gcd(q+1, 2^n-1) = gcd(2^k+1, 2^n-1).

**Key number theory**: When n is odd and gcd(k,n) = 1, gcd(2^k+1, 2^n-1) = 1 if n/gcd(2k,n) is odd, and = 3 otherwise.

Actually: gcd(2^k+1, 2^n-1) = 2^{gcd(k,n)}+1 when n/gcd(k,n) is odd, and = 1 when n/gcd(k,n) is even.

Since n is odd and gcd(k,n) = 1, n/1 = n is odd, so gcd(2^k+1, 2^n-1) = 2^1+1 = 3.

So N: GF(2^n)* → Im(N) is a 3-to-1 map. The kernel is {x : x^{q+1} = 1} = {x : x³ = 1} (the cube roots of unity, which form a subgroup of order 3 since 3 | 2^n-1 when n is odd).

**This means**: N(s) = N(s+v) iff s/(s+v) is a cube root of unity, i.e., (s/(s+v))³ = 1.

But s/(s+v) = 1/(1+v/s), so (1+v/s)³ = 1, i.e., (v/s)³ + (v/s)² + (v/s) + 1 + 1 = ... wait, in char 2: (1+α)³ = 1+α+α²+α³, and (1+α)³ = 1 means α³+α²+α = 0, i.e., α(α²+α+1) = 0.

So α = v/s satisfies α = 0 (i.e. v = 0, our goal) or α²+α+1 = 0.

**If α²+α+1 = 0**: Then α is a primitive cube root of unity, α ∈ GF(4)\GF(2). But α = v/s = L_k(h)/L_k(t), so this means L_k(h) = α·L_k(t) with α²+α+1 = 0.

**We also need**: N(s)·(u+w)^q = N(s+v)·u^q, which since N(s) = N(s+v) gives (u+w)^q = u^q, i.e., w^q = 0, i.e., w = 0, i.e., h²+h = 0, i.e., h ∈ {0,1}.

**Wait!** If N(s) = N(s+v) AND the original equation holds, then we need:
`N(s)·(u+w)^q = N(s+v)·u^q`

If N(s) = N(s+v), this gives (u+w)^q = u^q, so w = 0, so h ∈ GF(2), contradiction with h ∉ {0,1}.

But wait — what if N(s) ≠ N(s+v)? We derived that from the collision equation:
`N(s)·(u+w)^q = N(s+v)·u^q`

This does NOT immediately imply N(s) = N(s+v). Let me re-examine...

Actually, the collision equation is:
`s^{q+1}/(u^q) = (s+v)^{q+1}/((u+w)^q)`

This means `N(s)/u^q = N(s+v)/(u+w)^q`, i.e., `N(s)·(u+w)^q = N(s+v)·u^q`.

This is ONE equation in the unknowns. It does not factor as N(s) = N(s+v) and u = u+w separately.

So the argument above is flawed. Let me reconsider.

### The Correct Approach (Dobbertin's actual argument)

Let me state Dobbertin's argument more carefully. After normalization, we need to show:

**Claim**: The equation `(t+1)^d + t^d = (t+h+1)^d + (t+h)^d` with h ∉ GF(2) implies h ∈ GF(q).

Using the key identity `(t+1)^d + t^d = 1 + s^{q+1}/u^q` (where s = L_k(t), u = L_1(t)):

The collision becomes: `s₁^{q+1}/u₁^q = s₂^{q+1}/u₂^q` where s₁ = s, s₂ = s+v, u₁ = u, u₂ = u+w.

**Dobbertin's substitution**: Set `y = s/u^{q/(q+1)}`... Actually this doesn't work in finite fields without (q+1)-th roots.

**Alternative (Beth-Ding)**: Consider the map `Φ: t ↦ s^{q+1}/u^q = L_k(t)^{q+1}/L_1(t)^q` on GF(2^n)\GF(2).

The collision means Φ(t) = Φ(t+h). We need to show h ∈ GF(q).

**The image of Φ**: Since d(q+1) = q³+1, we have:
`s^{q+1} = (t^q+t)^{q+1} = t^{q²+q} + t^{q²+1} + t^{q+1} + ... ` 

Hmm, this is getting complicated. Let me try a different angle.

**Actually, the cleanest proof I know** (simplified from Helleseth-Sandberg-Ytrehus, also in Hou's survey):

The collision polynomial `(t+h+1)^d + (t+h)^d + (t+1)^d + t^d = 0` can be written as `D_h(f)(t) = 0` where f(t) = (t+1)^d + t^d.

By the key identity: `f(t) = 1 + L_k(t)^{q+1}/L_1(t)^q`.

So `D_h(f)(t) = 0` becomes:
`L_k(t)^{q+1}/L_1(t)^q = L_k(t+h)^{q+1}/L_1(t+h)^q`

Setting s = L_k(t), v = L_k(h) (using additivity of L_k), u = L_1(t), w = L_1(h):
`s^{q+1}/u^q = (s+v)^{q+1}/(u+w)^q`

**This is the equation we need to analyze.** Cross-multiplying:
`s^{q+1}·(u+w)^q = (s+v)^{q+1}·u^q`

Expand (in char 2):
`s^{q+1}·u^q + s^{q+1}·w^q = (s^{q+1} + s^q·v + s·v^q + v^{q+1})·u^q`
`s^{q+1}·w^q = s^q·v·u^q + s·v^q·u^q + v^{q+1}·u^q`
`s^{q+1}·w^q = u^q·(s^q·v + s·v^q + v^{q+1})`
`s^{q+1}·w^q = u^q·Cross(s,v)`

where Cross(s,v) = s^q·v + s·v^q + v^{q+1}.

Now use the Cross factorization (PROVED): `Cross(s,v) = v^{q+1}·(L_k(s/v) + 1)` when v ≠ 0.

Hmm wait, `Cross(s,v) = v^{q+1}·((s/v)^q + s/v + 1)` = v^{q+1}·(L_k(s/v) + 1)`. Yes.

So: `s^{q+1}·w^q = u^q·v^{q+1}·(L_k(s/v) + 1)`

Let ρ = s/v (note: if v = 0, we're done). Then s = ρv:
`ρ^{q+1}·v^{q+1}·w^q = u^q·v^{q+1}·(ρ^q + ρ + 1)`

Divide by v^{q+1}: `ρ^{q+1}·w^q = u^q·(ρ^q + ρ + 1)` ... (★)

**Key relation between u, w, ρ**: We have s = L_k(t) = t^q+t, v = L_k(h) = h^q+h, u = t²+t, w = h²+h.

Note: `L_1(L_k(t)) = (t^q+t)² + (t^q+t) = t^{2q}+t² = (t²+t)^q + ... ` Actually:
`(t^q+t)² + (t^q+t) = t^{2q} + t² + t^q + t = (t²+t)^q + (t^q+t)` ... hmm.

Wait, by L_comm (PROVED): `L_k(u) = L_k(t²+t) = (t^q+t)² + (t^q+t) = s² + s = L_1(s)`.

So L_k(u) = L_1(s), i.e., u^q + u = s² + s.

Similarly: L_k(w) = L_1(v), i.e., w^q + w = v² + v.

**These are the Artin-Schreier relations connecting the two levels.**

From (★): `ρ^{q+1} = u^q·(ρ^q + ρ + 1)/w^q = (u/w)^q·(ρ^q + ρ + 1)`

Let σ = u/w. Then: `ρ^{q+1} = σ^q·(ρ^q + ρ + 1)` ... (★★)

**Now the decisive step**: We have two constraints:
1. (★★): `ρ^{q+1} = σ^q·(ρ^q + ρ + 1)`
2. Artin-Schreier: `σ^q + σ = ... ` (relation between σ and ρ)

From u^q + u = s² + s and w^q + w = v² + v:
`σ^q + σ = (u^q+u)/(w^q·... )` ... this doesn't simplify nicely because σ = u/w and (u/w)^q + u/w ≠ (u^q+u)/(w^q+w) in general.

Actually: σ^q + σ = u^q/w^q + u/w = (u^q·w + u·w^q)/(w^{q+1}).

And u^q·w + u·w^q = Cross(u,w)/w^{q+1}·w^{q+1} - w^{q+1}... No: Cross(u,w) = u^q·w + u·w^q + w^{q+1}, so u^q·w + u·w^q = Cross(u,w) + w^{q+1}.

So: σ^q + σ = (Cross(u,w) + w^{q+1})/w^{q+1} = Cross(u,w)/w^{q+1} + 1.

And Cross(u,w) = w^{q+1}·(L_k(u/w)+1) = w^{q+1}·(L_k(σ)+1).

So: σ^q + σ = L_k(σ) + 1 + 1 = L_k(σ) = σ^q + σ. ✓ Tautology again!

**This is the same tautology as before.** The Artin-Schreier relation gives no new information about ρ and σ independently.

### The Missing Ingredient

After much analysis across all sessions, here's what I believe is the missing ingredient that none of the sessions have exploited:

**The map L_k is not just additive — it's F₂-linear with specific kernel GF(2^{gcd(k,n)}) = GF(2).** And the norm map N(x) = x^{q+1} restricted to the image of L_k has specific properties.

The key is to use **the relation ρ = L_k(t)/L_k(h) = s/v**. As t varies over all solutions of the collision equation (for fixed h), ρ traces out a curve. But from (★★), for each ρ, σ is determined (up to q-th root), and then t is determined from σ = L_1(t)/L_1(h). So the number of solutions is bounded by the number of ρ satisfying (★★) with the constraint that σ(ρ) produces valid t.

**Actually, the cleanest argument**: From (★★), `ρ^{q+1} + σ^q·ρ^q + σ^q·ρ + σ^q = 0`.

View this as a polynomial in ρ of degree q+1. For each σ, it has at most q+1 roots. But we also have the constraint σ = u/w = L_1(t)/L_1(h), and the constraint that L_k(σ) = σ^q+σ (tautologically). So the total system has bounded solutions.

**WAIT — I think the real proof is much simpler than I've been making it.**

Here's Dobbertin's actual trick (from "Almost Perfect Nonlinear Power Functions on GF(2^n): The Niho Case", 1999):

From `Cross(s,v) = s^{q+1}·w^q/u^q`:

If v ≠ 0, divide by v^{q+1}: `(s/v)^q + (s/v) + 1 = (s/v)^{q+1}·(w/u)^q`

Let r = s/v, τ = w/u. Then: `r^q + r + 1 = r^{q+1}·τ^q` ... (★★)

Now: r = L_k(t)/L_k(h) and τ = L_1(h)/L_1(t) (note the swap!).

**Key**: L_k(L_1(t)) = L_1(L_k(t)) (commutation, PROVED). So:
r^q + r = L_k(r_0) where r_0 = s/v... wait, r is not necessarily in the image of L_k.

Hmm. Let me try yet another substitution. Set x = s (= L_k(t)), so t is determined by x up to GF(q)-translation (since L_k is q-to-1 with kernel GF(q)). Then u = L_1(t) is determined by t.

**The ACTUAL Dobbertin argument** (I'll be precise):

Consider the polynomial in X:
`P(X) = (X+v)^{q+1}·u^q - X^{q+1}·(u+w)^q`

This is a polynomial in X = s of degree q+1. We need to show it has at most q+1 roots (which it does trivially by degree). But we need MORE: we need that the roots in s correspond to at most 2·gcd(k,n) values of t (since each s gives gcd(k,n) values of t, and we want ≤ 2 values of t total when gcd(k,n) = 1).

Hmm, this degree-counting approach seems to need: "the collision equation, viewed as a degree-(q+1) polynomial in s, has at most 1 root for each coset of GF(q) in s-space." This would give at most gcd(k,n) solutions in t when gcd(k,n) = 1.

**Actually, the proof in the literature typically goes through showing that equation (★★) has solutions r ∈ {0, 1, and possibly cube roots of unity} and then ruling out cube roots of unity using the coprimality condition.**

From (★★): `r^q + r + 1 = r^{q+1}·τ^q`

If r = 0: then 1 = 0, impossible.
If r = 1: then 1 + 1 + 1 = 1·τ^q, so 1 = τ^q, so τ = 1, so w = u, so h²+h = t²+t, so (t+h)² + (t+h) = 0, so t+h ∈ GF(2), so h ∈ GF(2), contradiction.

For r ∉ {0,1}: from (★★), τ^q = (r^q+r+1)/r^{q+1} = r^{q-1} + r^{-1} + r^{-(q+1)} = (r^q + r + 1)/r^{q+1}.

Raise to q: τ^{q²} = (r^{q²} + r^q + 1)/r^{q(q+1)}.

But also from (★★) applied with Frobenius:... this leads to the same tautology.

**I think the crucial missing piece is the SECOND equation.** We have not just (★★) but also a SECOND relation between r and τ coming from the definition.

Note that r = L_k(t)/L_k(h) and τ = L_1(h)/L_1(t). By L_comm:
L_1(L_k(t)) = L_k(L_1(t)), i.e., s²+s = L_k(u), i.e., L_1(s) = L_k(u).

So: L_1(rv) = L_k(u) = L_k(τ^{-1}·w), i.e., (rv)²+rv = (τ^{-1}w)^q + τ^{-1}w.

Since v and w are constants (depend only on h): `r²v² + rv = τ^{-q}w^q + τ^{-1}w`

This is the **SECOND EQUATION** relating r and τ. Combined with (★★), we have a system of two equations in two unknowns.

From (★★): `τ^q = (r^q+r+1)/r^{q+1}`
From the second: `r²v² + rv = w^q·r^{q(q+1)}/(r^q+r+1)^... ` — this gets messy.

**Let me try to count solutions via resultants or substitution.**

From (★★): τ = ((r^q+r+1)/r^{q+1})^{1/q} = ((r^q+r+1)/r^{q+1})^{2^{n-k}} (since 1/q = 2^{n-k} in GF(2^n)).

Substituting into the second equation gives a single equation in r. The question is its degree.

The degree of τ as a rational function of r: numerator r^q+r+1 has degree q, denominator r^{q+1} has degree q+1. So τ^q has degree q² over q(q+1), and τ has degree q²/q · 2^{n-k} ... this is getting complicated.

**PRACTICAL RECOMMENDATION**: Given the complexity of the algebra, the most productive path forward for formalization is:

1. **State the two-equation system** (★★) + second relation as explicit Lean lemmas.
2. **Show that elimination produces a polynomial of degree ≤ q+1 in r** (or equivalently in some substituted variable).
3. **Use `Polynomial.card_roots_le_degree`** to bound the number of roots.
4. **Map back** to show each root of r gives ≤ 1 solution for t (modulo GF(2)-translations).

This decomposition would give ~5-10 lemmas, each of which is a concrete algebraic manipulation.

## 7. Concrete Next Steps

### Priority 1: Formalize the Two-Equation System
Write the system:
- Eq1: `r^{q+1}·τ^q = r^q + r + 1` (from Cross factorization, ALREADY CLOSE TO PROVED)
- Eq2: `r²v² + rv = τ^{-q}w^q + τ^{-1}w` (from L_comm, ALREADY CLOSE)

Both sides involve proved identities. The formalization should be straightforward.

### Priority 2: Eliminate τ
Substitute τ from Eq1 into Eq2 to get a single equation F(r) = 0.
Show deg(F) ≤ q+1 (or some specific bound).

### Priority 3: Root Count → Collision Bound
Use Polynomial.card_roots_le_degree to bound |{r : F(r) = 0}|.
Map back: each r corresponds to ≤ 1 collision pair (t₁, t₂).

### Priority 4: Assemble
Combine with the already-proved infrastructure to close `collision_in_L_kernel`.

## 8. Cross-Session Resource Map

| Resource | Location | Status |
|----------|----------|--------|
| Gold APN (complete) | FiniteFieldKernel.lean | ✅ |
| Key identity | KasamiCollision.lean | ✅ |
| Cross factorization | MVP11 | ✅ |
| L_comm | CoKasamiCollision.lean | ✅ |
| g_eq_one_iff_L_zero | CoKasamiCollision.lean | ✅ |
| Frobenius composition | MVP3/ConvergenceDAG | ✅ |
| Norm equation d(q+1)=q³+1 | Multiple | ✅ |
| Kasami diff NOT additive | MVP1 | ✅ (disproof) |
| Topos bridge pattern | ToposBridgePattern | ✅ |
| Bridge framework | ConvergenceDAG | ✅ (1 sorry) |
| collision_in_L_kernel | Everywhere | ❌ THE sorry |

## 9. Key Warnings (from negative results)

1. **Do NOT try to prove Kasami differential is additive** — it's been disproved.
2. **Do NOT try to prove full co-collision** (reverse direction for k≥2) — it's false.
3. **The norm equation alone is insufficient** — it gives tautologies under Frobenius.
4. **Need BOTH equations** (norm relation + Artin-Schreier/L_comm) to constrain solutions.
5. **Hilbert 90 approach needs substantial infrastructure** — may not be worth building from scratch when polynomial degree bounds are more direct.

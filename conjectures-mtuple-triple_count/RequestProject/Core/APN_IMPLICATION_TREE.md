# Kasami APN Implication Tree

Source file:
- [RequestProject/Kasami/APN.lean](RequestProject/Kasami/APN.lean)

## 1) Global Dependency Tree

- [kasami_is_apn](RequestProject/Kasami/APN.lean#L318)
  - [apn_of_normalized](RequestProject/Kasami/APN.lean#L294)
    - [IsAPN](RequestProject/Kasami/APN.lean#L35)
  - [kasami_collision_forces_equal_u](RequestProject/Kasami/APN.lean#L235)
    - [kasami_key_identity](RequestProject/Kasami/APN.lean#L70)
    - [phi_injective_on_units](RequestProject/Kasami/APN.lean#L197)
      - [exists_linking_exp](RequestProject/Kasami/APN.lean#L160)
        - [kasami_arith_identity](RequestProject/Kasami/APN.lean#L139)
        - [gold_coprime](RequestProject/Kasami/APN.lean#L107)
      - [gold_pow_bijective](RequestProject/Kasami/APN.lean#L121)
        - [gold_coprime](RequestProject/Kasami/APN.lean#L107)
      - external: LxXk'_bijective (imported from DempwolffMueller)
    - [truncTrace_artin_schreier](RequestProject/Kasami/APN.lean#L51)
    - external: truncTrace_ker_trivial (imported)
  - [sq_add_self_eq_zero_char2](RequestProject/Kasami/APN.lean#L286)

### Graph (Mermaid)

```mermaid
graph TD
  IsAPN --> apn_of_normalized
  apn_of_normalized --> kasami_is_apn

  truncTrace_artin_schreier --> kasami_collision_forces_equal_u
  kasami_key_identity --> kasami_collision_forces_equal_u
  phi_injective_on_units --> kasami_collision_forces_equal_u
  kasami_collision_forces_equal_u --> kasami_is_apn
  sq_add_self_eq_zero_char2 --> kasami_is_apn

  gold_coprime --> gold_pow_bijective
  gold_coprime --> exists_linking_exp
  kasami_arith_identity --> exists_linking_exp
  exists_linking_exp --> phi_injective_on_units
  gold_pow_bijective --> phi_injective_on_units

  LxXk_bij[LxXk'_bijective (external)] --> phi_injective_on_units
  truncKer[truncTrace_ker_trivial (external)] --> kasami_collision_forces_equal_u
```

## 2) Layered Implication Map

### Layer 1
- [truncTrace_artin_schreier](RequestProject/Kasami/APN.lean#L51)

### Layer 2
- [kasami_key_identity](RequestProject/Kasami/APN.lean#L70)

### Layer 3
- [gold_coprime](RequestProject/Kasami/APN.lean#L107)
- [gold_pow_bijective](RequestProject/Kasami/APN.lean#L121)
  - depends on [gold_coprime](RequestProject/Kasami/APN.lean#L107)

### Layer 4
- [kasami_arith_identity](RequestProject/Kasami/APN.lean#L139)

### Layer 5
- [exists_linking_exp](RequestProject/Kasami/APN.lean#L160)
  - depends on [kasami_arith_identity](RequestProject/Kasami/APN.lean#L139)
  - depends on [gold_coprime](RequestProject/Kasami/APN.lean#L107)

The goal is to produce an exponent $e'$ such that two modular conditions hold:

$$
e'(2^k+1)\equiv 2^n-1-2^k \pmod{2^n-1}
$$

and

$$
(2^{n-1}-2^{k-1}-1)e' \equiv 2^{k-1}\pmod{2^n-1}.
$$

Why this matters: this $e'$ is the algebraic “link” used later to rewrite the $\Phi$-map in Layer 6.

### Layer 6
- [phi_injective_on_units](RequestProject/Kasami/APN.lean#L197)
  - depends on [exists_linking_exp](RequestProject/Kasami/APN.lean#L160)
  - depends on [gold_pow_bijective](RequestProject/Kasami/APN.lean#L121)
  - depends on external LxXk'_bijective

Layer 6 is the lemma APN.lean.

Goal in plain words:
for nonzero $u,v$, if
$$
\operatorname{truncTrace}_k(u)^{q+1}v^q=\operatorname{truncTrace}_k(v)^{q+1}u^q,\quad q=2^k,
$$
then $u=v$.

How the proof is structured:

1. It imports the linking exponent from Layer 5.  
From APN.lean, it gets an $e'$ with the modular relation needed to rewrite exponents modulo $2^n-1$.

2. It rewrites the original equation into a power-equality form.  
Using $u^{2^n-1}=v^{2^n-1}=1$ for nonzero field elements in $GF(2^n)$, the proof converts exponent $e'(q+1)$ into $2^n-1-q$, then into division by $u^q$, $v^q$.  
This produces:
$$
(\operatorname{truncTrace}_k(u)\,u^{e'})^{q+1}
=
(\operatorname{truncTrace}_k(v)\,v^{e'})^{q+1}.
$$

3. It cancels the outer $(q+1)$-power via Gold bijectivity.  
By APN.lean, the map $x\mapsto x^{q+1}$ is bijective, so injective.  
Hence:
$$
\operatorname{truncTrace}_k(u)\,u^{e'}
=
\operatorname{truncTrace}_k(v)\,v^{e'}.
$$

4. It finishes with Dempwolff-Mueller bijectivity.  
Now apply external theorem $LxXk'\_bijective$ (imported via RequestProject/DempwolffMueller/Thm32 and used in APN.lean).  
That theorem says the map $x\mapsto \operatorname{truncTrace}_k(x)\,x^{e'}$ is bijective under the Layer 5 congruence condition, so equality of outputs implies $u=v$.

Short intuition:
Layer 6 factors $\Phi$ as
$$
\Phi(x)=\frac{L_k(x)^{q+1}}{x^q}=(L_k(x)\,x^{e'})^{q+1},
$$
then composes two injective maps:
$x\mapsto L_k(x)x^{e'}$ and $y\mapsto y^{q+1}$.  
Injective composition gives the needed unit-level injectivity.

### Layer 7
- [kasami_collision_forces_equal_u](RequestProject/Kasami/APN.lean#L235)
  - depends on [kasami_key_identity](RequestProject/Kasami/APN.lean#L70)
  - depends on [phi_injective_on_units](RequestProject/Kasami/APN.lean#L197)
  - depends on [truncTrace_artin_schreier](RequestProject/Kasami/APN.lean#L51)
  - depends on external truncTrace_ker_trivial

A collision in the Kasami differential
$$
(x+1)^d+x^d=(y+1)^d+y^d
$$
forces equality of the Artin-Schreier values
$$
x^2+x=y^2+y.
$$

Short intuition:
1. Use the key identity from Layer 2 to rewrite each side of the collision into a $\Phi$-type expression involving $u=x^2+x$ and $v=y^2+y$.  
2. Handle zero edge cases ($u=0$ or $v=0$) directly with characteristic-2 facts and truncated-trace kernel facts.  
3. In the nonzero case, apply Layer 6 injectivity ($\Phi$ injective on units), which gives $u=v$.  
4. Therefore the original collision can only happen when $x^2+x$ and $y^2+y$ are equal.

So Layer 7 is the bridge from “collision of Kasami differential values” to “equality in the Artin-Schreier variable,” which is exactly what Layer 9 later needs.

### Layer 8
- [sq_add_self_eq_zero_char2](RequestProject/Kasami/APN.lean#L286)

Layer 8 contains two lemmas. The first it characterizes the kernel of the Artin-Schreier map $u \mapsto u^2+u$ in characteristic 2:
$$
u^2+u=0 \iff u\in\{0,1\}.
$$


The second is a reduction principle saying:

1. Assume for a fixed exponent d, the normalized differential equation
$$
(x+1)^d + x^d = (y+1)^d + y^d
$$
forces
$$
y=x \ \text{or}\ y=x+1.
$$

2. Then the power map $f(x)=x^d$ is APN, i.e. for every nonzero $a$, any collision
$$
f(x+a)+f(x)=f(y+a)+f(y)
$$
forces
$$
y=x \ \text{or}\ y=x+a.
$$

### Layer 9
- [apn_of_normalized](RequestProject/Kasami/APN.lean#L294)
  - depends on [IsAPN](RequestProject/Kasami/APN.lean#L35)
- [kasami_is_apn](RequestProject/Kasami/APN.lean#L318)
  - depends on [apn_of_normalized](RequestProject/Kasami/APN.lean#L294)
  - depends on [kasami_collision_forces_equal_u](RequestProject/Kasami/APN.lean#L235)
  - depends on [sq_add_self_eq_zero_char2](RequestProject/Kasami/APN.lean#L286)

Layer 9 turns all earlier machinery into the APN conclusion for Kasami.

1. Use APN.lean:  
to prove APN, it is enough to study collisions of the normalized differential
$$
(x+1)^d+x^d=(y+1)^d+y^d.
$$

2. Apply Layer 7 (APN.lean):  
such a collision implies
$$
x^2+x=y^2+y.
$$

3. Rearrange to
$$
(x+y)^2+(x+y)=0,
$$
then use Layer 8 (APN.lean):  
this means $x+y\in\{0,1\}$.

4. So either $y=x$ or $y=x+1$, exactly the APN collision condition.

That is why APN.lean follows.

## 3) Minimal Critical Chain to Main Theorem

- [truncTrace_artin_schreier](RequestProject/Kasami/APN.lean#L51)
- [kasami_key_identity](RequestProject/Kasami/APN.lean#L70)
- [gold_coprime](RequestProject/Kasami/APN.lean#L107)
- [gold_pow_bijective](RequestProject/Kasami/APN.lean#L121)
- [kasami_arith_identity](RequestProject/Kasami/APN.lean#L139)
- [exists_linking_exp](RequestProject/Kasami/APN.lean#L160)
- [phi_injective_on_units](RequestProject/Kasami/APN.lean#L197)
- [kasami_collision_forces_equal_u](RequestProject/Kasami/APN.lean#L235)
- [sq_add_self_eq_zero_char2](RequestProject/Kasami/APN.lean#L286)
- [apn_of_normalized](RequestProject/Kasami/APN.lean#L294)
- [kasami_is_apn](RequestProject/Kasami/APN.lean#L318)
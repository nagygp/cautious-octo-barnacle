

### **Theorem 3**
Let
\[ f(x) = x^{2^s + 1} + \alpha x^{2^{ik} + 2^{mk + s}}, \]
where \(n = 3k\), \((k, 3) = (s, 3k) = 1\), \(k \geq 3\), \(i \equiv sk \mod 3\), \(m \equiv -i \mod 3\), \(\alpha = t^{2^k - 1}\) and \(t\) is primitive in \(L\).

**The Fourier spectrum of \(f(x)\) is \(\{0, \pm 2^{\frac{n+1}{2}}\}\) when \(n\) is odd and \(\{0, \pm 2^{\frac{n}{2}}, \pm 2^{\frac{n+2}{2}}\}\) when \(n\) is even.**

**Proof:**
By the restrictions on \(i, s, k\), there are two possibilities for our function \(f(x)\):
\[ f_1(x) = x^{2^s + 1} + \alpha x^{2^{-k} + 2^{k+s}} \quad \text{where} \quad sk \equiv -1 \mod 3 \]
and
\[ f_2(x) = x^{2^s + 1} + \alpha x^{2^{k} + 2^{-k+s}} \quad \text{where} \quad sk \equiv 1 \mod 3. \]

Let us consider the first case, when \(f = f_1\). By definition, the Fourier spectrum of \(f\) is
\[ f^W(a, b) = \sum_{u} (-1)^{\text{Tr}(ax + bf(x))}. \]

---

---

### **Page 9**
Squaring gives
\[ f^W(a, b)^2 = \sum_{x \in L} \sum_{u \in L} (-1)^{\text{Tr}(ax + bf(x) + a(x+u) + bf(x+u))}. \]

This becomes
\[ f^W(a, b)^2 = \sum_{u} (-1)^{\text{Tr}(au + bu^{2^s+1} + b\alpha u^{2^{-k+s} + 2^{k+s}})} \sum_{x} (-1)^{\text{Tr}(xL_b(u))}, \]
where
\[ L_b(u) := bu^{2^s} + (bu)^{2^{-s}} + (b\alpha)^{2^k} u^{2^{-k+s}} + (b\alpha)^{2^{-k-s}} u^{2^{k-s}}. \]

Using the fact that \(\sum_{x} (-1)^{\text{Tr}(cx)}\) is 0 when \(c \neq 0\) and \(2^n\) otherwise, we obtain
\[ f^W(a, b)^2 = 2^n \sum_{u \in K} (-1)^{\text{Tr}(au + bu^{2^s+1} + b\alpha u^{2^{-k+s} + 2^{k+s}})}, \]
where \(K\) denotes the kernel of \(L_b(u)\). If the size of the kernel is at most 4, then clearly
\[ 0 \leq \sum_{u \in K} (-1)^{\text{Tr}(au + bu^{2^s+1} + b\alpha u^{2^{-k+s} + 2^{k+s}})} \leq 4. \]

Since \(f^W(a, b)\) is an integer, this sum can only be 0, 2, or 4 if \(n\) is even, and 1 or 3 if \(n\) is odd. The set of permissible values of \(f^W(a, b)\) is then
\[ f^W(a, b) \in
\begin{cases}
\{0, \pm 2^{\frac{n+1}{2}}\} & \text{if } 2 \nmid n, \\
\{0, \pm 2^{\frac{n}{2}}, \pm 2^{\frac{n+2}{2}}\} & \text{if } 2 \mid n.
\end{cases} \]

We must now demonstrate that \(|K| \leq 4\), which is sufficient to complete the proof.

Note that since \(\alpha\) is a \((2^k - 1)\)-th power, we have \(\alpha^{2^{2k} + 2^k + 1} = 1\). Now suppose that \(L_b(u) = 0\). Then we have the following equations:
\[ (b\alpha)^{-2^k} L_b(u) + b^{1-2^k - 2^{-k}} \alpha L_b(u)^{2^k} + b^{-2^k} L_b(u)^{2^{2k}} = 0, \]
\[ b^{-2^{-s}} L_b(u) + b^{2^{-k-s} - 2^{k-s} - 2^{-s}} \alpha^{2^{-k-s}} L_b(u)^{2^k} + b^{-2^{k-s}} \alpha^{-2^{k-s}} L_b(u)^{2^{-k}} = 0. \]

---

---

### **Page 10**
Substituting the definition of \(L_b(u)\) into equations above and gathering the terms gives
\[ c_1 u^{2^{-s}} + c_2 u^{2^{k-s}} + c_3 u^{2^{-k-s}} = 0, \tag{1} \]
\[ d_1 u^{2^s} + d_2 u^{2^{k+s}} + d_3 u^{2^{-k+s}} = 0, \tag{2} \]
where
\[
\begin{aligned}
c_1 &= (b^{2^{-s} - 2^k} \alpha^{-2^k} + b^{2^{k-s} - 2^{-k}} \alpha^{2^{k-s}}), \\
c_2 &= ((b\alpha)^{2^{-k-s} - 2^k} + b^{2^{k-s} + 1 - 2^{-k} - 2^k} \alpha), \\
c_3 &= (b^{2^{-s} + 1 - 2^k - 2^{-k}} \alpha^{2^{-s+1}} + b^{2^{-k-s} - 2^{-k}}), \\
d_1 &= (b^{1-2^{-s}} + b^{2^{-k-s} + 2^{-k} - 2^{-s} - 2^{k-s}} \alpha^{2^{-k-s+2^{-k}}}), \\
d_2 &= (b^{2^{-k-s} + 2^k - 2^{-s} - 2^{k-s}} \alpha^{2^{-k-s}} + b^{1-2^{k-s}} \alpha^{2^{-k-s+2^{-s+1}}}), \\
d_3 &= (b^{2^k - 2^{-s}} \alpha^{2^k} + b^{2^{-k} - 2^{k-s}} \alpha^{2^{-k-s+2^{-s}}}).
\end{aligned}
\]

First we demonstrate that the coefficients \(c_i, d_j\) in Equations (1) and (2) do not vanish. Suppose that \(c_1 = 0\). We then have
\[ \alpha^{2^{k-s} + 2^k} = b^{-2^{k-s} + 2^{-k} + 2^{-s} - 2^k} \]
and taking \(2^{-k}\)-th power of both sides yields
\[ \alpha^{2^{-s+1}} = b^{(2^{k+s} - 1)(2^{-s} - 2^{-k-s})}. \]

Let \(\alpha = t^{2^k - 1}\), where \(t\) is primitive in \(GF(2^{3k})\). Substituting \(t\) into the previous equation and some rearrangement gives
\[ t^{2^{k-s} - 1} = t^{2^{-s}(1-2^{k+s})} b^{(2^{k+s} - 1)(2^{-s} - 2^{-k-s})}. \]

The multiplicative order of 2 modulo 7 is equal to 3, therefore for any \(r\) we have 7 divides \(2^r - 1\) if and only if \(r\) is divisible by 3. Since \(3 \nmid k - s\), we conclude that \(7 \nmid 2^{k-s} - 1\), therefore the left hand side is not a seventh power, while the right hand side is. We conclude that the coefficient of \(u^{2^{-s}}\) in Equation (1) is not 0 and use the same type of argument to conclude that all the coefficients in Equation (1) are non-zero. A similar argument holds for Equation (2).

We will next combine Equation (1) and Equation (2) to obtain an equation of the form
\[ A u + B u^{2^k} = 0. \]

Raise Equation (1) to the power of \(2^s\), Equation (2) to the power of \(2^{-s}\) and combine the two expressions, cancelling the terms in \(u^{2^{-k}}\) to obtain
\[ A u + B u^{2^k} = 0, \tag{3} \]
where
\[ A = \left( \frac{c_1}{c_3} \right)^{2^s} + \left( \frac{d_1}{d_3} \right)^{2^{-s}} \]
and
\[ B = \left( \frac{c_2}{c_3} \right)^{2^s} + \left( \frac{d_2}{d_3} \right)^{2^{-s}}. \]

For now assume that both \(A, B\) are non-zero.

---

---

### **Page 11**
We obtain the following equalities by applying the appropriate powers of the Frobenius automorphism to Equation (3):
\[ u^{2^{-k+s}} = A^{-2^{-k+s}} B^{2^{-k+s}} u^{2^s}, \]
\[ u^{2^{k-s}} = B^{-2^{-s}} A^{2^{-s}} u^{2^{-s}}. \]

Substituting the two identities above to our expression for \(L_b(u) = 0\) gives
\[ (b + (b\alpha)^2) A^{-2^{-k-s}} B^{2^{-k-s}} u^{2^s} + (b^{2^{-s}} + (b\alpha)^{2^{-k-s}} B^{-2^{-s}} A^{2^{-s}} u^{2^{-s}} = 0. \tag{4} \]

Raising this equation to the power of \(2^s\) gives a polynomial of degree \(2^{2s}\) which is \(GF(2^s)\)-linear. By Corollary 2, the dimension of the kernel of this polynomial over \(GF(2)\) is at most 2, unless the lefthand side of Equation (4) is identically 0. It therefore remains to show that the polynomial in Equation (4) is not identically 0. Assuming that both coefficients are zero, we get
\[ A b^{2^k - s} + (b\alpha)^{2^{-k-s}} B = 0, \]
\[ B b + (b\alpha)^{2^{-k}} A = 0. \]

We combine the equations above to obtain
\[ B b + (b\alpha)^{2^{-k}} b^{2^{k-s}} \alpha^{2^{-k-s}} B = 0. \]

So we have
\[ b^{1-2^{-k} + 2^{k-s} - 2^{-k-s}} = \alpha^{2^{-k-s} + 2^{-k}}. \]
Substituting \(\alpha\) with \(t^{2^k - 1}\), rearranging and factoring the powers gives
\[ b^{(2^{k+s} - 1)(1 - 2^{-k})} t^{1-2^{k+s}} = t^{2^s (2^{k-s} - 1)}. \]

Here we observe that only the left hand side of the above equation is a seventh power, thus obtaining the desired contradiction. We conclude that the size of the kernel \(K\) is less than 4. This finishes the argument.

It finally remains to show that the coefficients \(A, B\) are non-zero. Setting \(A\) to 0 gives rise to the equation
\[ \alpha^{2^{-2s} + 2^{k+s}} = \left( \frac{b^{1-2^{-k+s}} + (b\alpha)^{2^{-k+s}} \alpha^{2^{-k+s}}}{b^{2^{-s} + 2^{-k-s}} + b^{2^{-k} + 2^{-k-s}} \alpha^{2^{-k-s} + 2^{-k}}} \right) \left( \frac{(b\alpha)^{2^{-k-s} + 2^{k-s}} + b^{2^{-k-s} - 2^{-k-s}}}{ (b\alpha)^{2^{-s+1}} + b^{2^{-k} + 2^{k+s}}} \right). \]

Substituting \(\alpha\) with \(t^{2^k - 1}\) and rearranging gives the equation
\[ t^{2^{k-2s+1}(2^k - 1)} = t^{2^{2s - k - 2s}(2^{3s - 1})} R^{2^{2k+2s - 1}} T^{1-2^{2k+2s}}, \]
where
\[ R = b^{2^{-s} + 2^{k-s}} + b^{2^{-k} + 2^{-k-s}} \alpha^{2^{-k-2s} + 2^{-k-s}} \]
and
\[ T = ((b\alpha)^{2^{-k-s} + 2^{k-s}} + b^{2^{-k-s} - 2^{-k-s}}). \]

Reducing the powers of 2 modulo 3 shows that the right hand side of the equation above is a seventh power, while the left hand side is not. We conclude that \(A \neq 0\).

Suppose \(B = 0\), then the only solution of Equation (3) is \(u = 0\). We can therefore assume that both \(A\) and \(B\) are non-zero.

This completes the proof of the theorem for the case when \(f = f_1\). When \(f = f_2\) a similar proof applies. We interchange \(k\) and \(-k\) in all equations and use the fact that in this case 3 divides \(k - s\).

---

---
---

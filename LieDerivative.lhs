% Lie Derivatives
% Dominic Steinitz
% 9th February 2016

---
bibliography: DiffGeom.bib
---

Introduction
============

In proposition 58 Chapter 1 in the excellent book @o1983semi, the author
demonstrates that the Lie derivative of one vector field with respect
to another is the same as the Lie bracket (of the two vector fields)
although he calls the Lie bracket just bracket and does not define the
Lie derivative preferring just to use its definition with giving it a
name. The proof relies on a prior result where he shows a co-ordinate
system at a point $p$ can be given to a vector field $X$ for which
$X_p \neq 0$ so that $X = \frac{\partial}{\partial x_1}$.

Here's a proof seems clearer (to me at any rate) and avoids having to
distinguish the case wehere the vector field is zero or
non-zero. These
[notes](https://people.maths.ox.ac.uk/hitchin/hitchinnotes/manifolds2012.pdf)
give a similar proof but, strangely for undergraduate level, elide
some of the details.

A Few Definitions
=================

Let $\phi: M \longrightarrow N$ be a smooth mapping and let $A$ be a
$0,s$ tensor with $s \geq 0$ then define the **pullback** of $A$ by $\phi$
to be

$$
\phi^*A(v_1,\ldots,v_s) = A(\mathrm{d}\phi v_1,\ldots,\mathrm{d}\phi v_s)
$$

For a $(0,0)$ tensor $f \in {\mathscr{F}}(N)$ the **pullback** is
defined to be $\phi^*(f) = f \circ \phi \in {\mathscr{F}}(M)$.

Standard manipulations show that $\phi^*A$ is a smooth (covariant)
tensor field and that $\phi^*$ is $\mathbb{R}$-linear and that
$\phi^*(A\otimes B) = \phi^*A \otimes \phi^*B$.

Let $F : M \longrightarrow N$ be a _diffeomorphism_ and $Y$ a vector
field on $N$ we define the **pullback** of this field to be

$$
(F^*{Y})_x = D(F^{-1})_{F(x)}(Y_{F(x)})
$$

Note that the pullback of a vector field only exists in the case where
$F$ is a diffeomorphism; in contradistinction, in the case of
pullbacks of purely covariant tensors, the pullback always exists.

For the proof below, we only need the pullback of functions and vector
fields; the pullback for $(0,s)$ tensors with $s \geq 1$ is purely to
give a bit of context.

From @o1983semi Chapter 1 Definition 20, let $\phi: M \rightarrow N$ be
a smooth mapping. Vector fields $X$ on $M$ and $Y$ on $N$ are
$F$-**related** written $X \underset{F}{\sim} Y$ if and only if
$dF({X}_p) = Y_{Fp}$.

The Alternative Proof
=====================

By Lemma 21 Chapter 1 of @o1983semi, $X$ and $Y$ are $F$-related if
and only if $X(f \circ F) = Yf \circ F$.

Recalling that $dF(X_p)(f) = X_p(F \circ f)$ and since

$$
dF_x d(F^{-1})_{Fx}(X_{Fx}) = X_{Fx}
$$

we see that the fields $F^*{Y}$ and $Y$ are $F$-related: $F^*{Y}_x
\underset{F}{\sim} Y_{Fx}$. Thus we can apply the Lemma.

$$
(F^*{Y})(f \circ F) = (F^*{Y})(F^*{f}) =  Yf \circ F = F^*(Yf)
$$

Although we don't need this, we can express the immediately above
equivalence in a way similar to the rule for covariant tensors

$$
(F^*{Y})(f \otimes F) = (F^*{Y})\otimes(F^*{f})
$$

First let's calculate the Lie derivative of a function $f$ with
respect to a vector field $X$ where $\phi_t$ is its flow

$$
\begin{aligned}
L_X f &\triangleq \lim_{t \rightarrow 0} \frac{\phi_t^*(f) - f}{t} \\
      &=          \lim_{t \rightarrow 0} \frac{f \circ \phi_t - f \circ \phi_0}{t} \\
      &=          \lim_{t \rightarrow 0} \frac{f \circ \phi (t,x) - f \circ \phi (0, x)}{t} \\
      &=          (\phi_x)'_0(f) \\
      &=          X_x(f) \\
      &=          (Xf)_x
\end{aligned}
$$

Analogously defining the Lie derivative of $Y$ with respect to $X$

$$
(L_X Y) \triangleq \frac{(\phi_t^*{Y}) - Y}{t}f
$$

we have

$$
\begin{aligned}
L_X(Yf) &= \lim_{t \rightarrow 0} \frac{\phi_t^*(Yf) - Yf}{t} \\
        &= \lim_{t \rightarrow 0} \frac{(\phi_t^*{Y})(\phi_t^*{f}) - Yf}{t} \\
        &= \lim_{t \rightarrow 0}
           \frac{(\phi_t^*{Y})(\phi_t^*{f}) - (\phi_t^*{Y})f + (\phi_t^*{Y})f - Yf}{t} \\
        &= \lim_{t \rightarrow 0}
           \Bigg(
           (\phi_t^*{Y})\frac{\phi_t^*{f} - f}{t} +
           \frac{(\phi_t^*{Y}) - Y}{t}f
           \Bigg) \\
        &= Y(L_X f) + (L_X Y)f
\end{aligned}
$$

Since $L_X f = Xf$ we have

$$
X(Yf) = Y(Xf) + (L_X Y)f
$$

Thus 

$$
(L_X Y)f  = Y(Xf) - X(Yf) = [X,Y]f
$$

as required.

Bibliography
============

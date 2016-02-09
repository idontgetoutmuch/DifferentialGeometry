% Lie Derivatives
% Dominic Steinitz
% 9th February 2016

---
bibliography: DiffGeom.bib
---

Proposition 58 in Barrett O'Neill's excellent book "Semi-Riemannian
Geometry with Applications to Relativity" (@o1983semi) demonstrates
that the Lie derivative of one vector field with respect to another is
the same as the Lie bracket (of the two vector fields) although he
calls the Lie bracket just bracket and does not define the Lie
derivative preferring just to use its definition with giving it a
name.

The proof relies on a prior result where he shows a co-ordinate system
at a point $p$ can be given to a vector field $X$ for which $X_p \neq
0$ so that $X = \frac{\partial}{\partial x_1}$.

This proof seems clearer (to me at any rate) and avoids having to
distinguish the case wehere the vector field is zero or non-zero.

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

In the terminolgoy of O'Neill (@o1983semi Defintion 20 Chapter 1), the
fields are $F^{-1}$-related: $F^*{Y}_x \underset{F^{-1}}{\sim}
Y_{Fx}$.

By Lemma 

$$
\begin{aligned}
L_X(Yf) &= \lim_{t \rightarrow 0} \frac{\phi_t^*(Yf) - Yf}{t} \\
        &= \lim_{t \rightarrow 0} \frac{}{}
\end{aligned}
$$

$$
Y(Xf) =
DF_x(\tilde{Y})(Xf) =
DF_x(\tilde{Y})\frac{\partial}{\partial t} f(\phi_t(a))\vert_{t=0}
$$

An alternative proof
====================

Let $\phi_t$ be the flow (FIXME: look in O'Neill) of a vector field
$X$ then

$$
\frac{\partial}{\partial t} f(\phi_t(a))\vert_{t=0} = X_a(f).
$$


$$
\frac{\partial}{\partial t}(f \circ \phi_t) =
$$

$$
M \times \mathbb{R} \longrightarrow^{\phi_t}
M \longrightarrow^{f}
\mathbb{R}
$$


Let

$$
\frac{\mathrm{d}x}{\mathrm{d}t} = sin t
$$

Let $X = \partial / \partial x$ and
$Y = \sin x \partial / \partial x + \cos y 


Bibliography
============

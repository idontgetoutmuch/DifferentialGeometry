% Every Manifold is Paracompact
% Dominic Steinitz
% 7th April 2016

\DeclareMathOperator*{\supp}{\mathrm{supp}}
\DeclareMathOperator*{\interior}{\mathrm{int}}

---
bibliography: DiffGeom.bib
---

Introduction
============

I spotted this
[tweet](https://twitter.com/betanalpha/status/1009714030649454592) in
which the author says "I'm taking a gamble and going to say 'cotangent
bundle' in a talk today. Pray for me."

I don't know how he explained the cotangent bundle but it seems that
it is not well known that one can define the cotangent bundle directly
without reference to the tangent bundle. Or perhaps this is so well
known that very few people write it down.

Let $(M, {\mathcal{O}}, {\mathcal{A}})$ be a manifold and let $f : M
\rightarrow \mathbb{R}$ be smooth.

Let $\phi_\alpha$ be a chart map then $g \triangleq f \circ
\phi_\alpha^{-1} :: \mathbb{R}^n \rightarrow \mathbb{R}$. This clearly
depends on the chart map.

Suppose its differential vanishes at $\phi_\alpha(a)$. That is
$\partial g \, / \, \partial x_i = 0, \, \forall i$.

Now take another chart map $\phi_\beta$ then $h \triangleq f \circ
\phi_\beta^{-1} :: \mathbb{R}^n \rightarrow \mathbb{R}$.

$$
g = f \circ \phi_\alpha^{-1} =
f \circ \phi_\beta^{-1} \circ \phi_\beta \circ \phi_\alpha^{-1} =
h \circ \phi_\beta \circ \phi_\alpha^{-1}
$$

If $\phi_\alpha(a) = (x_1, x_2, \ldots, x_n)$ and $\phi_\beta(a) =
(y_1, y_2, \ldots, y_n)$ then $\phi_\beta \circ \phi_\alpha^{-1}$ is a
smooth map taking $(x_1, x_2, \ldots, x_n)$ to $(y_1, y_2, \ldots,
y_n)$ and we have

$$
g(x_1, x_2, \ldots, x_n) = h(y_1, y_2, \ldots y_n)
$$

By the chain rule in $\mathbb{R}^n$ we have

$$


$$

Bibliography
============

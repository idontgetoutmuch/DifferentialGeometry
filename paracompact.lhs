% Every Manifold is Paracompact
% Dominic Steinitz
% 7th April 2016

\DeclareMathOperator*{\supp}{\mathrm{supp}}

---
bibliography: DiffGeom.bib
---

Introduction
============

In their paper @Betancourt2014, the authors give a corollary which
starts with the phrase "Because the manifold is paracompact\ldots". It
wasn't immediately clear why *the* manifold was paracompact or indeed
what paracompactness meant although it was clearly something like
compactness which means that every cover has a finite sub-cover. One
might further guess that since a manifold is locally Euclidean that
$\mathbb{R}^n$ really ought to be paracompact and that the local
homeomorphisms somehow preserve this.

It turns out that *every* manifold is paracompact and that this is
intimately related to partitions of unity.

Most of what I have written below is taken from some hand-written
anonymous lecture notes I found by chance in the
[DPMMS](https://www.dpmms.cam.ac.uk) library in Cambridge
University. To whomever wrote them: thank you very much.

Limbering Up
============

Let $\{U_i : i \in {\mathcal{I}}\}$ be an open cover of a smooth
manifold $M$. A *partition of unity* on M, subordinate to the cover
$\{U_i : i \in {\mathcal{I}}\}$ is a finite collection of smooth
functions

$$
X_j : M^n \longrightarrow \mathbb{R}_+
$$

where $j = 1, 2, \ldots N$ for some $N$ such that

$$
\sum_{j = 0}^N X_j(x) = 1 \,\mathrm{for all}\, x \in M
$$

and for each $j$ there exists $i(j) \in {\mathcal{I}}$ such that

$$
\supp{X_j} \subset U_{i(j)}
$$

We don't yet know partitions of unity exist.

First define

$$
f(t) \triangleq
\begin{cases}
0            & \text{if } t \leq 0 \\
\exp{(-1/t)} & \text{if } t > 0 \\
\end{cases}
$$

Techniques of classical analysis easily show that $f$ is smooth ($t=0$
is the only point that might be in doubt and it can be checked from
first principles that $f^{(n)}(0) = 0$ for all $n$).

Next define

$$
\begin{aligned}
g(t) &\triangleq \frac{f(t)}{f(t) + f(1 - t)} \\
h(t) &\triangleq g(t + 2)g(2 - t)
\end{aligned}
$$

```{.dia height='600'}
dia = image (DImage (ImageRef "diagrams/f.png") 600 600 (translationX 0.0))
```

```{.dia height='600'}
dia = image (DImage (ImageRef "diagrams/g.png") 600 600 (translationX 0.0))
```

```{.dia height='600'}
dia = image (DImage (ImageRef "diagrams/h.png") 600 600 (translationX 0.0))
```

Finally we can define $F: \mathbb{R}^n \rightarrow \mathbb{R}$ by
$F(x) = h(\|x\|)$. This has the properties

* $F(x) = 1$ if $\|x\| \leq 1$
* $0 \leq F(x) \leq 1$
* $F(x) = 0$ if $\|x\| > 2$

Now take a point $p \in M$ centred in a chart $(U_p, \phi_p)$ so that,
without loss of generality, $B(0,3) \subseteq \phi_p(U_p)$ (we can
always choose $r_p$ so that the open ball $B(0,3r_p) \subseteq
\phi'_p(U_p)$ and then define another chart $(U_p, \phi_p)$ with
$\phi_p(x) = \phi'(x)/\|x\|$).

Define the images of the open and closed balls of radius $1$ and $2$
respectively

$$
\begin{aligned}
V_p &= \phi_p^{-1}(B(0,1)) \\
W_p &= \phi_p^{-1}\big(\overline{B(0,2)}\big) \\
\end{aligned}
$$

and further define

$$
\psi_p(y) \triangleq
\begin{cases}
F(\phi_p(y)) & \text{if } y \in U_p\\
0            & \text{otherwise} \\
\end{cases}
$$

Then $\psi_p$ is smooth and its support lies in $W_p \subset U_p$.

By compactness, the open cover $\{V_p : p \in M\}$ has a finite
subcover $\{V_{p_1},\ldots,V_{p_K}\}$. Now define

$$
X_j : M^n \longrightarrow \mathbb{R}_+
$$

by

$$
X_j(y) = \frac{\psi_{p_j}(y)}{\sum_{i=1}^K \psi_{p_i}(y)}
$$




Further let

$$
V_p = \phi_p^{-1}(\{z \in \mathbb{R}^n : \|z\| < 2\}) = \psi_p^{-1}(0,\infty)
$$

Bibliography
============

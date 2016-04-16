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

In their paper @Betancourt2014, the authors give a corollary which
starts with the phrase "Because the manifold is paracompact\ldots". It
wasn't immediately clear why *the* manifold was paracompact or indeed
what paracompactness meant although it was clearly something like
compactness which means that every cover has a finite sub-cover.

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
$\phi_p(x) = \phi'_p(x)/\|x\|$).

Define the images of the open and closed balls of radius $1$ and $2$
respectively

$$
\begin{aligned}
V_p &= \phi_p^{-1}(B(0,1)) \\
W_p &= \phi_p^{-1}\big(\overline{B(0,2)}\big) \\
\end{aligned}
$$

and further define bump functions

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

Then $X_j$ is smooth, $\supp{X_j} = \supp{\psi_{p_j}} \subset U_{p_j}$
and $\sum_{j=1}^K X_j(y) = 1$. Thus $\{X_j\}$ is the required
partition of unity.

Paracompactness
===============

Because $M$ is a manifold, it has a countable basis $\{A_i\}_{i \in
\mathbb{N}}$ and for any point $p$, there must exist $A_i \subset V_p$
with $p \in A_i$. Choose one of these and call it $V_{p_i}$. This
gives a countable cover of $M$ by such sets.

Now define

$$
L_1 = W_{p_1} \subset V_{p_1} \cup V_{p_2} \cup \ldots \cup V_{p_{i(2)}}
$$

where, since $L_1$ is compact, $V_{p_2}, \ldots, V_{p_{i(2)}}$ is a
finite subcover.

And further define

$$
L_n = W_{p_1} \cup W_{p_2} \cup \ldots \cup W_{p_{i(n)}}
      \subset
      V_{p_1} \cup V_{p_2} \cup \ldots \cup V_{p_{i(n+1)}}
$$

where again, since $L_n$ is compact, $V_{p_{i(n)+1}}, \ldots,
V_{p_{i(n+1)}}$ is a finite subcover.

Now define

$$
\begin{aligned}
K_n &= L_n \setminus \interior{L_{n-1}} \\
U_n &= \interior(L_{n+1}) \setminus L_n
\end{aligned}
$$

Then $K_n$ is compact, $U_n$ is open and $K_n \subset
U_n$. Furthermore, $\bigcup_{n \in \mathbb{N}} K_n = M$ and $U_n$ only
intersects with $U_{n-1}$ and $U_{n+1}$.

Given any open cover ${\mathcal{O}}$ of $M$, each $K_n$ can be covered
by a finite number of open sets in $U_n$ contained in some member of
${\mathcal{O}}$. Thus every point in $K_n$ can be covered by at most a
finite number of sets from $U_{n-1}, U_n$ and $U_{n+1}$ and which are
contained in some member of${\mathcal{O}}$. This is a locally finite
refinement of ${\mathcal{O}}$ and which is precisely the definition of
*paracompactness*.

To produce a partition of unity we define bump functions $\psi_j$ as
above on this locally finite cover and note that locally finite
implies that $\sum_j \psi_j$ is well defined. Again, as above, define

$$
X_j(y) = \frac{\psi_{j}(y)}{\sum_{i=1} \psi_{i}(y)}
$$

to get the required result.

Bibliography
============

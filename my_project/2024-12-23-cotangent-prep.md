# Introduction

Suppose we have smooth $f : M \longrightarrow \mathbb{R}$. Then we can
define the derivative of $f$ to be $0$ at a point $a$ if for a chart
$\phi_\alpha$ then $D(f \phi_\alpha^{-1}) = 0$. But this may not be
well-defined. Suppose $\phi_\beta$ is another chart, setting
$g \triangleq f \phi_\alpha^{-1}$ and $g \triangleq f \phi_\beta^{-1}$
then

$$
g=f \phi_\alpha^{-1}=f \phi_\beta^{-1} \phi_\beta \phi_\alpha^{-1}=h \phi_\beta \phi_\alpha^{-1}
$$

and now we are in the familiar world of calculus on $\mathbb{R}^n$.

On one definition of an atlas, $\phi_\beta \phi_\alpha^{-1}$ is smooth
with a smooth inverse. By the chain rule for calculus we have

$$
\frac{\partial g}{\partial x_i}=\sum_j \frac{\partial h}{\partial y_j}(y(x)) \frac{\partial y_j}{\partial x_i}(x)
$$

$\frac{\partial y_j}{\partial x_i}(x)$ has full rank so we can conclude
that

$$
D(f\phi_\alpha^{-1}) = 0 \iff D(f\phi_\beta^{-1}) = 0
$$

This post captures my experiences using Lean to formalise this. The user
of Lean is not just faced with learning Lean the language and also its
proof system via so-called tactics but also learning how the Mathlib
authors decided to define manifolds and other necessary mathematical
structures. The design decisions of the latter are captured in the
Mathlib documentation.

In a nutshell, the authors wanted to be able to capture manifolds with
boundary as well as those without. It took me some time to work out how
to restrict my proof manifolds without boundary (the ones undergraduates
first encounter).

# Transition Maps are Smooth

Mathlib has its own way of defining manifolds which I won\'t elaborate
here but this does not use the fact that transition maps are smooth with
a smooth inverse. So let\'s state and prove that the transition maps are
smooth and have a smooth inverse.

1.  Charts in Mathlib are defined as partial homeomorphisms, that is,
    structures that have a source and a target and a continuous function
    from the source to the target with a continuous inverse. These are
    homeomorphisms from $M$ to $m$ dimensional Euclidean space (a
    manifold is locally Euclidean).
2.  To make the charts smooth we declare them as elements of the maximal
    (presumably smooth) atlas on $M$.
3.  Adding `.symm`{.verbatim} as a suffix gives the inverse of the
    homeomorphism and `.trans`{.verbatim} allows a partial homeomorphism
    to composed with another taking into account the sources and
    targets.
4.  `h2`{.verbatim} and `h3`{.verbatim} state that $\phi_\beta$ and the
    inverse of $\phi_\alpha$ are smooth.
5.  After a bit of manipulation, we can apply the chain rule to deduce
    `h6`{.verbatim} that the transition map is smooth.
6.  And finally a bit more manipulation proves the theorem.

The only tactic used is `rw`{.verbatim} which re-writes terms if it
finds a match. The rest of the proof is finding existing theorems. I
found [moogle](https://www.moogle.ai/) very useful for this.

``` lean4
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.AnalyticManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib

open Manifold

open SmoothManifoldWithCorners

theorem contMDiffAt_chart_transition
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)
  (x : M)  (hx : x ∈  φ_α.source ∩ φ_β.source) :
   ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) := by
    have h1 : (φ_α.symm.trans φ_β) = φ_β ∘ φ_α.symm :=
      PartialHomeomorph.coe_trans φ_α.symm φ_β
    have h2 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_β x :=
      contMDiffAt_of_mem_maximalAtlas hΦ_Β hx.2
    have h3 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_α.symm (φ_α x) :=
      contMDiffAt_symm_of_mem_maximalAtlas hΦ_Α (PartialHomeomorph.map_source φ_α hx.1)
    have h4 : φ_α.symm (φ_α x) = x := PartialHomeomorph.left_inv φ_α hx.1
    have h5 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_β (φ_α.symm (φ_α x)) := by
      rw [h4]
      exact h2
    have h6 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_β ∘ φ_α.symm) (φ_α x) :=
      ContMDiffAt.comp (I' := 𝓡 m) (φ_α x) h5 h3
    have h7 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) := by
      rw [h1]
      exact h6
    exact h7
```

We want the transition maps be smooth as functions on $\mathbb{R}^n$:

``` lean4
theorem contDiffAt_chart_transition
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)
  (x : M) (hx : x ∈ φ_α.source ∩ φ_β.source) :
    ContDiffAt ℝ (⊤ : ENat) (φ_α.symm.trans φ_β) (φ_α x) := by
    have h_contMDiff : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) :=
     contMDiffAt_chart_transition m φ_α hΦ_Α φ_β hΦ_Β x hx
    exact contMDiffAt_iff_contDiffAt.mp h_contMDiff
```

I can\'t help feeling that this is a bit circular but I believe (but
will not prove) that we can go from the fact the transition maps are
smooth (in the ordinary sense) to define a topology on the space from
which the co-ordinate functions map and then that these functions are
homeomorpisms (smooth even but then we have define what it means for a
function to be smooth). It would make a good exercise.

Even before that we want the fact that two functions have the same
derivative at a point if they agree on an open set containing that
point.

``` lean4
theorem mfderivWithin_congr_of_eq_on_open
  {m n : ℕ} {M N : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SmoothManifoldWithCorners (𝓡 n) N]
  (f g : M → N) (s : Set M)
  (ho : IsOpen s)
  (he : ∀ x ∈ s, f x = g x) :
  ∀ x ∈ s, mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x := by
    intros x hy
    exact mfderivWithin_congr (IsOpen.uniqueMDiffWithinAt ho hy) he (he x hy)
```

This is the same as writing a term but the tactics above seem to be
preferred and we will stick to lean traditions from now on bearing in
mind that they can always be re-written as term (well they are a term
really).

``` lean4
theorem mfderivWithin_congr_of_eq_on_open_as_term
  {m n : ℕ} {M N : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SmoothManifoldWithCorners (𝓡 n) N]
  (f g : M → N) (s : Set M)
  (ho : IsOpen s)
  (he : ∀ x ∈ s, f x = g x) :
  ∀ x ∈ s, mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x :=
  λ z hz =>
    mfderivWithin_congr (IsOpen.uniqueMDiffWithinAt ho hz) he (he z hz)
```

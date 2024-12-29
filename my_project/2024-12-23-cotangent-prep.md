---
date: 2024-12-23
title: Vanishing Derivatives
---

Suppose we have smooth $f : M \longrightarrow \mathbb{R}$. Then we can
define the derivative of $f$ to be $0$ at a point $a$ if for a chart
$\phi_\alpha$ then $D(f \phi_\alpha^{-1}) = 0$. But this may not
be well-defined. Suppose $\phi_\beta$ is another chart, setting $g \triangleq f \phi_\alpha^{-1}$ and $g \triangleq f \phi_\beta^{-1}$ then

$$
g=f \phi_\alpha^{-1}=f \phi_\beta^{-1} \phi_\beta \phi_\alpha^{-1}=h \phi_\beta \phi_\alpha^{-1}
$$

and now we are in the familiar world of calculus on $\mathbb{R}^n$.

On one definition of an atlas, $\phi_\beta \phi_\alpha^{-1}$ is smooth
with a smooth inverse. By the chain rule for calculus we have

$$
\frac{\partial g}{\partial x_i}=\sum_j \frac{\partial h}{\partial y_j}(y(x)) \frac{\partial y_j}{\partial x_i}(x)
$$

# Transition Maps are Smooth

$$
g=f \phi_\alpha^{-1}=f \phi_\beta^{-1} \phi_\beta \phi_\alpha^{-1}=h \phi_\beta \phi_\alpha^{-1}
$$

```lean4
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.AnalyticManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

open Manifold

open SmoothManifoldWithCorners

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

This is the same as writing a term but the tactics above seem to be preferred.

```lean4
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

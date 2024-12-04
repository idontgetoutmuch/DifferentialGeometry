import Mathlib

import Mathlib.Geometry.Manifold.MFDeriv.Basic

open Manifold

#check mfderivWithin_congr_set

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (f : M → ℝ)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
  (x : M) (hx : x ∈ φ_α.source ∩ φ_β.source) : true := by

    let g : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_α.invFun
    let h : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_β.invFun

    -- I have a proof for this
    have h1 : ∀ x ∈ φ_α.source ∩ φ_β.source, g (φ_α.toFun x) = (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun x) := by
      sorry

    -- I would like a proof for this
    have h2 : ∀ x ∈ φ_α.source ∩ φ_β.source,
              fderiv ℝ g (φ_α.toFun x) = fderiv ℝ (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun x) := by
      -- have h2a : mfderivWithin_congr_set
      sorry

    sorry

variable
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]

variable
  (n : ℕ) {N : Type*}
  [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SmoothManifoldWithCorners (𝓡 n) N]

variable
  (f : M -> N)

variable
  (s : Set M)

variable
  (x : M)

#check mfderivWithin (𝓡 m) (𝓡 n) f s x
#check mfderivWithin_congr
#check UniqueMDiffWithinAt

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
    have hx : f x = g x := he x hy
    have h1 : UniqueMDiffWithinAt (𝓡 m) s x := IsOpen.uniqueMDiffWithinAt ho hy
    have h2 : mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x :=
    mfderivWithin_congr h1 he hx
    exact h2

#check mfderivWithin_congr_of_eq_on_open
  (id : EuclideanSpace ℝ (Fin 1) -> EuclideanSpace ℝ (Fin 1))
  (id : EuclideanSpace ℝ (Fin 1) -> EuclideanSpace ℝ (Fin 1))
  (∅ :  Set (EuclideanSpace ℝ (Fin 1))) sorry sorry

example
  (m : ℕ) {M : Type*}
  (n : ℕ) {N : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SmoothManifoldWithCorners (𝓡 n) N]
  (f : M → N) (g : M -> N) (s : Set M)
  (ho : IsOpen s)
  (he : ∀ x ∈ s, f x = g x) :
     ∀ x ∈ s, mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x := by
     intros x hy
     have hx : f x = g x := he x hy
     have h1 : UniqueMDiffWithinAt (𝓡 m) s x := IsOpen.uniqueMDiffWithinAt ho hy
     have h2 : mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x :=
      mfderivWithin_congr h1 he hx
     exact h2

#synth TopologicalSpace (EuclideanSpace ℝ (Fin 1))
#check ChartedSpace

instance : ChartedSpace ℝ (EuclideanSpace ℝ (Fin 1)) where
  atlas := sorry
  chartAt := sorry
  mem_chart_source := sorry
  chart_mem_atlas := sorry

example : ChartedSpace ℝ (EuclideanSpace ℝ (Fin 1)) ℝ := by
  apply_instance

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) ℝ

example (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℝ) (s : Set (EuclideanSpace ℝ (Fin n)))
  (ho : IsOpen s) (he : ∀ x ∈ s, f x = g x) :
  ∀ x ∈ s, mfderivWithin (𝓡 n) (𝓡 1) f s x = mfderivWithin (𝓡 n) (𝓡 1) g s x := by
    intros x hy
    have hx : f x = g x := he x hy
    have h1 : UniqueMDiffWithinAt (𝓡 n) s x := IsOpen.uniqueMDiffWithinAt ho hy
    have h2 : mfderivWithin (𝓡 n) (𝓡 1) f s x = mfderivWithin (𝓡 n) (𝓡 1) g s x :=
      mfderivWithin_congr h1 he hx
    exact h2

example (f g : ℝ → ℝ) (s : Set ℝ)
  (ho : IsOpen s) (he : ∀ x ∈ s, f x = g x) :
  ∀ x ∈ s, mfderivWithin (𝓡 1) (𝓡 1) f s x = mfderivWithin (𝓡 1) (𝓡 1) g s x :=
by
  intros x hy
  have hx : f x = g x := he x hy
  have h1 : UniqueMDiffWithinAt (𝓡 1) s x := IsOpen.uniqueMDiffWithinAt ho hy
  have h2 : mfderivWithin (𝓡 1) (𝓡 1) f s x = mfderivWithin (𝓡 1) (𝓡 1) g s x :=
    mfderivWithin_congr h1 he hx
  exact h2

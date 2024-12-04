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

#check mfderivWithin

example
  (m : ℕ) {M : Type*}
  (n : ℕ) {N : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [SmoothManifoldWithCorners (𝓡 n) N]
  (f : M → M') (g : M -> M') (s : Set M) (hs : ∀ x ∈ s, f x = g x) :
     ∀ x ∈ s, mfderivWithin f s x = mfderivWithin g s x := sorry 

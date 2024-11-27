import Mathlib

open Manifold

variable
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]

#check atlas
#check atlas M

#check deriv
#synth DivInvMonoid ℚ
#synth NormedSpace ℝ (EuclideanSpace ℝ (Fin 2))

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
  (g : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_α.invFun)
  (h : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_β.invFun)

  (Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    λ x => fderiv ℝ g (φ_α.toFun x))

  (Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    λ x => fderiv ℝ h (φ_β.toFun x))
   : true := by
  -- ∀ x ∈ φ_α.source ∩ φ_β.source, (∀ v, Dg x v = 0) <-> (∀ v, Dh x v = 0) := by

  have h2 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            g x = (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by sorry
  have h3 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            g x = (h ∘ (φ_α.symm.trans φ_β).toFun) x := by sorry
  have h1 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            fderiv ℝ g x = fderiv ℝ (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by
    intros x hx
    simp [h2 x hx]
    sorry
  have h4 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            fderiv ℝ g x = fderiv ℝ (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by
    intros x hx
    simp [h2 x hx]
    sorry
  trivial

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (f : M → ℝ)
  (smooth_f : Smooth (𝓡 m) 𝓘(ℝ, ℝ) f)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ atlas (EuclideanSpace ℝ (Fin m)) M)

  (g : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_α.invFun)
  (h : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_β.invFun)

  (Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    λ x => fderiv ℝ g (φ_α.toFun x))

  (Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    λ x => fderiv ℝ h (φ_β.toFun x))

   (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source)

      : (∀ v, Dg x v = 0) <-> (∀ v, Dh x v = 0) := by

  have bah : fderiv ℝ (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α x) =
             (fderiv ℝ h ((φ_α.symm.trans φ_β).toFun (φ_α x))).comp (fderiv ℝ (φ_α.symm.trans φ_β).toFun (φ_α x)) := by


    have smooth_h : SmoothAt (𝓡 m) 𝓘(ℝ, ℝ) h ((φ_α.symm.trans φ_β).toFun (φ_α x)) := by
      have bar : SmoothAt (𝓡 m) 𝓘(ℝ, ℝ) f (φ_β.invFun (φ_β x)) := sorry
      have baz : SmoothAt (𝓡 m) (𝓡 m) φ_β.invFun (φ_β x) := sorry
      have foo : SmoothAt (𝓡 m) 𝓘(ℝ, ℝ) (f ∘ φ_β.invFun) (φ_β x) := SmoothAt.comp (φ_β x) bar baz
      sorry

    have hg : DifferentiableAt ℝ h ((φ_α.symm.trans φ_β).toFun (φ_α x)) := sorry
    have hf : DifferentiableAt ℝ (φ_α.symm.trans φ_β).toFun (φ_α x) := sorry
    exact fderiv.comp (φ_α x) hg hf

  sorry

#check λ (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) =>
  Set.mem_image (φ_α.invFun ∘ φ_α.toFun) (φ_α.source ∩ φ_β.source)

#min_imports

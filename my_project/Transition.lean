import Mathlib

open scoped Manifold
open SmoothManifoldWithCorners

example (m : ℕ) {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [SmoothManifoldWithCorners (𝓡 m) M]
    (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
    (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
    (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
    (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)
    (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
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
  have h7 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_β ∘ φ_α.symm) (φ_α x) :=
   ContMDiffAt.comp (I' := 𝓡 m) (φ_α x) h5 h3
  have h8 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) := by
    rw [h1]
    exact h7
  exact h8
  -- simp only [PartialHomeomorph.coe_trans]
  -- apply ContMDiffAt.comp (I' := 𝓡 m)
  -- · apply contMDiffAt_of_mem_maximalAtlas hΦ_Β
  --   simpa [hx.1] using hx.2
  -- · apply contMDiffAt_symm_of_mem_maximalAtlas hΦ_Α
  --   exact PartialHomeomorph.map_source φ_α hx.1

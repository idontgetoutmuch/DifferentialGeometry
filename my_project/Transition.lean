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
  simp only [PartialHomeomorph.coe_trans]
  sorry
  -- show _
  -- apply ContMDiffAt.comp (I' := 𝓡 m)
  -- · apply contMDiffAt_of_mem_maximalAtlas hΦ_Β
  --   simpa [hx.1] using hx.2
  -- · apply contMDiffAt_symm_of_mem_maximalAtlas hΦ_Α
  --   exact PartialHomeomorph.map_source φ_α hx.1

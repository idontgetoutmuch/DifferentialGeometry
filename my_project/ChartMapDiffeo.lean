import Mathlib
import Mathlib.Topology.ContinuousOn
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

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
    have hx : f x = g x := he x hy
    have h1 : UniqueMDiffWithinAt (𝓡 m) s x := IsOpen.uniqueMDiffWithinAt ho hy
    have h2 : mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x :=
    mfderivWithin_congr h1 he hx
    exact h2

theorem h1
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
    have h7 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_β ∘ φ_α.symm) (φ_α x) :=
      ContMDiffAt.comp (I' := 𝓡 m) (φ_α x) h5 h3
    have h8 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) := by
      rw [h1]
      exact h7
    exact h8

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :

  let Dαβ : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    λ x => mfderiv (𝓡 m) (𝓡 m) ((φ_α.symm.trans φ_β).toFun) (φ_α.toFun x)

  let Dβα : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    λ x => mfderiv (𝓡 m) (𝓡 m) ((φ_β.symm.trans φ_α).toFun) (φ_β.toFun x)

  HasMFDerivAt (𝓡 m) (𝓡 m)
   (↑(φ_β.symm ≫ₕ φ_α) ∘ ↑(φ_α.symm ≫ₕ φ_β)) (φ_α x) ((Dβα x).comp (Dαβ x)) := by

  let Dαβ : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    λ x => mfderiv (𝓡 m) (𝓡 m) ((φ_α.symm.trans φ_β).toFun) (φ_α.toFun x)

  let Dβα : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    λ x => mfderiv (𝓡 m) (𝓡 m) ((φ_β.symm.trans φ_α).toFun) (φ_β.toFun x)

  have h2 : MDifferentiableAt (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β) (φ_α x) :=
   ContMDiffAt.mdifferentiableAt (h1 m φ_α hΦ_Α φ_β hΦ_Β x hx)  le_top

  have h3 : HasMFDerivAt (𝓡 m) (𝓡 m)  (φ_α.symm.trans φ_β) (φ_α x) (Dαβ x) :=
    MDifferentiableAt.hasMFDerivAt h2

  have h4 : MDifferentiableAt (𝓡 m) (𝓡 m) (φ_β.symm.trans φ_α) (φ_β x) := by
   have h41 : x ∈ φ_β.source ∩ φ_α.source := by
     rw [Set.inter_comm]
     assumption
   exact ContMDiffAt.mdifferentiableAt (h1 m φ_β hΦ_Β φ_α hΦ_Α x h41) le_top

  have h5 : HasMFDerivAt (𝓡 m) (𝓡 m)  (φ_β.symm.trans φ_α) (φ_β x) (Dβα x) :=
    MDifferentiableAt.hasMFDerivAt h4

  have h41 : (φ_α.symm ≫ₕ φ_β) (φ_α x) = (φ_β x) := by
    rw [PartialHomeomorph.trans_apply]
    congr
    exact PartialHomeomorph.left_inv φ_α (Set.mem_of_mem_inter_left hx)

  have h61 : HasMFDerivAt (𝓡 m) (𝓡 m) (φ_β.symm.trans φ_α) ((φ_α.symm ≫ₕ φ_β) (φ_α x)) (Dβα x) := by
    rw [h41]
    exact h5

  have baa : HasMFDerivAt (𝓡 m) (𝓡 m) (↑(φ_β.symm ≫ₕ φ_α) ∘ ↑(φ_α.symm ≫ₕ φ_β)) (φ_α x) ((Dβα x).comp (Dαβ x)) := by
    apply HasMFDerivAt.comp (φ_α x) h61 h3

  have h_inv1 : ∀ x ∈ φ_α.source ∩ φ_β.source,
  ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x) = (φ_α x) := by
    intro x hx
    calc ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x) =
        (φ_α (φ_β.symm (φ_β (φ_α.symm (φ_α x))))) := by rfl
    _ = (φ_α (φ_β.symm (φ_β x))) := by rw [φ_α.left_inv hx.1]
    _ = (φ_α x) := by rw [φ_β.left_inv hx.2]

  have h_inv2 : ∀ x ∈ ↑φ_α.toPartialEquiv '' (φ_α.source ∩ φ_β.source),
    ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) x = id x := by
    intro x hx
    obtain ⟨x₀, hx₀, hfx₀⟩ := (Set.mem_image ↑φ_α.toPartialEquiv (φ_α.source ∩ φ_β.source) x).mp hx
    have h := h_inv1 x₀ hx₀
    rw [←hfx₀]
    exact h

  have h2o : IsOpen (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) := by
    have ho : IsOpen (φ_α.source ∩ φ_β.source) := by
      have ho1 : IsOpen φ_α.source := φ_α.open_source
      have ho2 : IsOpen φ_β.source := φ_β.open_source
      exact IsOpen.and ho1 ho2
    have hs : φ_α.source ∩ φ_β.source ⊆  φ_α.source := inf_le_left
    have h2 : φ_α.toFun = φ_α := φ_α.toFun_eq_coe
    rw [h2]
    have h1 := φ_α.isOpen_image_iff_of_subset_source hs
    rw [h1]
    exact ho

  have h6 : ∀ x ∈ φ_α.toFun '' (φ_α.source ∩ φ_β.source),
    mfderivWithin (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) x =
    mfderivWithin (𝓡 m) (𝓡 m) id (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) x :=
      mfderivWithin_congr_of_eq_on_open ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) id (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) h2o h_inv2

  let EuclideanSpace_id : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearMap.id

  have h7 : φ_α x ∈ ↑φ_α.toPartialEquiv '' (φ_α.source ∩ φ_β.source) := by
      exact ⟨x, hx, rfl⟩

  have h8 : mfderivWithin (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) (φ_α x) =
              mfderivWithin (𝓡 m) (𝓡 m) id (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) (φ_α x) := by
              apply h6 (φ_α x) h7

  have ha : MDifferentiableAt (𝓡 m) (𝓡 m) (↑(φ_β.symm ≫ₕ φ_α) ∘ ↑(φ_α.symm ≫ₕ φ_β)) (φ_α x) := by
    sorry

  have h9 : true := by
    have h1 : HasMFDerivAt (𝓡 m) (𝓡 m) (↑(φ_β.symm ≫ₕ φ_α) ∘ ↑(φ_α.symm ≫ₕ φ_β)) (φ_α x)
              (mfderiv (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x)) := by
                apply MDifferentiableAt.hasMFDerivAt ha
    sorry

  exact baa

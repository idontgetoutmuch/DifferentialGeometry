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
    exact mfderivWithin_congr (IsOpen.uniqueMDiffWithinAt ho hy) he (he x hy)

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
    have h7 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_β ∘ φ_α.symm) (φ_α x) :=
      ContMDiffAt.comp (I' := 𝓡 m) (φ_α x) h5 h3
    have h8 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) := by
      rw [h1]
      exact h7
    exact h8

theorem h2o
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) :
   IsOpen (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) := by
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

noncomputable def Dab
  (m : ℕ)
  {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (x : M) :
  (EuclideanSpace ℝ (Fin m)) →L[ℝ] (EuclideanSpace ℝ (Fin m)) :=
  mfderiv (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β).toFun (φ_α.toFun x)

theorem inverse_transition_of_transition
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :

  .id _ _ = (Dab m φ_β φ_α x) ∘L (Dab m φ_α φ_β x) := by

  let Dαβ := Dab m φ_α φ_β
  let Dβα := Dab m φ_β φ_α
  let s := (φ_α.toFun '' (φ_α.source ∩ φ_β.source))

  have h1 : HasMFDerivAt (𝓡 m) (𝓡 m)  (φ_α.symm.trans φ_β) (φ_α x) (Dαβ x) := by
    apply MDifferentiableAt.hasMFDerivAt (ContMDiffAt.mdifferentiableAt (contMDiffAt_chart_transition m φ_α hΦ_Α φ_β hΦ_Β x hx) le_top)

  have hy : x ∈ φ_β.source ∩ φ_α.source := by
     rw [Set.inter_comm]
     assumption

  have h2 : HasMFDerivAt (𝓡 m) (𝓡 m)  (φ_β.symm.trans φ_α) (φ_β x) (Dβα x) :=
    MDifferentiableAt.hasMFDerivAt ( ContMDiffAt.mdifferentiableAt (contMDiffAt_chart_transition m φ_β hΦ_Β φ_α hΦ_Α x hy) le_top)

  have h41 : (φ_α.symm ≫ₕ φ_β) (φ_α x) = (φ_β x) := by
    rw [PartialHomeomorph.trans_apply]
    congr
    exact PartialHomeomorph.left_inv φ_α (Set.mem_of_mem_inter_left hx)

  have h61 : HasMFDerivAt (𝓡 m) (𝓡 m) (φ_β.symm.trans φ_α) ((φ_α.symm ≫ₕ φ_β) (φ_α x)) (Dβα x) := by
    rw [h41]
    exact h2

  have baa : HasMFDerivAt (𝓡 m) (𝓡 m) (↑(φ_β.symm ≫ₕ φ_α) ∘ ↑(φ_α.symm ≫ₕ φ_β)) (φ_α x) ((Dβα x).comp (Dαβ x)) := by
    apply HasMFDerivAt.comp (φ_α x) h61 h1

  have h_inv1 : ∀ x ∈ φ_α.source ∩ φ_β.source,
  ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x) = (φ_α x) := by
    intro x hx
    calc ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x) =
        (φ_α (φ_β.symm (φ_β (φ_α.symm (φ_α x))))) := by rfl
    _ = (φ_α (φ_β.symm (φ_β x))) := by rw [φ_α.left_inv hx.1]
    _ = (φ_α x) := by rw [φ_β.left_inv hx.2]

  have h_inv2 : ∀ x ∈ s,
    ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) x = id x := by
    intro x hx
    obtain ⟨x₀, hx₀, hfx₀⟩ := (Set.mem_image ↑φ_α.toPartialEquiv (φ_α.source ∩ φ_β.source) x).mp hx
    have h := h_inv1 x₀ hx₀
    rw [←hfx₀]
    exact h

  have h6 : ∀ x ∈ s,
    mfderivWithin (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) s x =
    mfderivWithin (𝓡 m) (𝓡 m) id s x :=
      mfderivWithin_congr_of_eq_on_open ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) id s (h2o m φ_α φ_β) h_inv2

  have h7 : φ_α x ∈ s := by
      exact ⟨x, hx, rfl⟩

  have h8 : mfderivWithin (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) s (φ_α x) =
              mfderivWithin (𝓡 m) (𝓡 m) id s (φ_α x) := by
              apply h6 (φ_α x) h7

  have ha : MDifferentiableAt (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) := by
     apply HasMFDerivAt.mdifferentiableAt baa

  have hc : mfderiv (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) =
            mfderiv (𝓡 m) (𝓡 m) id (φ_α x) := by
            have h1 : mfderivWithin (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) s (φ_α x) =
                      mfderiv (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) := by
                      apply MDifferentiable.mfderivWithin ha (IsOpen.uniqueMDiffWithinAt (h2o m φ_α φ_β) h7)
            have h2 : mfderivWithin (𝓡 m) (𝓡 m) id s (φ_α x) =
                      mfderiv (𝓡 m) (𝓡 m) id (φ_α x) := by
                      apply MDifferentiable.mfderivWithin mdifferentiableAt_id (IsOpen.uniqueMDiffWithinAt (h2o m φ_α φ_β) h7)
            have h3 : mfderivWithin (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) s (φ_α x) =
                      mfderivWithin (𝓡 m) (𝓡 m) id s (φ_α x) := by
                apply h8
            calc
                mfderiv (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) =
                mfderivWithin (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) s (φ_α x) := by
                  apply h1.symm
                _ = mfderivWithin (𝓡 m) (𝓡 m) id s (φ_α x) := by
                  apply h3
                _ = mfderiv (𝓡 m) (𝓡 m) id (φ_α x) := by
                  apply h2

  have he : HasMFDerivAt (𝓡 m) (𝓡 m) (↑(φ_β.symm ≫ₕ φ_α) ∘ ↑(φ_α.symm ≫ₕ φ_β)) (φ_α x)
              (mfderiv (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x)) := by
                apply MDifferentiableAt.hasMFDerivAt ha

  have hd : HasMFDerivAt
            (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x)
            (mfderiv (𝓡 m) (𝓡 m) id (φ_α x)) := by
            rw [<-hc]
            exact he

  have hf : mfderiv (𝓡 m) (𝓡 m) id (φ_α x) = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 m) (φ_α x)) := by
   apply mfderiv_id

  have hg : HasMFDerivAt
            (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x)
            (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 m) (φ_α x))) := by
            rw [<-hf]
            exact hd

  apply hasMFDerivAt_unique hg baa

open ContinuousLinearMap

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)
  (g : EuclideanSpace ℝ (Fin m) -> EuclideanSpace ℝ (Fin 1))
  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source)
  (hαβ : MDifferentiableAt (𝓡 m) (𝓡 m) (φ_β ∘ ↑φ_α.symm) (φ_α x))
  (hg : MDifferentiableAt (𝓡 m) (𝓡 1) g (((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) :
    mfderiv (𝓡 m) (𝓡 1) (g ∘ φ_β ∘ ↑φ_α.symm) (φ_α x) = 0 ->
    mfderiv (𝓡 m) (𝓡 1) g  ((φ_β ∘ ↑φ_α.symm) (φ_α x)) = 0 := by

  intro h

  have h0 : mfderiv (𝓡 m) (𝓡 1) (g ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) = 0 := by
    exact h
  have h1 : mfderiv (𝓡 m) (𝓡 1) (g ∘ (φ_β ∘ ↑φ_α.symm)) (φ_α x) =
            (mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x) := by
     apply mfderiv_comp (φ_α x) hg hαβ
  have h2 : (mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x) = 0 := by
    rw [<-h1]
    exact h
  have h3 : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x)) ∘L (Dab m φ_β φ_α x) =
            0 ∘L (Dab m φ_β φ_α x) := by
    rw [h2]
  have h4 : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x)) ∘L (Dab m φ_β φ_α x) =
            ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) ∘L  ((Dab m φ_α φ_β x) ∘L (Dab m φ_β φ_α x)) := by
    rfl
  have h5 : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) ∘L  ((Dab m φ_α φ_β x)) ∘L (Dab m φ_β φ_α x) =
             ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) ∘L  (.id _ _) := by
     have h1 : (.id _ _) = (Dab m φ_α φ_β x) ∘L (Dab m φ_β φ_α x) := by
       have hy : x ∈ φ_β.source ∩ φ_α.source := by
        rw [Set.inter_comm]
        assumption
       apply inverse_transition_of_transition m φ_β hΦ_Β φ_α hΦ_Α x hy
     rw [<-h1]
     rfl
  have h6 : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) ∘L  (.id _ _) =
            ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) := by
    exact ContinuousLinearMap.comp_id _

  have ha : 0 = mfderiv (𝓡 m) (𝓡 1) (g ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) := by
    exact h0.symm
  have hb : mfderiv (𝓡 m) (𝓡 1) (g ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) =
            (mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x) := by
    exact h1
  have hc : (mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x) = 0 := by
    rw [←hb]
    exact h0
  have hd : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x)) ∘L (Dab m φ_β φ_α x) =
            0 ∘L (Dab m φ_β φ_α x) := by
    exact h3
  have he : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L (Dab m φ_α φ_β x)) ∘L (Dab m φ_β φ_α x) =
            0 := by
    rw [hd]
    rw [ContinuousLinearMap.zero_comp]
  have hf : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L ((Dab m φ_α φ_β x)) ∘L (Dab m φ_β φ_α x)) =
            0 := by
    rw [<-h4]
    exact he
  have hg : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) ∘L  (.id _ _) = 0 := by
    rw [<-h5]
    exact hf
  have hh : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) = 0 := by
    rw [<-h6]
    exact hg
  exact hh

import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.AnalyticManifold
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib

open Manifold

open IsManifold

theorem mfderivWithin_congr_of_eq_on_open
  {m n : ℕ} {M N : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤ M]
  [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ⊤ N]
  (f g : M → N) (s : Set M)
  (ho : IsOpen s)
  (he : ∀ x ∈ s, f x = g x) :
  ∀ x ∈ s, mfderivWithin (𝓡 m) (𝓡 n) f s x = mfderivWithin (𝓡 m) (𝓡 n) g s x := by
    intro z hz
    exact mfderivWithin_congr (IsOpen.uniqueMDiffWithinAt ho hz) he (he z hz)

theorem fderivWithin_congr_of_eq_on_open
  {m n : ℕ}
  (f g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)) (s : Set (EuclideanSpace ℝ (Fin m)))
  (he : ∀ x ∈ s, f x = g x) :
  ∀ x ∈ s, fderivWithin ℝ f s x = fderivWithin ℝ g s x := by
    intro z hz
    exact fderivWithin_congr he (he z hz)

theorem contMDiffAt_chart_transition
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) ⊤ M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) ⊤ M)
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

theorem contDiffAt_chart_transition
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) ⊤  M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) ⊤  M)
  (x : M) (hx : x ∈ φ_α.source ∩ φ_β.source) :
    ContDiffAt ℝ (⊤ : ENat) (φ_α.symm.trans φ_β) (φ_α x) := by
    have h_contMDiff : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) :=
     contMDiffAt_chart_transition m φ_α hΦ_Α φ_β hΦ_Β x hx
    exact contMDiffAt_iff_contDiffAt.mp h_contMDiff

theorem open_image_of_inter_sources
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
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
  [IsManifold (𝓡 m) ⊤  M]
  (φ_α φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (x : M) :
  (EuclideanSpace ℝ (Fin m)) →L[ℝ] (EuclideanSpace ℝ (Fin m)) :=
  mfderiv (𝓡 m) (𝓡 m) (φ_α.symm ≫ₕ φ_β) (φ_α x)

theorem h_equiv (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
    ((↑φ_β ∘ ↑φ_α.symm) (φ_α x)) = (φ_β x) := by
      calc ((↑φ_β ∘ ↑φ_α.symm) (φ_α x)) =
               φ_β (φ_α.symm (φ_α x)) := by rfl
           _ = φ_β x := by rw [φ_α.left_inv hx.1]

theorem inverse_of_chart_transition
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
  ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x) = (φ_α x) := by
    have hy : x ∈ φ_β.source ∩ φ_α.source := by
      rw [Set.inter_comm]
      assumption

    rw [Function.comp_apply]
    rw [h_equiv m φ_α φ_β x hx]
    rw [h_equiv m φ_β φ_α x hy]

variable
(m : ℕ) {M : Type*}
[TopologicalSpace M]

 #check λ (a : (PartialHomeomorph M (EuclideanSpace ℝ (Fin m))))
          (b : (PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))) =>
  a.symm ≫ₕ b

example
(m : ℕ)
(f : PartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)))
(hf : f.symm ≫ₕ f = PartialHomeomorph.ofSet f.source f.open_source)
(hg : f ≫ₕ f.symm = PartialHomeomorph.ofSet f.target f.open_target)
(x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ f.source) :
 .id _ _  = mfderiv (𝓡 m) (𝓡 m) f.symm (f x) ∘L mfderiv (𝓡 m) (𝓡 m) f x := by
  have h1 : HasMFDerivAt (𝓡 m) (𝓡 m) f x (mfderiv (𝓡 m) (𝓡 m) f x) := sorry
  have h2 : HasMFDerivAt (𝓡 m) (𝓡 m) f.symm x (mfderiv (𝓡 m) (𝓡 m) f.symm x) := sorry
  sorry

theorem inverse_transition_of_transition
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) ⊤  M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) ⊤  M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :

  .id _ _ = (Dab m φ_β φ_α x) ∘L (Dab m φ_α φ_β x) := by

  let Dαβ := Dab m φ_α φ_β
  let Dβα := Dab m φ_β φ_α
  let s := φ_α.toFun '' (φ_α.source ∩ φ_β.source)

  have h1 : HasMFDerivAt (𝓡 m) (𝓡 m)  (φ_α.symm ≫ₕ φ_β) (φ_α x) (Dαβ x) := by
    apply MDifferentiableAt.hasMFDerivAt (ContMDiffAt.mdifferentiableAt (contMDiffAt_chart_transition m φ_α hΦ_Α φ_β hΦ_Β x hx) le_top)

  have h2 : HasMFDerivAt (𝓡 m) (𝓡 m)  (φ_β.symm ≫ₕ φ_α) (φ_β x) (Dβα x) := by
    have hy : x ∈ φ_β.source ∩ φ_α.source := by
       rw [Set.inter_comm]
       assumption
    exact MDifferentiableAt.hasMFDerivAt (ContMDiffAt.mdifferentiableAt (contMDiffAt_chart_transition m φ_β hΦ_Β φ_α hΦ_Α x hy) le_top)

  have h2_rw : HasMFDerivAt (𝓡 m) (𝓡 m) (φ_β.symm ≫ₕ φ_α) ((φ_α.symm ≫ₕ φ_β) (φ_α x)) (Dβα x) := by
    have h2_rwa : (φ_α.symm ≫ₕ φ_β) (φ_α x) = (φ_β x) := h_equiv m φ_α φ_β x hx
    rw [h2_rwa]
    exact h2

  have h_inv1 : ∀ x ∈ φ_α.source ∩ φ_β.source,
  ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x) = (φ_α x) := by
   exact inverse_of_chart_transition m φ_α φ_β

  have h_inv2 : ∀ x ∈ s,
    ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) x = id x := by
    intro x hx
    obtain ⟨y, hy, hfy⟩ := (Set.mem_image ↑φ_α.toPartialEquiv (φ_α.source ∩ φ_β.source) x).mp hx
    have h := h_inv1 y hy
    rw [←hfy]
    exact h

  have h3 : ∀ x ∈ s,
    mfderivWithin (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) s x =
    mfderivWithin (𝓡 m) (𝓡 m) id s x :=
      mfderivWithin_congr_of_eq_on_open ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) id s (open_image_of_inter_sources m φ_α φ_β) h_inv2

  have h4 : φ_α x ∈ s := by
      exact ⟨x, hx, rfl⟩

  have h5 : mfderivWithin (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) s (φ_α x) =
              mfderivWithin (𝓡 m) (𝓡 m) id s (φ_α x) := by
              apply h3 (φ_α x) h4

  have h6 : HasMFDerivAt (𝓡 m) (𝓡 m) ((φ_β.symm ≫ₕ φ_α) ∘ (φ_α.symm ≫ₕ φ_β)) (φ_α x) ((Dβα x).comp (Dαβ x)) := by
    apply HasMFDerivAt.comp (φ_α x) h2_rw h1

  have h7 : MDifferentiableAt (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) := by
     apply HasMFDerivAt.mdifferentiableAt h6

  have h8 : mfderiv (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) =
            mfderiv (𝓡 m) (𝓡 m) id (φ_α x) := by
            have h1 : mfderivWithin (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) s (φ_α x) =
                      mfderiv (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) := by
                      apply MDifferentiable.mfderivWithin h7 (IsOpen.uniqueMDiffWithinAt (open_image_of_inter_sources m φ_α φ_β) h4)
            have h2 : mfderivWithin (𝓡 m) (𝓡 m) id s (φ_α x) =
                      mfderiv (𝓡 m) (𝓡 m) id (φ_α x) := by
                      apply MDifferentiable.mfderivWithin mdifferentiableAt_id (IsOpen.uniqueMDiffWithinAt (open_image_of_inter_sources m φ_α φ_β) h4)
            calc
                mfderiv (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) =
                mfderivWithin (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) s (φ_α x) := by
                  apply h1.symm
                _ = mfderivWithin (𝓡 m) (𝓡 m) id s (φ_α x) := by
                  apply h5
                _ = mfderiv (𝓡 m) (𝓡 m) id (φ_α x) := by
                  apply h2

  have h9 : HasMFDerivAt (𝓡 m) (𝓡 m) (↑(φ_β.symm ≫ₕ φ_α) ∘ ↑(φ_α.symm ≫ₕ φ_β)) (φ_α x)
              (mfderiv (𝓡 m) (𝓡 m) ((φ_α ∘ φ_β.symm)  ∘ (φ_β ∘ φ_α.symm)) (φ_α x)) := by
                apply MDifferentiableAt.hasMFDerivAt h7

  have ha : HasMFDerivAt
            (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x)
            (mfderiv (𝓡 m) (𝓡 m) id (φ_α x)) := by
            rw [<-h8]
            exact h9

  have hb : HasMFDerivAt
            (𝓡 m) (𝓡 m) ((↑φ_α ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x)
            (ContinuousLinearMap.id ℝ (TangentSpace (𝓡 m) (φ_α x))) := by
            rw [<-mfderiv_id]
            exact ha

  apply hasMFDerivAt_unique hb h6

open ContinuousLinearMap

theorem zero_mderiv_change_of_coords
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) ⊤  M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) ⊤  M)
  (g : EuclideanSpace ℝ (Fin m) -> EuclideanSpace ℝ (Fin 1))
  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source)
  (hαβ : MDifferentiableAt (𝓡 m) (𝓡 m) (φ_β ∘ ↑φ_α.symm) (φ_α x))
  (hg : MDifferentiableAt (𝓡 m) (𝓡 1) g (((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) :
    mfderiv (𝓡 m) (𝓡 1) (g ∘ φ_β ∘ ↑φ_α.symm) (φ_α x) = 0 ->
    mfderiv (𝓡 m) (𝓡 1) g  ((φ_β ∘ ↑φ_α.symm) (φ_α x)) = 0 := by

  intro h

  have h1 : mfderiv (𝓡 m) (𝓡 1) (g ∘ (φ_β ∘ ↑φ_α.symm)) (φ_α x) =
            (mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x) := by
     apply mfderiv_comp (φ_α x) hg hαβ

  have h2 : (mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L  (Dab m φ_α φ_β x) = 0 := by
    rw [<-h1]
    exact h

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

  have he : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x))) ∘L (Dab m φ_α φ_β x)) ∘L (Dab m φ_β φ_α x) =
            0 := by
    rw [h2]
    rw [ContinuousLinearMap.zero_comp]

  have hg : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) ∘L  (.id _ _) = 0 := by
    rw [<-h5]
    exact he

  have hh : ((mfderiv (𝓡 m) (𝓡 1) g ((φ_β  ∘ ↑φ_α.symm) (φ_α x)))) = 0 := by
    rw [<-h6]
    exact hg

  exact hh

theorem bar {α β : Type _}
  [TopologicalSpace α]
  {f g : α → β}
  {t : Set α}
  {y : α}
  (ht : IsOpen t)
  (hy : y ∈ t)
  (h : ∀ x ∈ t, f x = g x) :
  f =ᶠ[nhds y] g := by
  have h1 : t ∈ nhds y := IsOpen.mem_nhds ht hy
  exact Filter.Eventually.mono h1 h

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (f : M → (EuclideanSpace ℝ (Fin 1)))
  (hs : ContMDiff (𝓡 m) (𝓡 1) ⊤ f)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) ⊤  M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) ⊤  M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
    fderiv ℝ (f ∘ φ_α.invFun) (φ_α.toFun x) = 0 →
    fderiv ℝ (f ∘ φ_β.invFun) (φ_β.toFun x) = 0 := by

    have h0 : ContDiffAt ℝ (⊤ : ENat) (φ_α.symm.trans φ_β) (φ_α x) := by
      exact contDiffAt_chart_transition m φ_α hΦ_Α  φ_β hΦ_Β x hx

    sorry

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ⊤  M]
  (f : M → (EuclideanSpace ℝ (Fin 1)))
  (hs : ContMDiff (𝓡 m) (𝓡 1) ⊤ f)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) ⊤  M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) ⊤  M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
    mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_α.invFun) (φ_α.toFun x) = 0 →
    mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_β.invFun) (φ_β.toFun x) = 0 := by

    have h0 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) := by
      exact contMDiffAt_chart_transition m φ_α hΦ_Α  φ_β hΦ_Β x hx

    have h1 : MDifferentiableAt (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β) (φ_α x) := by
      exact ContMDiffAt.mdifferentiableAt h0 le_top

    let g : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin 1)) := f ∘ φ_α.invFun
    let h : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin 1)) := f ∘ φ_β.invFun

    have h2 : ContMDiffAt (𝓡 m) (𝓡 1) ⊤ h (φ_β x) := by
      have h21 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_β.symm (φ_β x) :=
        contMDiffAt_symm_of_mem_maximalAtlas hΦ_Β (φ_β.map_source hx.2)
      exact ContMDiffAt.comp (I' := 𝓡 m) (φ_β x) (ContMDiff.contMDiffAt hs) h21

    have h3 : MDifferentiableAt (𝓡 m) (𝓡 1) h (φ_β x) := ContMDiffAt.mdifferentiableAt h2 le_top

    have h4 : MDifferentiableAt (𝓡 m) (𝓡 1) h ((↑φ_β ∘ ↑φ_α.symm) (φ_α x)) := by
      rw [<-h_equiv m φ_α φ_β x hx] at h3
      exact h3

    have h5 : mfderiv (𝓡 m) (𝓡 1) (h ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) = 0 →
              mfderiv (𝓡 m) (𝓡 1) h ((↑φ_β ∘ ↑φ_α.symm) (φ_α x)) = 0 := by
      exact zero_mderiv_change_of_coords m φ_α hΦ_Α φ_β hΦ_Β h x hx h1 h4

    have h6 : mfderiv (𝓡 m) (𝓡 1) (h ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) = 0 →
              mfderiv (𝓡 m) (𝓡 1) h (φ_β x) = 0 := by
      intro h
      have h1_rewritten := h5 h
      rw [h_equiv m φ_α φ_β x hx] at h1_rewritten
      exact h1_rewritten

    have h333 : ∀ x ∈ φ_α.source ∩ φ_β.source,
                (h ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) = g (φ_α x) := by
      intro x hx
      have h3a : (h ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) = g (φ_α x) := by
        calc
          ((f ∘ φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) (φ_α x) = f (φ_β.symm (φ_β (φ_α.symm (φ_α x)))) := by
            rw [Function.comp_apply, Function.comp_apply, Function.comp_apply]
          _ = f (φ_β.symm (φ_β x)) := by
            rw [φ_α.left_inv hx.1]
          _ = f x := by
            rw [φ_β.left_inv hx.2]
          _ = f (φ_α.symm (φ_α x)) := by
            rw [φ_α.left_inv hx.1]
          _ = (f ∘ φ_α.symm) (φ_α x) := by
            rw [Function.comp_apply]
      exact h3a

    have h6p : ∀ x ∈ φ_α.toFun '' (φ_α.source ∩ φ_β.source),
              ((f ∘ ↑φ_β.symm) ∘ ↑φ_β ∘ ↑φ_α.symm) x = g x := by
      intro x hx
      simp only [Set.mem_image] at hx
      obtain ⟨y, hy_mem, hx_eq⟩ := hx
      have h_eq := h333 y hy_mem
      rw [<-hx_eq]
      exact h_eq

    have deduce_h6c_transformed : ∀ x ∈ φ_α.source ∩ φ_β.source,
    mfderiv (𝓡 m) (𝓡 1) (h ∘ (φ_β ∘ φ_α.symm)) (φ_α x) =
    mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_α.symm) (φ_α x) := by
      intro x hx

      have h0 : φ_α x ∈ Set.image φ_α (φ_α.source ∩ φ_β.source) := ⟨x, hx, rfl⟩

      have h1 : h ∘ φ_β ∘ φ_α.symm =ᶠ[nhds (φ_α x)] f ∘ φ_α.symm := by
        exact bar (open_image_of_inter_sources m φ_α φ_β) h0 h6p
      have h2 : mfderiv (𝓡 m) (𝓡 1) (h ∘ (φ_β ∘ φ_α.symm)) (φ_α x) =
                mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_α.symm) (φ_α x) := Filter.EventuallyEq.mfderiv_eq h1
      exact h2

    have h11 : mfderiv (𝓡 m) (𝓡 1) (f ∘ ↑φ_α.symm) (φ_α x) = 0 →
               mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_β.symm) (φ_β x) = 0 := by
      intro h_eq_zero
      have h_rewrite := deduce_h6c_transformed x hx
      rw [<-h_rewrite] at h_eq_zero
      exact h6 h_eq_zero

    exact h11

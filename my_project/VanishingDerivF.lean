import Mathlib
import Mathlib.Topology.ContinuousOn
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

open Manifold

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

def myBall : Set (EuclideanSpace ℝ (Fin 1)) := Metric.ball ((EuclideanSpace.single 1 1)  : EuclideanSpace ℝ (Fin 1)) 1

open SmoothManifoldWithCorners

#check fderiv
#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
#synth SmoothManifoldWithCorners (𝓡 1) (EuclideanSpace ℝ (Fin 1))
#check mfderiv (𝓡 1) (𝓡 1) id sorry
#check maximalAtlas (EuclideanSpace ℝ (Fin m)) M

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (f : M → (EuclideanSpace ℝ (Fin 1)))
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
    mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_α.invFun) (φ_α.toFun x) = 0 ↔
    mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_β.invFun) (φ_β.toFun x) = 0 := by

    let g : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin 1)) := f ∘ φ_α.invFun
    let h : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin 1)) := f ∘ φ_β.invFun

    let Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
      λ x => mfderiv (𝓡 m) (𝓡 1) g (φ_α.toFun x)

    let Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
      λ x => mfderiv (𝓡 m) (𝓡 1) g (φ_β.toFun x)

    have smooth_chart_h : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_α.toFun x := sorry

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

    have h1 : ∀ x ∈ φ_α.source ∩ φ_β.source, g (φ_α.toFun x) = (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun x) := by
      intros x hx
      have h1a : ∀ y ∈ φ_α.source, φ_α.invFun (φ_α.toFun y) = y := λ h hy => φ_α.left_inv hy
      have h1b : x ∈ φ_α.source := hx.1
      have h1c : φ_α.invFun (φ_α.toFun x) = x := h1a _ h1b
      have h1d : g (φ_α.toFun x) = f x := by
        calc  g (φ_α.toFun x) = (f ∘ φ_α.invFun) (φ_α.toFun x) := rfl
              _ = f (φ_α.invFun (φ_α.toFun x)) := rfl
              _ = f x := by rw [h1c]

      have h1g : ∀ y ∈ φ_β.source, φ_β.invFun (φ_β.toFun y) = y := λ h hy => φ_β.left_inv hy
      have h1h : x ∈ φ_β.source := hx.2
      have h1i : φ_β.invFun (φ_β.toFun x) = x := h1g _ h1h
      have h1j : (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun x) = f x := by
        calc
         (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun x) = h (φ_β.toFun (φ_α.invFun (φ_α.toFun x))) := rfl
         _ = f (φ_β.invFun (φ_β.toFun (φ_α.invFun (φ_α.toFun x)))) := rfl
         _ = f (φ_β.invFun (φ_β.toFun x)) := by rw [h1c]
         _ = f x := by rw [h1i]

      have h1k : g (φ_α.toFun x) = (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun x) := by
        rw [h1d]
        rw [h1j]

      exact h1k

    have g1 : ∀ x ∈ φ_α.toFun '' (φ_α.source ∩ φ_β.source), g x = (h ∘ (φ_α.symm.trans φ_β).toFun) x := by
      rintro x ⟨y, hy, rfl⟩
      exact h1 y hy

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

    have h2 : ∀ x ∈ φ_α.toFun '' (φ_α.source ∩ φ_β.source),
      mfderivWithin (𝓡 m) (𝓡 1) g (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) x =
      mfderivWithin (𝓡 m) (𝓡 1) (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) x :=
       mfderivWithin_congr_of_eq_on_open g (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) h2o g1

    let s := φ_α.toFun '' (φ_α.source ∩ φ_β.source)

    have h3 : MDifferentiableWithinAt (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β).toFun s (φ_α x) := by
      sorry

    have bah : mfderiv (𝓡 m) (𝓡 1) (h ∘ (φ_α.symm.trans φ_β).toFun) (φ_α x) =
               (mfderiv (𝓡 m) (𝓡 1) h ((φ_α.symm.trans φ_β).toFun (φ_α x))).comp (mfderiv (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β).toFun (φ_α x)) := by
      sorry

    sorry

#check mfderiv_comp_mfderivWithin
#check HasMFDerivAt.comp_hasMFDerivWithinAt
#check MDifferentiableWithinAt.comp

variable
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]

variable (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
variable (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))

example (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)
  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
    ContMDiffWithinAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β).toFun (φ_α.toFun '' (φ_α.source ∩ φ_β.source))
    (φ_α x) := by
    have h1 : ContMDiffOn (𝓡 m) (𝓡 m) ⊤ φ_α φ_α.source := contMDiffOn_of_mem_maximalAtlas hΦ_Α
    sorry

-- import Mathlib

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
  apply ContMDiffAt.comp (I' := 𝓡 m)
  · apply contMDiffAt_of_mem_maximalAtlas hΦ_Β
    simpa [hx.1] using hx.2
  · apply contMDiffAt_symm_of_mem_maximalAtlas hΦ_Α
    exact PartialHomeomorph.map_source φ_α hx.1


#check contMDiffOn_of_mem_maximalAtlas

#check maximalAtlas (𝓡 m) M

#check mfderivWithin (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β).toFun (φ_α.toFun '' (φ_α.source ∩ φ_β.source))

#check ContMDiff (𝓡 m) (𝓡 1) ⊤

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (f : M → ℝ)
  (smooth_f : ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) ⊤ f)
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


    have smooth_h : ContMDiffAt (𝓡 m) 𝓘(ℝ, ℝ) ⊤ h ((φ_α.symm.trans φ_β).toFun (φ_α x)) := by
      have bar : ContMDiffAt (𝓡 m) 𝓘(ℝ, ℝ) ⊤ f (φ_β.invFun (φ_β x)) := sorry
      have baz : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_β.invFun (φ_β x) := sorry
      have foo : ContMDiffAt (𝓡 m) 𝓘(ℝ, ℝ) ⊤ (f ∘ φ_β.invFun) (φ_β x) := ContMDiffAt.comp (φ_β x) bar baz
      sorry

    have hg : DifferentiableAt ℝ h ((φ_α.symm.trans φ_β).toFun (φ_α x)) := sorry
    have hf : DifferentiableAt ℝ (φ_α.symm.trans φ_β).toFun (φ_α x) := sorry
    exact fderiv_comp (φ_α x) hg hf

  sorry

def hbo : IsOpen myBall := Metric.isOpen_ball
def heq : ∀ x ∈ myBall, id x = id x := by
  intros x hx
  exact rfl

#check mfderivWithin_congr_of_eq_on_open
  (id : EuclideanSpace ℝ (Fin 1) -> EuclideanSpace ℝ (Fin 1))
  (id : EuclideanSpace ℝ (Fin 1) -> EuclideanSpace ℝ (Fin 1))
  myBall hbo heq

example :
 ∀ x ∈ myBall, mfderivWithin (𝓡 1) (𝓡 1) id myBall x = mfderivWithin (𝓡 1) (𝓡 1) id myBall x :=
  mfderivWithin_congr_of_eq_on_open id id myBall hbo heq

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) :
    IsOpen φ_α.source := φ_α.open_source

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) :
    IsOpen (φ_α.toFun '' φ_α.source) := by
      have h1 : IsOpen φ_α.target := φ_α.open_target
      have h2 : φ_α.toFun '' φ_α.source = φ_α.target := φ_α.image_source_eq_target
      have h3 : IsOpen (φ_α.toFun '' φ_α.source ) := h2 ▸ h1
      exact h3

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (s : Set M)
  (ho : IsOpen s) (hs : s ⊆ φ_α.source):
    IsOpen (φ_α '' s) := by
      have h1 := φ_α.isOpen_image_iff_of_subset_source hs
      rw [h1]
      exact ho

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (s : Set M)
  (ho : IsOpen s) (hs : s ⊆ φ_α.source) :
    IsOpen (φ_α.toFun '' s) := by
    have h2 : φ_α.toFun = φ_α := φ_α.toFun_eq_coe
    rw [h2]
    have h1 := φ_α.isOpen_image_iff_of_subset_source hs
    rw [h1]
    exact ho

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) :
    IsOpen (φ_α '' φ_α.source) := by
      have h1 : IsOpen φ_α.source := φ_α.open_source
      have hs : φ_α.source ⊆ φ_α.source := by rfl
      have h2 := φ_α.isOpen_image_iff_of_subset_source hs
      rw [h2]
      exact h1

#check ContinuousWithinAt
#check continuousWithinAt_id
#check ContinuousOn.isOpen_preimage
#check PartialEquiv

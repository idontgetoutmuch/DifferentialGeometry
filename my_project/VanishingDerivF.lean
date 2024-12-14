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

-- #check fderiv
-- #synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
-- #synth SmoothManifoldWithCorners (𝓡 1) (EuclideanSpace ℝ (Fin 1))
-- #check mfderiv (𝓡 1) (𝓡 1) id sorry
-- #check maximalAtlas (EuclideanSpace ℝ (Fin m)) M

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (f : M → (EuclideanSpace ℝ (Fin 1)))
  (hs : ContMDiff (𝓡 m) (𝓡 1) ⊤ f)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) :
    mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_α.invFun) (φ_α.toFun x) = 0 ↔
    mfderiv (𝓡 m) (𝓡 1) (f ∘ φ_β.invFun) (φ_β.toFun x) = 0 := by

    let g : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin 1)) := f ∘ φ_α.invFun
    let h : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin 1)) := f ∘ φ_β.invFun
    have h17 : ContMDiffAt (𝓡 m) (𝓡 1) ⊤ g (φ_α x) := by
      have h1 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_α.symm (φ_α x) :=
        contMDiffAt_symm_of_mem_maximalAtlas hΦ_Α (φ_α.map_source hx.1)
      exact ContMDiffAt.comp (I' := 𝓡 m) (φ_α x) (ContMDiff.contMDiffAt hs) h1

    have h17b : ContMDiffAt (𝓡 m) (𝓡 1) ⊤ h (φ_β x) := by
      have h1 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ φ_β.symm (φ_β x) :=
        contMDiffAt_symm_of_mem_maximalAtlas hΦ_Β (φ_β.map_source hx.2)
      exact ContMDiffAt.comp (I' := 𝓡 m) (φ_β x) (ContMDiff.contMDiffAt hs) h1

    have h18 : MDifferentiableAt (𝓡 m) (𝓡 1) g (φ_α x) := ContMDiffAt.mdifferentiableAt h17 le_top
    have h18b : MDifferentiableAt (𝓡 m) (𝓡 1) h (φ_β x) := ContMDiffAt.mdifferentiableAt h17b le_top

    let Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
      λ x => mfderiv (𝓡 m) (𝓡 1) g (φ_α.toFun x)

    let Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
      λ x => mfderiv (𝓡 m) (𝓡 1) h (φ_β.toFun x)

    have hgAkaf : HasMFDerivAt (𝓡 m) (𝓡 1) g (φ_α x) (Dg x) :=
      MDifferentiableAt.hasMFDerivAt h18
    have hhAkag : HasMFDerivAt (𝓡 m) (𝓡 1) h (φ_β x) (Dh x) :=
      MDifferentiableAt.hasMFDerivAt h18b

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

    have h3 : ContMDiffAt (𝓡 m) (𝓡 m) ⊤ (φ_α.symm.trans φ_β) (φ_α x) := by
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

    let Dαβ : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
      λ x => mfderiv (𝓡 m) (𝓡 m) ((φ_α.symm.trans φ_β).toFun) (φ_α.toFun x)

    have h23 : MDifferentiableAt (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β) (φ_α x) := ContMDiffAt.mdifferentiableAt h3 le_top

    have h31 : HasMFDerivAt (𝓡 m) (𝓡 m)  (φ_α.symm.trans φ_β) (φ_α x) (Dαβ x) :=
      MDifferentiableAt.hasMFDerivAt h23

    have h41 : (φ_α.symm ≫ₕ φ_β) (φ_α x) = (φ_β x) := by
      rw [PartialHomeomorph.trans_apply]
      congr
      exact PartialHomeomorph.left_inv φ_α (Set.mem_of_mem_inter_left hx)

    have h61 : HasMFDerivAt (𝓡 m) (𝓡 1) h ((φ_α.symm ≫ₕ φ_β) (φ_α x)) (Dh x) := by
      rw [h41]
      exact hhAkag

    have baa : HasMFDerivAt (𝓡 m) (𝓡 1) (h ∘ ((φ_α.symm.trans φ_β).toFun)) (φ_α x) ((Dh x).comp (Dαβ x)) := by
      apply HasMFDerivAt.comp (φ_α x) h61 h31

    sorry

variable
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]

variable (x : M)

variable (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
variable (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))

-- #check HasMFDerivAt.comp (φ_α x) (_ : HasMFDerivAt (𝓡 m) (𝓡 1) sorry sorry sorry)
-- #check ((HasMFDerivAt.comp sorry sorry sorry) : HasMFDerivAt (𝓡 m) (𝓡 1) sorry sorry sorry)
set_option maxHeartbeats 200000

example
  (m : ℕ) {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [SmoothManifoldWithCorners (𝓡 m) M]
  (f : M → (EuclideanSpace ℝ (Fin 1)))
  (hs : ContMDiff (𝓡 m) (𝓡 1) ⊤ f)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ maximalAtlas (𝓡 m) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ maximalAtlas (𝓡 m) M)

  (x : M) (hx : x ∈  φ_α.source ∩ φ_β.source) : true := by

    let αβ : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m)) := (φ_α.symm.trans φ_β)

    let Dαβ : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
      λ x => mfderiv (𝓡 m) (𝓡 m) αβ (φ_α.toFun x)

    have hst : HasMFDerivAt (𝓡 m) (𝓡 m) (φ_α.symm.trans φ_β) (φ_α x) (Dαβ x) := sorry

    let h : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin 1)) := f ∘ φ_β.invFun

    let Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1)) :=
      λ x => mfderiv (𝓡 m) (𝓡 1) h (φ_β.toFun x)

    have hsh : HasMFDerivAt (𝓡 m) (𝓡 1) h ((φ_α.symm.trans φ_β) (φ_α x)) (Dh x) := sorry

    have bab : HasMFDerivAt (𝓡 m) (𝓡 1) (h ∘ ((φ_α.symm.trans φ_β))) (φ_α x) ((Dh x).comp (Dαβ x)) := sorry

    have bab : HasMFDerivAt (𝓡 m) (𝓡 1) (h ∘ ((φ_α.symm.trans φ_β))) (φ_α x) ((Dh x).comp (Dαβ x)) := by
      apply HasMFDerivAt.comp (φ_α x) hsh hst

    sorry

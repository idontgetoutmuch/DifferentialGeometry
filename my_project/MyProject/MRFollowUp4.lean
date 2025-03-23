import Mathlib

open SmoothManifoldWithCorners
open IsManifold
open scoped Manifold
open TopologicalSpace

#check fderivWithin_of_isOpen

theorem helper1
  {EE : Type*} [TopologicalSpace EE]
  {FF : Type*} [TopologicalSpace FF]
  {f : PartialHomeomorph EE FF} {g : PartialHomeomorph FF EE} {x : EE}
  (hf : f ≫ₕ g = PartialHomeomorph.ofSet f.source f.open_source)
  (ht : x ∈ f.source) : f x ∈ g.source := by
    have h1 : (PartialHomeomorph.ofSet f.source f.open_source).source = f.source := rfl
    have h2 : (f ≫ₕ g).source = f.source := by rw [<-hf] at h1; exact h1
    have h3 : (f ≫ₕ g).source = f.source ∩ ↑f ⁻¹' g.source := f.trans_source g
    have h4 : f.source = f.source ∩ ↑f ⁻¹' g.source := by rw [h2] at h3; exact h3
    have h5 : x ∈ f.source ∩ ↑f ⁻¹' g.source := by rw [h4] at ht; exact ht
    have h6 : f x ∈ g.source := h5.2
    exact h6

theorem helper2
  (n : ℕ)
  (x : EuclideanSpace ℝ (Fin n))
  (f : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (g : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (hf : f ≫ₕ g = PartialHomeomorph.ofSet f.source f.open_source)
  -- (hr : g ≫ₕ f = PartialHomeomorph.ofSet g.source g.open_source)
  (fd : DifferentiableOn ℝ f f.source)
  (gd : DifferentiableOn ℝ g g.source)
  (hsx : x ∈ f.source)

  : (fderiv ℝ (↑g) (f x)).comp (fderivWithin ℝ (↑f) f.source x) = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by

  have hz : f x ∈ g.source := helper1 hf hsx

  have hss : f.source ∈ nhds x := IsOpen.mem_nhds f.open_source hsx
  have htt : g.source ∈ nhds (f x) := IsOpen.mem_nhds g.open_source hz

  have h1 : DifferentiableWithinAt ℝ f f.source x := fd x hsx
  have h2 : DifferentiableAt ℝ g (f x) := DifferentiableOn.differentiableAt gd htt
  have h3 : DifferentiableAt ℝ f x := DifferentiableOn.differentiableAt fd hss

  have h4 : Set.EqOn (f ≫ₕ g) (PartialHomeomorph.ofSet f.source f.open_source) f.source := by
    rw [hf]
    intro x h
    exact rfl

  have h5 : fderiv ℝ (f ≫ₕ g) x =
            ContinuousLinearMap.comp (fderiv ℝ g (f x)) (fderiv ℝ f x) := fderiv_comp x h2 h3

  have h5a : fderiv ℝ (f ≫ₕ g) x =
             (fderiv ℝ g (f x)).comp (fderiv ℝ f x) := fderiv_comp x h2 h3

  have h7 : UniqueDiffWithinAt ℝ f.source x := IsOpen.uniqueDiffWithinAt f.open_source hsx

  have h8a : fderivWithin ℝ (↑(f ≫ₕ g)) f.source x =
             fderivWithin ℝ (↑(PartialHomeomorph.ofSet f.source f.open_source)) f.source x := fderivWithin_congr' h4 hsx

  have h5b : fderivWithin ℝ (g ∘ f) f.source x = (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) :=
   fderiv_comp_fderivWithin x h2 h1 h7

  have h5c : fderivWithin ℝ (f ≫ₕ g) f.source x =
            (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) := fderiv_comp_fderivWithin x h2 h1 h7

  have h8 : fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x =
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := fderivWithin_id' h7

  have h6 : (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) =
            ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      calc (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) = fderivWithin ℝ (f ≫ₕ g) f.source x := h5c.symm
           _ = fderivWithin ℝ (↑(PartialHomeomorph.ofSet f.source f.open_source)) f.source x := h8a
           _ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := h8
  exact h6

lemma hf
  (n : ℕ)
  (x : EuclideanSpace ℝ (Fin n))
  (f : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (g : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (hf : f ≫ₕ g = PartialHomeomorph.ofSet f.source f.open_source)
  (hr : g ≫ₕ f = PartialHomeomorph.ofSet g.source g.open_source)
  (fd : DifferentiableOn ℝ f f.source)
  (gd : DifferentiableOn ℝ g g.source)
  (hsx : x ∈ f.source)
 : ∀ x ∈ f.source, ∃ (L : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) (L' : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))),
    (fderivWithin ℝ f f.source x = L) ∧ (fderivWithin ℝ g f.target (f x) = L') ∧
    (L.comp L' = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) ∧ (L'.comp L = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    := by
      intros x hx
      have L_eq : fderivWithin ℝ f f.source x = fderiv ℝ f x :=
        fderivWithin_of_isOpen f.open_source hx
      have L'_eq : fderivWithin ℝ g f.target (f x) = fderiv ℝ g (f x) :=
        fderivWithin_of_isOpen f.open_target (f.map_source hx)
      let L := fderivWithin ℝ f f.source x
      let L' := fderivWithin ℝ g f.target (f x)
      use L, L'
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · have hy : f x ∈ f.target := PartialHomeomorph.map_source f hx

        have ha : (fderiv ℝ f (g (f x))).comp (fderivWithin ℝ g f.target (f x)) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)):= he (f x) hy

        have hgf : g (f x) = x := by
          have h1 : (f ≫ₕ g) x = x := by
            rw [hf]
            rfl
          exact h1
        have hb : (fderiv ℝ (↑f) x).comp (fderivWithin ℝ (↑g) f.target (f x)) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
                    rw [hgf] at ha
                    exact ha

        have h1 : (fderivWithin ℝ f f.source x).comp (fderivWithin ℝ g f.target (f x)) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
                  calc
                    (fderivWithin ℝ f f.source x).comp (fderivWithin ℝ g f.target (f x)) =
                    (fderiv ℝ f x).comp (fderivWithin ℝ g f.target (f x)) := by rw [L_eq]
                    _ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := hb
        exact h1
      · have hy : f x ∈ f.target := PartialHomeomorph.map_source f hx
        have hd : (fderiv ℝ (↑g) (f x)).comp (fderivWithin ℝ (↑f) f.source x) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := helper2 n x f g hf fd gd hx

        have ha : (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)):= hd

        have h1 : (fderivWithin ℝ g f.target (f x)).comp (fderivWithin ℝ f f.source x) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
                  calc
                    (fderivWithin ℝ g f.target (f x)).comp (fderivWithin ℝ f f.source x) =
                    (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) := by rw [L'_eq]
                    _ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := ha

        have h1 : L'.comp L = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by rw [h1]
        exact h1

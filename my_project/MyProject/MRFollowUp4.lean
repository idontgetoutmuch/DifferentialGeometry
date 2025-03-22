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

variable
(n : ℕ)
(f : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
(g : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))

def s := f.source
def t := f.target
def E := EuclideanSpace ℝ (Fin n)
def F := EuclideanSpace ℝ (Fin n)

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

theorem DifferentiableOn.differentiable_within_at
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {s : Set E} {x : E}
  (h : DifferentiableOn 𝕜 f s) (hx : x ∈ s) :
  DifferentiableWithinAt 𝕜 f s x := h x hx

example
{EE : Type*} [TopologicalSpace EE]
{ff : Type*} [TopologicalSpace FF]

 {f : PartialHomeomorph EE FF} {g : PartialHomeomorph FF EE}
  (hf : f ≫ₕ g = PartialHomeomorph.ofSet f.source f.open_source)
  (hr : g ≫ₕ f = PartialHomeomorph.ofSet g.source g.open_source) :
  f.source = g.target := by
  have hz : (PartialHomeomorph.ofSet f.source f.open_source).source = f.source := rfl
  have hy : (PartialHomeomorph.ofSet f.source f.open_source).target = f.source := PartialHomeomorph.ofSet_target f.source f.open_source
  have hx : (f ≫ₕ g).target = f.source := by
    rw [<-hf] at hy
    exact hy
  have hw : (f ≫ₕ g).source = f.source := by
    rw [<-hf] at hz
    exact hz
  have h1 : (f ≫ₕ g).target = g.target ∩ g.symm ⁻¹' f.target := f.trans_target g
  have h2 : f.source = g.target ∩ g.symm ⁻¹' f.target := by rw [hx] at h1; exact h1

  exact sorry

theorem helper1'
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

example
  (n : ℕ)
  (x : EuclideanSpace ℝ (Fin n))
  (f : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (g : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (hf : f ≫ₕ g = PartialHomeomorph.ofSet f.source f.open_source)
  (hr : g ≫ₕ f = PartialHomeomorph.ofSet g.source g.open_source)
  (fd : DifferentiableOn ℝ f f.source)
  (gd : DifferentiableOn ℝ g g.source)
  (hsx : x ∈ f.source)

  : true := by

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

  have h3 : g ∘ f = f ≫ₕ g := PartialHomeomorph.coe_trans f g

  have h6 : Set.EqOn (f ≫ₕ g) (PartialHomeomorph.ofSet f.source f.open_source) f.source := by
      rw [hf]
      intro x h
      exact rfl

  have h5 : fderivWithin ℝ (f ≫ₕ g) f.source x =
            fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x :=
      fderivWithin_congr' h6 hsx

  have h5a : fderivWithin ℝ (g ∘ f) f.source x =
            fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x := by
    rw [h3]
    exact h5

  have h8 : fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x =
              ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := fderivWithin_id' sorry

  have hd : ∀ x ∈ f.source,
    (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) =
     ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
      exact sorry

  have h9 : fderivWithin ℝ (g ∘ f) f.source x =
              (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) :=
      fderiv_comp_fderivWithin x h2 h1 sorry

  have hc : fderivWithin ℝ (f ≫ₕ g) f.source x =
              (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) :=
      fderiv_comp_fderivWithin x h2 h1 sorry

  have he : ∀ y ∈ f.target,
    (fderiv ℝ f (g y)).comp (fderivWithin ℝ g f.target y) =
     ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := sorry

  exact sorry

example
  (n : ℕ)
  (x : EuclideanSpace ℝ (Fin n))
  (f : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (g : PartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
  (hf : f ≫ₕ g = PartialHomeomorph.ofSet f.source f.open_source)
  (hr : g ≫ₕ f = PartialHomeomorph.ofSet g.source g.open_source)
  (fd : DifferentiableOn ℝ f f.source)
  (gd : DifferentiableOn ℝ g g.source)
  (hsx : x ∈ f.source)
  (hss : f.source ∈ nhds x)

  : true := by

  have h6 : DifferentiableAt ℝ f x :=
      DifferentiableOn.differentiableAt fd hss
  have h6a : DifferentiableWithinAt ℝ f f.source x := sorry
  have h7 : DifferentiableAt ℝ g (f x) :=
      sorry

  have h3 : g ∘ f = f ≫ₕ g := PartialHomeomorph.coe_trans f g

  have hb : fderiv ℝ (f ≫ₕ g) x =
              ContinuousLinearMap.comp (fderiv ℝ g (f x))
                                       (fderiv ℝ f x) := fderiv_comp x h7 h6

  have h6 : Set.EqOn (f ≫ₕ g) (PartialHomeomorph.ofSet f.source f.open_source) f.source := by
      rw [hf]
      intro x h
      exact rfl

  have h5 :   fderivWithin ℝ (f ≫ₕ g) f.source x =
                fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x :=
      fderivWithin_congr' h6 hsx

  have h8 : fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x =
              ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := fderivWithin_id' sorry

  have h9 : fderivWithin ℝ (g ∘ f) f.source x =
              (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) :=
      fderiv_comp_fderivWithin x h7 h6a sorry

  have hc : fderivWithin ℝ (f ≫ₕ g) f.source x =
              (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) :=
      fderiv_comp_fderivWithin x h7 h6a sorry

  have hd : ∀ x ∈ f.source,
    (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) =
     ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := sorry

  have he : ∀ y ∈ f.target,
    (fderiv ℝ f (g y)).comp (fderivWithin ℝ g f.target y) =
     ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := sorry

  let s := f.source
  let t := f.target
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin n)

  have L_eq : fderivWithin ℝ f f.source x = fderiv ℝ f x :=
              fderivWithin_of_isOpen f.open_source hsx

  have L'_eq : fderivWithin ℝ g f.target (f x) = fderiv ℝ g (f x) :=
    fderivWithin_of_isOpen f.open_target (f.map_source hsx)

  have hf : ∀ x ∈ s, ∃ (L : E →L[ℝ] F) (L' : F →L[ℝ] E),
    (fderivWithin ℝ f s x = L) ∧ (fderivWithin ℝ g t (f x) = L') ∧
    (L.comp L' = ContinuousLinearMap.id ℝ F) ∧ (L'.comp L = ContinuousLinearMap.id ℝ E)
    := by
      intros x hx
      have L_eq : fderivWithin ℝ f f.source x = fderiv ℝ f x :=
        fderivWithin_of_isOpen f.open_source hx
      have L'_eq : fderivWithin ℝ g f.target (f x) = fderiv ℝ g (f x) :=
        fderivWithin_of_isOpen f.open_target (f.map_source hx)
      let L := fderivWithin ℝ f s x
      let L' := fderivWithin ℝ g t (f x)
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
        have hb : (fderiv ℝ (↑f) x).comp (fderivWithin ℝ (↑g) t (f x)) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
                    rw [hgf] at ha
                    exact ha

        have h1 : (fderivWithin ℝ f f.source x).comp (fderivWithin ℝ g t (f x)) =
                  ContinuousLinearMap.id ℝ F := by
                  calc
                    (fderivWithin ℝ f f.source x).comp (fderivWithin ℝ g t (f x)) =
                    (fderiv ℝ f x).comp (fderivWithin ℝ g t (f x)) := by rw [L_eq]
                    _ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := hb
        exact h1
      · have hy : f x ∈ f.target := PartialHomeomorph.map_source f hx
        have ha : (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) =
                  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)):= hd x hx

        have h1 : (fderivWithin ℝ g f.target (f x)).comp (fderivWithin ℝ f f.source x) =
                  ContinuousLinearMap.id ℝ F := by
                  calc
                    (fderivWithin ℝ g f.target (f x)).comp (fderivWithin ℝ f f.source x) =
                    (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) := by rw [L'_eq]
                    _ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := ha

        have h1 : L'.comp L = ContinuousLinearMap.id ℝ E := by rw [h1]
        exact h1

  exact sorry

#check StructureGroupoid.symm'

#check  mdifferentiableAt_atlas
#check mdifferentiableOn_atlas
#check  mdifferentiable_of_mem_atlas

#check  mdifferentiableAt_atlas_symm
#check mdifferentiableOn_atlas_symm

#check MDifferentiableOn.comp
#check mfderivWithin

#check DifferentiableOn.hasFDerivAt
#check MDifferentiableOn

#check MDifferentiableOn.mdifferentiableAt
#check MDifferentiableAt.hasMFDerivAt

#check mfderiv_comp

#check PartialHomeomorph.ofSet_apply

#check mfderivWithin_of_isOpen

#check mfderiv_comp_mfderivWithin

#check DifferentiableOn

#check (LinearMap.id : (EuclideanSpace ℝ (Fin 3)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3)))
#check (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)))

#check  fderivWithin_id'
#check  fderivWithin_id

example
  (x : EuclideanSpace ℝ (Fin 3))
  (f : PartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
  (g : PartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
  (hf : f ≫ₕ g = PartialHomeomorph.ofSet f.source f.open_source)
  (hr : g ≫ₕ f = PartialHomeomorph.ofSet g.source g.open_source)
  (fd : DifferentiableOn ℝ f f.1.source)
  (gd : DifferentiableOn ℝ g g.1.source)
  (hsx : x ∈ f.source)
  (hss : f.source ∈ nhds x)

  : true := by

  have h6 : DifferentiableAt ℝ f x :=
      DifferentiableOn.differentiableAt fd hss
  have h6a : DifferentiableWithinAt ℝ (↑f) f.source x := sorry
  have h7 : DifferentiableAt ℝ g (f x) :=
      sorry

  have h3 : g ∘ f = f ≫ₕ g := PartialHomeomorph.coe_trans f g

  have hb : fderiv ℝ (f ≫ₕ g) x =
              ContinuousLinearMap.comp (fderiv ℝ g (f x))
                                       (fderiv ℝ f x) := fderiv_comp x h7 h6

  have h6 : Set.EqOn (f ≫ₕ g) (PartialHomeomorph.ofSet f.source f.open_source) f.source := by
      rw [hf]
      intro x h
      exact rfl

  have h5 :   fderivWithin ℝ (f ≫ₕ g) f.source x =
                fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x :=
      fderivWithin_congr' h6 hsx

  have h8 : fderivWithin ℝ (PartialHomeomorph.ofSet f.source f.open_source) f.source x =
              ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := fderivWithin_id' sorry

  have h9 : fderivWithin ℝ (g ∘ f) f.source x =
              (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) :=
      fderiv_comp_fderivWithin x h7 h6a sorry

  have hc : fderivWithin ℝ (f ≫ₕ g) f.source x =
              (fderiv ℝ g (f x)).comp (fderivWithin ℝ f f.source x) :=
      fderiv_comp_fderivWithin x h7 h6a sorry

  exact sorry

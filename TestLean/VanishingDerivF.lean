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

lemma source_inter_image {N : Type*} [TopologicalSpace N]
  (φ : PartialHomeomorph N (EuclideanSpace ℝ (Fin n)))
  (ψ : PartialHomeomorph N (EuclideanSpace ℝ (Fin n))) :
  φ.source ∩ ψ.source = φ.invFun '' (φ.toFun '' (φ.source ∩ ψ.source)) := by
    have h01 : ∀ y, y ∈ φ.source -> φ.invFun (φ.toFun y) = y := λ h hy => φ.left_inv hy
    have h02 : φ.source ∩ ψ.source ⊆ (φ.invFun '' (φ.toFun '' (φ.source ∩ ψ.source))) := by
      intros x hx
      have h02a : x ∈ φ.source := hx.1
      have h02b : φ.invFun (φ.toFun x) = x := h01 _ h02a
      have h02z : (φ.invFun ∘ φ.toFun) x = φ.invFun (φ.toFun x) := rfl
      have h02y : (φ.invFun ∘ φ.toFun) x = x := by
        rw [h02z]
        exact h02b
      have h02c : (φ.invFun ∘ φ.toFun) x ∈ (φ.invFun ∘ φ.toFun) '' (φ.source ∩ ψ.source) := by
        exact Set.mem_image_of_mem (φ.invFun ∘ φ.toFun) hx
      have h02d : x ∈ (φ.invFun ∘ φ.toFun) '' (φ.source ∩ ψ.source) :=
        by rw [h02y] at h02c
           exact h02c
      have h02e : (φ.invFun ∘ φ.toFun) '' (φ.source ∩ ψ.source) =
                  φ.invFun '' (φ.toFun '' (φ.source ∩ ψ.source)) := by rw [<-Set.image_comp]
      rw [h02e] at h02d
      exact h02d
    have h03 : (φ.invFun '' (φ.toFun '' (φ.source ∩ ψ.source))) ⊆  φ.source ∩ ψ.source := by
      intros y hy
      have h3b : ∃ z ∈ φ.source ∩ ψ.source, (φ.invFun ∘ φ.toFun) z = y := by
        rcases hy with ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
      have h3c : ∀ y, y ∈ φ.source -> φ.invFun (φ.toFun y) = y := λ h hy => φ.left_inv hy
      have h3d : ∀ y, y ∈ φ.source -> (φ.invFun ∘ φ.toFun) y = y :=  h3c
      have h3e : ∃ z ∈ φ.source ∩ ψ.source, z = y := by
        rcases h3b with ⟨z, hz, h_eq⟩
        have h_z : (φ.invFun ∘ φ.toFun) z = z := h3d z hz.1
        rw [h_eq] at h_z
        use z
        exact ⟨hz, h_z.symm⟩
      have h3f : y ∈ φ.source ∩ ψ.source := by
        rcases h3e with ⟨z, hz, h_eq⟩
        rw [h_eq] at hz
        exact hz
      exact h3f
    have h04 : φ.source ∩ ψ.source =
               φ.invFun '' (φ.toFun '' (φ.source ∩ ψ.source)) := by
      exact subset_antisymm h02 h03
    exact h04

example
  (f : M → ℝ)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ atlas (EuclideanSpace ℝ (Fin m)) M) :

      let Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_α.invFun)
                        (φ_α.toFun x)

      let Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_β.invFun)
                        (φ_β.toFun x)

      ∀ x ∈ φ_α.source ∩ φ_β.source, (∀ v, Dg x v = 0) <-> (∀ v, Dh x v = 0) := by

  let g := f ∘ φ_α.invFun
  let h := f ∘ φ_β.invFun

  have h0 : g '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = (h ∘ φ_β.toFun ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) := by

    have h04 : φ_α.source ∩ φ_β.source =
           φ_α.invFun '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) :=
      source_inter_image φ_α φ_β

    have h07 : φ_α.source ∩ φ_β.source =
           φ_β.invFun '' (φ_β.toFun '' (φ_α.source ∩ φ_β.source)) := by
      rw [Set.inter_comm]
      exact source_inter_image φ_β φ_α

    have h05 : g '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = f '' (φ_α.source ∩ φ_β.source) := by
      calc
        g '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = (f ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) := by rfl
        _                                             = f '' (φ_α.invFun '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source))) := by rw [Set.image_comp]
        _                                             = f '' (φ_α.source ∩ φ_β.source) := by rw [<-h04]

    have h06 : (h ∘ φ_β.toFun ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = f '' (φ_α.source ∩ φ_β.source) := by
      have h06a : ((h ∘ φ_β.toFun) ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = (h ∘ φ_β.toFun) '' (φ_α.invFun '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source))) := by
        rw [Set.image_comp]
      have h06g : (h ∘ φ_β.toFun ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = f '' (φ_α.source ∩ φ_β.source) := by
        calc
          (h ∘ φ_β.toFun ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = (h ∘ φ_β.toFun) '' (φ_α.invFun '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source))) := h06a
          _ = (h ∘ φ_β.toFun) '' (φ_α.source ∩ φ_β.source) := by rw [<-h04]
          _ = (f ∘ φ_β.invFun ∘ φ_β.toFun) '' (φ_α.source ∩ φ_β.source) := by rfl
          _ = f '' ((φ_β.invFun ∘ φ_β.toFun) '' (φ_α.source ∩ φ_β.source)) := by rw [Set.image_comp]
          _ = f '' ((φ_β.invFun '' (φ_β.toFun '' (φ_α.source ∩ φ_β.source)))) := by rw [Set.image_comp]
          _ = f '' (φ_α.source ∩ φ_β.source) := by rw [<-h07]
      exact h06g

    have h08 : g '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) =
           (h ∘ φ_β.toFun ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) := by
      calc
        g '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) = f '' (φ_α.source ∩ φ_β.source) := h05
        _ = (h ∘ φ_β.toFun ∘ φ_α.invFun) '' (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) := h06.symm

    exact h08
  have h2 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            g x = (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by sorry
  have h1 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            fderiv ℝ g x = fderiv ℝ (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by
    intros x hx
    simp [h2 x hx]
    sorry
  sorry

-- set_option trace.Meta.Tactic.simp.rewrite true

example
  (f : M → ℝ)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ atlas (EuclideanSpace ℝ (Fin m)) M) :

      let Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_α.invFun)
                        (φ_α.toFun x)

      let Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_β.invFun)
                        (φ_β.toFun x)

      ∀ x ∈ φ_α.source ∩ φ_β.source, (∀ v, Dg x v = 0) <-> (∀ v, Dh x v = 0) := by

  let g := f ∘ φ_α.invFun
  let h := f ∘ φ_β.invFun
  have h2 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            g x = (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by sorry
  have h1 : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            fderiv ℝ g x = fderiv ℝ (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by
    intros x hx
    simp [h2 x hx]
    sorry
  sorry

example
  (f g : ℝ → ℝ)
  (h2 : ∀ x ∈ Set.univ, f x = g x) :
  ∀ x ∈ Set.univ, fderiv ℝ f x = fderiv ℝ g x := by
    intros x _
    have eq_fg : f = g := funext (λ y => h2 y (Set.mem_univ y))
    rw [eq_fg]

example (f g : ℝ → ℝ) (z : ℝ) (U : Set ℝ) (hfg : ∀ x ∈ U, f x = g x) (hz : z ∈ U) :
  fderivWithin ℝ f U z = fderivWithin ℝ g U z := by
    have hs : Set.EqOn f g U := hfg
    exact fderivWithin_congr' hs hz

example {m n : ℕ}
  (f g : (Fin m → ℝ) → (Fin n → ℝ)) (z : Fin m → ℝ) (U : Set (Fin m → ℝ))
  (hfg : ∀ x ∈ U, f x = g x) (hz : z ∈ U) :
  fderivWithin ℝ f U z = fderivWithin ℝ g U z := by
  have hs : Set.EqOn f g U := hfg
  exact fderivWithin_congr' hs hz

example
  (f : M → ℝ)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
   (g : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_α.invFun)
   (h : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_β.invFun)
   (Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_α.invFun)
                        (φ_α.toFun x))
   (Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_β.invFun)
                        (φ_β.toFun x)) :

   ∀ z ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
  fderivWithin ℝ g (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) z =
  fderivWithin ℝ (h ∘ ↑φ_β.toPartialEquiv ∘ φ_α.invFun) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) z := by

   have hfg  : ∀ x ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
            g x = (h ∘ φ_β.toFun ∘ φ_α.invFun) x := by
     sorry

   have hd : ∀ z ∈ (φ_α.toFun '' (φ_α.source ∩ φ_β.source)),
             fderivWithin ℝ g (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) z =
             fderivWithin ℝ (h ∘ φ_β.toFun ∘ φ_α.invFun) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) z := by
     intros z hz
     have hs : Set.EqOn g (h ∘ φ_β.toFun ∘ φ_α.invFun) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) := hfg

     exact fderivWithin_congr' hs hz

   exact hd

variable (f : ((Fin m) -> ℝ) → ℝ) (f' : ((Fin m) -> ℝ) →L[ℝ] ℝ) (x : (Fin m) -> ℝ)

example : Prop := HasFDerivAt f f' x

example : Prop :=
  let foo := λ (f : ((Fin m) -> ℝ) → ℝ) (f' : ((Fin m) -> ℝ) →L[ℝ] ℝ) (x : (Fin m) -> ℝ) => HasFDerivAt f f' x
  sorry

example
  (f : M → ℝ)
  (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Α : φ_α ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
  (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
  (hΦ_Β : φ_β ∈ atlas (EuclideanSpace ℝ (Fin m)) M)
   (g : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_α.invFun)
   (h : EuclideanSpace ℝ (Fin m) → ℝ := f ∘ φ_β.invFun)
   (Dg : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_α.invFun)
                        (φ_α.toFun x))
   (Dh : M -> (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
        λ x => fderiv ℝ (f ∘ φ_β.invFun)
                        (φ_β.toFun x)) : true := by

   have baz: fderiv ℝ (φ_α.symm.trans φ_β).toFun =
             fderiv ℝ (((φ_α.symm.trans φ_β).toFun) : EuclideanSpace ℝ (Fin m) -> (EuclideanSpace ℝ (Fin m))) := sorry

   let bab := λ x y => HasFDerivAt h (Dh x) y
   let bac := λ y => fderiv ℝ (φ_α.symm.trans φ_β).toFun y
   let bad := λ x => (Dh x).comp (fderiv ℝ (φ_α.symm.trans φ_β).toFun (φ_α x))

   let foo := λ (f : ((Fin m) -> ℝ) → ℝ) (f' : ((Fin m) -> ℝ) →L[ℝ] ℝ) (x : (Fin m) -> ℝ) => HasFDerivAt f f' x
   let fop := λ (x : M) (g : EuclideanSpace ℝ (Fin m) → (Fin m -> ℝ)) => (Dh x).comp (fderiv ℝ g (φ_α x))
   let foq := λ x => fop x ((φ_α.symm.trans φ_β).toFun)

   have fos :  ∀ x ∈ φ_α.source ∩ φ_β.source,
    (foq x) = ((Dh x) :  EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := sorry

   -- let bae := λ (f' : ℝ) (x : EuclideanSpace ℝ (Fin m)) =>
   --   HasDerivAt (h ∘ (φ_β.toFun ∘ φ_α.invFun)) f' x
   -- let bae := λ f' x => HasDerivAt (h ∘ (φ_β.toFun ∘ φ_α.invFun)) f' x
                     -- ((Dh x).comp (fderiv ℝ (φ_α.symm.trans φ_β).toFun (φ_α x)))

   -- have baa : ∀ x ∈ φ_α.source ∩ φ_β.source,
   --   HasDerivAt (h ∘ (φ_β.toFun ∘ φ_α.invFun)) ((Dh x).comp (fderiv ℝ (φ_α.symm.trans φ_β).toFun))

   have foo : ∀ x ∈ φ_α.source ∩ φ_β.source, (Dh x) = ((Dh x) :  EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
              -- HasFDerivAt (h ∘ (φ_β.toFun ∘ φ_α.invFun)) ((Dh x).comp (φ_β.toFun ∘ φ_α.invFun)') z =
              -- HasFDerivAt (h ∘ (φ_β.toFun ∘ φ_α.invFun)) (Dh.comp (φ_β.toFun ∘ φ_α.invFun)') z
              := by
     intros x hx
     have bar : (fderivWithin ℝ (φ_β.toFun ∘ φ_α.invFun) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) (φ_α x) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))=
                fderivWithin ℝ (φ_β.toFun ∘ φ_α.invFun) (φ_α.toFun '' (φ_α.source ∩ φ_β.source)) (φ_α x) := by rfl
     sorry

   sorry

#check λ (φ_α : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) (φ_β : PartialHomeomorph M (EuclideanSpace ℝ (Fin m))) =>
  Set.mem_image (φ_α.invFun ∘ φ_α.toFun) (φ_α.source ∩ φ_β.source)

#min_imports

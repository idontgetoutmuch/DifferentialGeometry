import Mathlib

open Topology Set

lemma continuous_on_union_of_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) :
  ∀ (s t : Set X), IsOpen s → IsOpen t → ContinuousOn f s → ContinuousOn f t → ContinuousOn f (s ∪ t) := by
  intro s t hso hto hcs hct
  rw [continuousOn_open_iff (IsOpen.union hso hto)]
  intro u hu
  have h1 : ∀ u, IsOpen u → IsOpen (s ∩ f ⁻¹' u) := (continuousOn_open_iff hso).mp hcs
  have h2 : ∀ u, IsOpen u → IsOpen (t ∩ f ⁻¹' u) := (continuousOn_open_iff hto).mp hct
  rw [inter_comm, Set.inter_union_distrib_left, inter_comm]
  have h3 : IsOpen (f ⁻¹' u ∩ t) := by rw [Set.inter_comm]; exact h2 u hu
  exact IsOpen.union (h1 u hu) h3

lemma constant_open_continuous_pre {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (s : Set X) (u : Set Y) :
  (∀ (x y : X), x ∈ s → y ∈ s → f x = f y) → IsOpen s → IsOpen (s ∩ f ⁻¹' u) := by
  intros h_const h_open
  by_cases hP : ∃ x ∈ s, f x ∈ u
  · obtain ⟨x₀, hx₀, hx₀u⟩ := hP
    have h_all : ∀ y ∈ s, f y ∈ u := by
      intro y hy
      have h_all_0 : f y =  f x₀ := h_const y x₀ hy hx₀
      have h_all_1 : f y ∈ u := by
        rw [<-h_all_0] at hx₀u
        exact hx₀u
      exact h_all_1
    have h1 : f ⁻¹' u ∩ s = s := by
      ext y
      have h1a : y ∈ f ⁻¹' u ∩ s -> y ∈ s := by
        intro hy
        exact hy.2
      have h1b : y ∈ s -> y ∈ f ⁻¹' u ∩ s := by
        intro hy
        exact ⟨h_all y hy, hy⟩
      exact ⟨h1a, h1b⟩
    rw [inter_comm, h1]
    exact h_open
  · have h1 :  ¬∃ x ∈ s, f x ∈ u := hP
    have h1 : s ∩ f ⁻¹' u = ∅ := by
      ext y
      constructor
      · intro hy
        exfalso
        apply h1
        exact ⟨y, (hy.1 : y ∈ s), (hy.2 : f y ∈ u)⟩
      · intro hy
        exact False.elim hy
    rw [h1]
    exact isOpen_empty

lemma constant_open_continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) (s : Set X) :
  (∀ (x y : X), x ∈ s → y ∈ s → f x = f y) → IsOpen s → ContinuousOn f s := by
  intros h_const h_open
  rw [continuousOn_open_iff h_open]
  intro u hu
  exact constant_open_continuous_pre f s u h_const h_open

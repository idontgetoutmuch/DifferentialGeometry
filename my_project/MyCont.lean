import Mathlib

open Topology Set

def PR := Subtype (λ (x : ℝ) => x ≠ 0)

def f : PR -> ℝ := λx => if x > 0 then x else -x

-- noncomputable
-- def g : { x : ℝ | x ≠ 0} -> ℝ := λ x => if x > (0 : ℝ) then x else -x

noncomputable
def h : ℝ -> ℝ := λ x => if x > (0 : ℝ) then x else -x

#check TopologicalSpace

instance : TopologicalSpace PR := sorry

instance : TopologicalSpace  := sorry

noncomputable
def g : { x : ℝ | x ≠ 0} -> ℝ := λ x => if x > (0 : ℝ) then x else -x

example (x : ℝ) (h : ¬ (x > (0 : ℝ))) : (λ x => if x > (0 : ℝ) then x else -x) x = -x := by simp [g, h]

example : Continuous g := by
  have h0 : ∀ s, g ⁻¹' s = {x | g x ∈ s} := by
    intro s
    have h0a : g ⁻¹' s = {x | g x ∈ s} := rfl
    exact h0a
  have h2a (x : { x : ℝ | x ≠ 0}) (h : x > (0 : ℝ)) : g x = x := by simp [g, h]
  have h2b (x : { x : ℝ | x ≠ 0}) (h : x < (0 : ℝ)) : g x = -x := by
    exact sorry
  have h3 : ∀ s, s = { x ∈ s | x > 0} ∪ {x ∈ s | x < 0} ∪ {x ∈ s | x = 0} := sorry
  have h4 : ∀ s, g ⁻¹' s =  g ⁻¹' { x ∈ s | x > 0} ∪  g ⁻¹' {x ∈ s | x < 0} ∪  g ⁻¹' {x ∈ s | x = 0}:= sorry
  have h5 : ∀ (s : Set ℝ), g ⁻¹' { x ∈ s | x > 0} = { x ∈ s | x > (0 : ℝ)} ∪ { x ∈ s | x < (0 : ℝ)} := sorry
  have h6 : ∀ (s : Set ℝ), g ⁻¹' { x ∈ s | x < 0} = ∅ := sorry
  have h7 : ∀ (s : Set ℝ), g ⁻¹' {x ∈ s | x = 0} = ∅ := sorry
  have h8 : ∀ s, g ⁻¹' s = { x ∈ s | x > 0} ∪ { x ∈ s | x < 0} := sorry
  have h9 : ∀ (s : Set ℝ), IsOpen { x ∈ s | x > 0} := sorry
  have ha : ∀ (s : Set ℝ), IsOpen { x ∈ s | x < 0} := sorry
  have h2 : ∀ s, IsOpen s → IsOpen (g ⁻¹' s) := by
    exact sorry
  have hb : ∀ s, IsOpen s → IsOpen (g ⁻¹' s) <-> Continuous g := sorry
  exact sorry

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
example ( x : { x : ℝ | x ≠ 0}) (h : ¬ (x > (0 : ℝ))) : g x = -x := by simp [g, h]
example ( x : { x : ℝ | x ≠ 0}) (h : (x < (0 : ℝ))) : g x = -x := by simp [g, h]

example (x : { x : ℝ | x ≠ 0}) (h : x < (0 : ℝ)) : g x = -x := by
  have h' : ¬ (x > (0 : ℝ)) := by exact not_lt.mpr (le_of_lt h)
  simp [g, h']

theorem foo {α : Type} {P Q : α → Prop} : { x | P x } ∪ { x | Q x } = { x | P x ∨ Q x } := by
  ext x
  simp

example (s : Set ℝ) : {x | x ∈ s ∧ x > 0 ∨ x ∈ s ∧ x < 0} ∪ { x | x ∈ s ∧ x = 0} = {x | (x ∈ s ∧ x > 0 ∨ x ∈ s ∧ x < 0) ∨ x ∈ s ∧ x = 0} := by
  have h1 : ({ x ∈ s | x > 0} ∪ { x ∈ s | x < 0}) = {x | x ∈ s ∧ x > 0 ∨ x ∈ s ∧ x < 0} := foo
  have h2 : {x | x ∈ s ∧ x > 0 ∨ x ∈ s ∧ x < 0} ∪ { x | x ∈ s ∧ x = 0} = {x | (x ∈ s ∧ x > 0 ∨ x ∈ s ∧ x < 0) ∨ x ∈ s ∧ x = 0} := foo
  exact h2

#check lt_or_gt_of_ne

example (s : Set ℝ) :
  { x ∈ s | x > 0 ∨ x < 0 ∨ x = 0 } = s := by
  ext x
  simp
  exact sorry

example (s : Set ℝ) :
  ({ x ∈ s | x > 0} ∪ { x ∈ s | x < 0}) ∪ { x ∈ s | x = 0 } = { x ∈ s | x > 0 ∨ x < 0 ∨ x = 0 } := by
  sorry

example (x : ℝ) : (x < 0) ∨ ¬ (x < 0) := by exact em (x < 0)

#check ContinuousOn

example : Continuous g := by
  have h0 : ∀ s, g ⁻¹' s = {x | g x ∈ s} := by
    intro s
    have h0a : g ⁻¹' s = {x | g x ∈ s} := rfl
    exact h0a
  have h2a (x : { x : ℝ | x ≠ 0}) (h : x > (0 : ℝ)) : g x = x := by simp [g, h]
  have h2b (x : { x : ℝ | x ≠ 0}) (h : x < (0 : ℝ)) : g x = -x := by
    have h' : ¬ (x > (0 : ℝ)) := by exact not_lt.mpr (le_of_lt h)
    simp [g, h']
  have h3 : ∀ s, s = { x ∈ s | x > 0} ∪ {x ∈ s | x < 0} ∪ {x ∈ s | x = 0} := sorry
  have h4a : ∀ (s : Set ℝ), g ⁻¹' ({ x ∈ s | x > 0} ∪ {x ∈ s | x < (0 : ℝ)})  =  g ⁻¹' { x ∈ s | x > 0} ∪  g ⁻¹' {x ∈ s | x < 0}  := by
    intro s
    exact Set.preimage_union
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

#check continuousOn_open_iff
-- ContinuousOn f s ↔ ∀ (t : Set β), IsOpen t → IsOpen (s ∩ f ⁻¹' t)

noncomputable
def p : ℝ -> ℝ := λ x => if x > (0 : ℝ) then 1 else -1

example : ∀ (t : Set ℝ), IsOpen t → IsOpen ({x | x > (0 : ℝ)} ∩ p ⁻¹' t) := by
  intro t ho x hx
  have h1 : 1 ∉ t ∧ -1 ∉ t -> p ⁻¹' t = ∅ := sorry
  have h2 : 1 ∉ t ∧ -1 ∈ t -> p ⁻¹' t = {x | x ≤ 0} := sorry
  have h3 : 1 ∈ t ∧ -1 ∉ t -> p ⁻¹' t = {x | x > 0} := sorry
  have h4 : 1 ∈ t ∧ -1 ∈ t -> p ⁻¹' t = ℝ := sorry
  have h1a : 1 ∉ t ∧ -1 ∉ t -> {x | x > (0 : ℝ)} ∩ p ⁻¹' t = ∅ := sorry
  have h2a : 1 ∉ t ∧ -1 ∈ t -> {x | x > (0 : ℝ)} ∩ p ⁻¹' t = ∅ := sorry
  have h3a : 1 ∈ t ∧ -1 ∉ t -> {x | x > (0 : ℝ)} ∩ p ⁻¹' t = {x | x > 0} := sorry
  have h4a : 1 ∈ t ∧ -1 ∈ t -> {x | x > (0 : ℝ)} ∩ p ⁻¹' t = {x | x > 0} := sorry
  exact sorry

#check preimage_inter
#check if_pos

example (h : x ∈ {x : ℝ | x ≤ 0}) : x ∉ {x : ℝ | x > 0} := by
  intro k
  have h1 : x > 0 := k
  have h2 : ¬ (x > 0) := not_lt_of_le h
  contradiction

theorem fff : {x : ℝ | x ≤ 0} ∩ {x | x > 0} = ∅ := by
  have hp : {x : ℝ | x > 0}ᶜ = {x : ℝ | x ≤ 0} := by ext x; simp
  have hq : {x : ℝ | x > 0}ᶜ ∩ {x | x > 0} = ∅ := Set.compl_inter_self {x : ℝ | x > 0}
  rw [hp] at hq
  exact hq

example : {x : ℝ | x ≤ 0} ∩ {x | x > 0} = ∅ := by
  have h1 : {x : ℝ | x > 0}ᶜ = {x : ℝ | x ≤ 0} := by ext x; simp
  have h2 : {x : ℝ | x > 0}ᶜ ∩ {x | x > 0} = ∅ := Set.compl_inter_self {x : ℝ | x > 0}
  have h3 : {x : ℝ | x ≤ 0} ∩ {x | x > 0} = {x : ℝ | x > 0}ᶜ ∩ {x | x > 0} := by rw [h1]
  have h4 : {x: ℝ | x ≤ 0} ∩ {x | x > 0} = ∅ :=
    calc
      {x : ℝ | x ≤ 0} ∩ {x | x > 0} = {x : ℝ | x > 0}ᶜ ∩ {x | x > 0} := h3
      _ = ∅ := h2
  exact h4

example : {x : ℝ | x ≤ 0} ∩ {x : ℝ | x > 0} = ∅ := by
  ext x
  have h1 : x > 0 := sorry
  have h2 : ¬ (x > 0) := not_lt_of_le sorry
  contradiction

lemma qreimage_empty (p : ℝ → ℝ) (hp : ∀ x, p x = if x > 0 then 1 else -1) (t : Set ℝ) (h : 1 ∉ t ∧ -1 ∉ t) :
  p ⁻¹' t = ∅ := by
  ext x
  simp [hp]
  intro hx
  cases lt_or_le 0 x with
  | inl hpos => have h1 : 1 ∉ t := h.1
                have h2 : (1 : ℝ) = (if 0 < x then 1 else -1) := (if_pos hpos).symm
                have h3 : (if 0 < x then 1 else -1) ∈ t := hx
                have h4 : 1 ∈ t := by
                  rw [h2]
                  exact h3
                contradiction
  | inr hneg => have h1 : -1 ∉ t := h.2
                have h2 : (-1 : ℝ) = (if 0 < x then 1 else -1) := (if_neg (not_lt_of_le hneg)).symm
                have h3 : (if 0 < x then 1 else -1) ∈ t := hx
                have h4 : -1 ∈ t := by
                  rw [h2]
                  exact h3
                contradiction

lemma preimage_nonpos (p : ℝ → ℝ) (hp : ∀ x, p x = if x > 0 then 1 else -1) (t : Set ℝ) (h : 1 ∉ t ∧ -1 ∈ t) :
  p ⁻¹' t = {x | x ≤ 0} := by
    exact sorry

example (p : ℝ → ℝ) (hp : ∀ x, p x = if x > 0 then 1 else -1) :
  ∀ (t : Set ℝ), IsOpen t → IsOpen ({x | x > (0 : ℝ)} ∩ p ⁻¹' t) := by
  intro t ho
  have h_cases :
    (1 ∉ t ∧ -1 ∉ t) ∨ (1 ∉ t ∧ -1 ∈ t) ∨ (1 ∈ t ∧ -1 ∉ t) ∨ (1 ∈ t ∧ -1 ∈ t) := by
    tauto
  cases h_cases with
  | inl h1 =>
      have : p ⁻¹' t = ∅ := qreimage_empty p hp t h1
      rw [this, inter_empty]
      exact isOpen_empty
  | inr h2 => cases h2 with
              | inl h3 => have h1 : p ⁻¹' t = {x | x ≤ 0} := preimage_nonpos p hp t h3
                          have hf : {x : ℝ | x ≤ 0} ∩ {x | x > 0} = ∅ := by
                            have hp : {x : ℝ | x > 0}ᶜ = {x : ℝ | x ≤ 0} := by ext x; simp
                            have hq : {x : ℝ | x > 0}ᶜ ∩ {x | x > 0} = ∅ := Set.compl_inter_self {x : ℝ | x > 0}
                            rw [hp] at hq
                            exact hq
                          have h2 : {x : ℝ | x ≤ 0} ∩ { x : ℝ  | x > 0 } = ∅ := hf
                          have h3 : p ⁻¹' t ∩ { x | x > 0 } = ∅ := by
                            rw [h1]
                            exact h2
                          rw [h1, Set.inter_comm, h2]
                          exact isOpen_empty
              | inr h4 => cases h4 with
                          | inl h5 => exact sorry
                          | inr h6 => exact sorry

example : ContinuousOn h {x | x > 0} := by
  have h1: ∀ (t : Set ℝ), IsOpen t → IsOpen ({x | x > (0 : ℝ)} ∩ h ⁻¹' t) := by
    exact sorry
  exact sorry


theorem eq_or_succ_le_of_le {a b : ℕ} (h : a ≤ b) : a = b ∨ Nat.succ a ≤ b := by
  cases Nat.eq_or_lt_of_le h with
  | inl h_eq => left; assumption
  | inr h_lt => right; assumption

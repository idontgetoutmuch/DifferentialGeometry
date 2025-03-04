import MyProject.MyCont
import Mathlib

def x := (![1, 0] : EuclideanSpace ℝ (Fin 2))

theorem h : x ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
   exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h5 : (x 0)^2 + (x 1)^2 = 1 := by
    calc
     (x 0)^2 + (x 1)^2 = 1^2 + 0^2 := rfl
     _ = 1 := by simp
  have h6 : x ∈  {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    simp [h5]
  have h7 : x ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
   rw [h1]
   exact h6
  exact h7

def u := (![-1, 0] : EuclideanSpace ℝ (Fin 2))

theorem g : u ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
   exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h5 : (u 0)^2 + (u 1)^2 = 1 := by
    calc
     (u 0)^2 + (u 1)^2 = (-1)^2 + 0^2 := rfl
     _ = 1 := by simp
  have h6 : u ∈  {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    simp [h5]
  have h7 : u ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
   rw [h1]
   exact h6
  exact h7

theorem tOpen : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 } := by
  let V := { x : EuclideanSpace ℝ (Fin 2) | x 1 > 0 }
  have h1 : Continuous (λ (x: EuclideanSpace ℝ (Fin 2)) => (0 : (fun x => ℝ) 1)) := continuous_const
  have h2 :  ∀ (i : Fin 2), Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x i := continuous_apply
  have h3 : Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x 1 := h2 1
  have h4 : IsOpen V := isOpen_lt h1 h3
  let U := { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 }
  have U_eq : U = (fun x ↦ x.val) ⁻¹' V := rfl
  exact isOpen_induced_iff.mpr ⟨V, h4, rfl⟩

theorem tOpen' : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 } := by
  let V := { x : EuclideanSpace ℝ (Fin 2) | x 1 < 0 }
  have h1 : Continuous (λ (x: EuclideanSpace ℝ (Fin 2)) => (0 : (fun x => ℝ) 1)) := continuous_const
  have h2 :  ∀ (i : Fin 2), Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x i := continuous_apply
  have h3 : Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x 1 := h2 1
  have h4 : IsOpen V := isOpen_lt h3 h1
  let U := { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 }
  have U_eq : U = (fun x ↦ x.val) ⁻¹' V := rfl
  exact isOpen_induced_iff.mpr ⟨V, h4, rfl⟩

noncomputable def U := chartAt (EuclideanSpace ℝ (Fin 1)) (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))
noncomputable def V := chartAt (EuclideanSpace ℝ (Fin 1)) (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

noncomputable
def chart_excluding_1 : PartialHomeomorph { x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} (EuclideanSpace ℝ (Fin 1)) := V
noncomputable
def chart_excluding_minus_1 : PartialHomeomorph { x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} (EuclideanSpace ℝ (Fin 1)) := U

noncomputable
def MyCoordChange : Fin 2 → Fin 2 → (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
      | 0, 0, _, α => α
      | 0, 1, x, α => if (x.val 1) > 0 then α else -α
      | 1, 0, x, α => if (x.val 1) > 0 then α else -α
      | 1, 1, _, α => α

theorem MyCoordChange_self : ∀ (i : Fin 2),
    ∀ x ∈ (fun i => if i = 0 then chart_excluding_minus_1.source else chart_excluding_1.source) i,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange i i x v = v := by
    intro i x h v
    have h : MyCoordChange i i x v = v :=
      match i with
        | 0 => rfl
        | 1 => rfl
    exact h

theorem t00 : ContinuousOn (λ p => MyCoordChange 0 0 p.1 p.2) (chart_excluding_minus_1.source ×ˢ univ) := by
  have h1 : (λ (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) =>
    MyCoordChange 0 0 p.fst p.snd) = (λ p => p.snd) := by rfl
  rw [h1]
  exact continuousOn_snd

theorem SulSource : chart_excluding_minus_1.source ∩ chart_excluding_1.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
  exact sorry

#check chart_excluding_minus_1.source
open Topology

#check Continuous.uncurry_right
#check Continuous.uncurry_left

open Function

theorem my_Continuous.uncurry_left.{u, v, u_1} {X : Type u} {Y : Type v} {Z : Type u_1} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] {f : X → Y → Z} (x : X) (h : Continuous (Function.uncurry f)) : Continuous (f x) := h.comp (Continuous.Prod.mk _)

variables {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variables {a : Set X} {b : Set Y}

-- Theorem: if a is open in X and b is open in Y, then a × b is open in X × Y
example (ha : IsOpen a) (hb : IsOpen b) : IsOpen (a ×ˢ b) := ha.prod hb

open Set

example : IsOpen (univ : Set X) := isOpen_univ
example : IsOpen (Set.univ : Set X) := isOpen_univ

-- continuousOn_coordChange : ∀ i j,
--   ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i ∩ baseSet j) ×ˢ univ)

#synth LocallyCompactSpace (EuclideanSpace ℝ (Fin 1))

#check ContinuousMap.uncurry_apply
#check ContinuousMap.continuous_uncurry_of_continuous

example
  {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, C(EuclideanSpace ℝ (Fin 1), EuclideanSpace ℝ (Fin 1)))} :
  Continuous (λ (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => (f x.1) x.2) := by
  have h1 : Continuous (uncurry fun x y ↦ (f x) y) := ContinuousMap.continuous_uncurry_of_continuous f
  have h2 : (uncurry fun x y ↦ (f x) y) = (λ (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => (f x.1) x.2) := by
    rfl
  rw [h2] at h1
  exact h1

#check continuousOn_open_iff

noncomputable
def MyCoordChange01 : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
      | x, α => if (x.val 1) > 0 then α else -α

noncomputable
def MyCoordChange01'': (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := Function.uncurry (MyCoordChange01)

noncomputable
def t := { x : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) | x.val.1 1 > 0 } ∪
         { x : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) | x.val.1 1 < 0 }

#check λ (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) => (x.val.1 1 > 0)

noncomputable
def MyCoordChange01' : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
  | (x, α) =>if (x.val 1) > 0 then α else -α

def s' : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 < x.1.val 1 }

example : ContinuousOn MyCoordChange01' s' := by
  have h0 : IsOpen s' := by
    let π : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) → ℝ :=
      λ x => x.1.val 1
    have hz : Continuous (Prod.fst : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) -> (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) := continuous_fst
    have hy : (Prod.fst : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) -> (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) =
              fun (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => x.1 := sorry
    have hx : Continuous (fun (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => x.1.val) := by
      rw [hy] at hz
      exact sorry

    have h_cont : Continuous π :=
      (Continuous.comp (continuous_apply 1) hx)

    have h0z : Continuous fun (x : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1))) ↦ x.1.val 1 := sorry
    have h0a : IsOpen s':= isOpen_lt continuous_const h0z
    exact sorry
  have h2 : ContinuousOn MyCoordChange01' s' ↔ ∀ (t : Set  (EuclideanSpace ℝ (Fin 1))), IsOpen t → IsOpen (s' ∩ MyCoordChange01' ⁻¹' t) := continuousOn_open_iff h0
  have h3 : ∀ (t : Set  (EuclideanSpace ℝ (Fin 1))), IsOpen t → IsOpen (s' ∩ MyCoordChange01' ⁻¹' t) := sorry
  have h4 : ContinuousOn MyCoordChange01' s' := h2.mpr h3
  exact sorry

example
  {f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, C(EuclideanSpace ℝ (Fin 1), EuclideanSpace ℝ (Fin 1)))}
  {a : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)} :
   f.uncurry a = uncurry (fun x y ↦ (f x) y) a := ContinuousMap.uncurry_apply f a

theorem t01' : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2) ((chart_excluding_minus_1.source ∩ chart_excluding_1.source) ×ˢ univ) := by
  have h1 : (chart_excluding_minus_1.source ∩ chart_excluding_1.source) = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  let U := { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 }
  have h2 : IsOpen U := tOpen
  have h22 : IsOpen (U ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := h2.prod isOpen_univ

  have h4 : ∀ (x y : ↑(Metric.sphere 0 1)), x ∈ U → y ∈ U → MyCoordChange 0 1 x = MyCoordChange 0 1 y := by
    intro x y hx hy
    have h4b : ∀ α, MyCoordChange 0 1 x α = α := by
      intro α
      exact if_pos hx
    have h4c : ∀ α, MyCoordChange 0 1 y α = α := by
      intro α
      exact if_pos hy
    ext α
    rw [h4b, h4c]

  have h44 : ∀ (x y : ↑(Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1)), x ∈ U ×ˢ univ → y ∈ U ×ˢ univ → MyCoordChange 0 1 x.1 x.2 = MyCoordChange 0 1 y.1 y.2 := by
    intro x y hx hy
    have h4b : ∀ α, MyCoordChange 0 1 x.1 α = α := by
      intro α
      exact if_pos hx.1
    have h4c : ∀ α, MyCoordChange 0 1 y.1 α = α := by
      intro α
      exact if_pos hy.1
    have h4d : MyCoordChange 0 1 x.1 = MyCoordChange 0 1 y.1 := h4 x.1 y.1 hx.1 hy.1
    have h4e : MyCoordChange 0 1 x.1 = MyCoordChange 0 1 y.1 := h4 x.1 y.1 hx.1 hy.1
    sorry

  have h33 : ContinuousOn (λ (x, a) => MyCoordChange 0 1 x a) (U ×ˢ univ) :=
   constant_open_continuous (λ (x, a) => MyCoordChange 0 1 x a) (U ×ˢ univ) sorry h22

  have h3 : ContinuousOn (MyCoordChange 0 1) U := constant_open_continuous (MyCoordChange 0 1) U h4 h2
  let V := { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 }
  have ha2 : IsOpen V := tOpen'
  have ha4 : ∀ (x y : ↑(Metric.sphere 0 1)), x ∈ V → y ∈ V → MyCoordChange 0 1 x = MyCoordChange 0 1 y := by
    intro x y hx hy
    have ha4b : ∀ α, MyCoordChange 0 1 x α = -α := by
      intro α
      have hz : x.val 1 < 0 := hx
      have hu :  ¬(0 < x.val 1)  := not_lt_of_gt hz
      have hq : (if x.val 1 > 0 then α else -α) = -α := by exact if_neg hu
      exact hq
    have ha4c : ∀ α, MyCoordChange 0 1 y α = -α := by
      intro α
      have hz : y.val 1 < 0 := hy
      have hu : ¬ (y.val 1 > 0) := by exact not_lt_of_gt hz
      have hq : (if y.val 1 > 0 then α else -α) = -α := by exact if_neg hu
      exact hq
    ext α
    rw [ha4b, ha4c]
  have ha3 : ContinuousOn (MyCoordChange 0 1) V := constant_open_continuous (MyCoordChange 0 1) V ha4 ha2

  have h5 : ContinuousOn (MyCoordChange 0 1) (U ∪ V) := continuous_on_union_of_open (MyCoordChange 0 1) U V h2 ha2 h3 ha3
  rw [h1]

  have h17 : ContinuousOn ((MyCoordChange 0 1) : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
                          ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }) := h5
  have h18 : ContinuousOn (Function.uncurry (MyCoordChange 0 1)) (({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }) ×ˢ univ ) := sorry

  exact h18

theorem t01 : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2) ((chart_excluding_minus_1.source ∩ chart_excluding_1.source) ×ˢ univ) := by
  have h1 : (chart_excluding_minus_1.source ∩ chart_excluding_1.source) = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  let U := { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 }
  have h2 : IsOpen U := tOpen
  have h4 : ∀ (x y : ↑(Metric.sphere 0 1)), x ∈ U → y ∈ U → MyCoordChange 0 1 x = MyCoordChange 0 1 y := by
    intro x y hx hy
    have h4b : ∀ α, MyCoordChange 0 1 x α = α := by
      intro α
      exact if_pos hx
    have h4c : ∀ α, MyCoordChange 0 1 y α = α := by
      intro α
      exact if_pos hy
    ext α
    rw [h4b, h4c]
  have h3 : ContinuousOn (MyCoordChange 0 1) U := constant_open_continuous (MyCoordChange 0 1) U h4 h2
  let V := { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 }
  have ha2 : IsOpen V := tOpen'
  have ha4 : ∀ (x y : ↑(Metric.sphere 0 1)), x ∈ V → y ∈ V → MyCoordChange 0 1 x = MyCoordChange 0 1 y := by
    intro x y hx hy
    have ha4b : ∀ α, MyCoordChange 0 1 x α = -α := by
      intro α
      have hz : x.val 1 < 0 := hx
      have hu :  ¬(0 < x.val 1)  := not_lt_of_gt hz
      have hq : (if x.val 1 > 0 then α else -α) = -α := by exact if_neg hu
      exact hq
    have ha4c : ∀ α, MyCoordChange 0 1 y α = -α := by
      intro α
      have hz : y.val 1 < 0 := hy
      have hu : ¬ (y.val 1 > 0) := by exact not_lt_of_gt hz
      have hq : (if y.val 1 > 0 then α else -α) = -α := by exact if_neg hu
      exact hq
    ext α
    rw [ha4b, ha4c]
  have ha3 : ContinuousOn (MyCoordChange 0 1) V := constant_open_continuous (MyCoordChange 0 1) V ha4 ha2

  have h5 : ContinuousOn (MyCoordChange 0 1) (U ∪ V) := continuous_on_union_of_open (MyCoordChange 0 1) U V h2 ha2 h3 ha3
  rw [h1]

  have h17 : ContinuousOn ((MyCoordChange 0 1) : ↑(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
                          ({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }) := h5
  have h18 : ContinuousOn (Function.uncurry (MyCoordChange 0 1)) (({ x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 }) ×ˢ univ ) := sorry

  exact h18

  have h6 : ContinuousOn Prod.fst ((U ∪ V) ×ˢ univ) := continuousOn_fst

  have hz : Prod.fst '' ((U ∪ V) ×ˢ univ) ⊆ (U ∪ V) := by
    intro z h
    obtain ⟨⟨x, y⟩, hxy, hx_eq⟩ := h
    rw [← hx_eq]
    exact hxy.1
  have hu : Set.MapsTo Prod.fst ((U ∪ V) ×ˢ univ) (U ∪ V) := Set.mapsTo'.mpr hz
  have h7 : ContinuousOn (MyCoordChange 0 1 ∘ Prod.fst) ((U ∪ V) ×ˢ univ) := ContinuousOn.comp h5 h6 hu
  let f : ((U ∪ V) ×ˢ univ) → EuclideanSpace ℝ (Fin 1) := λ p : (U ∪ V) ×ˢ univ => MyCoordChange 0 1 p.val.1 p.val.2
  let g : ((U ∪ V) ×ˢ univ) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := λ p : (U ∪ V) ×ˢ univ => MyCoordChange 0 1 (Prod.fst p.val)
  have heq : (λ p : (Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) => MyCoordChange 0 1 p.1 p.2) = (λ p : (Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) => (MyCoordChange 0 1 ∘ Prod.fst) p p.2) := by
    exact funext (λ p => rfl)
  rw [heq]
  -- rw [h1]
  let foo : (Metric.sphere 0 1) × EuclideanSpace ℝ (Fin 1) -> EuclideanSpace ℝ (Fin 1) := (MyCoordChange 0 1 ∘ Prod.fst)
  have h7' : ContinuousOn (fun p ↦ (MyCoordChange 0 1 ∘ Prod.fst) p p.2) ((U ∪ V) ×ˢ univ) := by
    sorry
  exact h7'

theorem t10 : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2) ((chart_excluding_1.source ∩ chart_excluding_minus_1.source) ×ˢ univ) := by
  exact sorry

  theorem t11 : ContinuousOn (λ p => MyCoordChange 0 0 p.1 p.2) (chart_excluding_1.source ×ˢ univ) := by
  have h1 : (λ (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) =>
    MyCoordChange 0 0 p.fst p.snd) = (λ p => p.snd) := by rfl
  rw [h1]
  exact continuousOn_snd

theorem MyContinuousOn_coordChange : ∀ (i j : Fin 2), ContinuousOn (fun p => MyCoordChange i j p.1 p.2)
  (((fun i => if i = 0 then chart_excluding_minus_1.source else chart_excluding_1.source) i ∩
      (fun i => if i = 0 then chart_excluding_minus_1.source else chart_excluding_1.source) j) ×ˢ
    univ) := by
    intro i j
    fin_cases i
    · fin_cases j
      · simp; exact t00
      · exact t01
    · fin_cases j
      · exact t10
      · simp; exact t11

noncomputable
def f : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
   | x, α => if (x.val 1) > 0 then α else -α

lemma l (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : f x (f x v) = v := by
    by_cases h : x.val 1 > 0
    case pos =>
      simp [f, h]
    case neg =>
      simp [f, h]

theorem t1001 (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (v : EuclideanSpace ℝ (Fin 1)) :
 MyCoordChange 1 0 x (MyCoordChange 0 1 x v) = v := by
  have h3 : ∀ v, f x v = MyCoordChange 0 1 x v := by
   intro h
   rfl
  have h4 : ∀ v, f x v = MyCoordChange 1 0 x v := by
    intro h
    rfl
  have h8 : f x (f x v) = MyCoordChange 1 0 x (MyCoordChange 0 1 x v) := by rw [h3 v, h4]
  have h9 : MyCoordChange 1 0 x (MyCoordChange 0 1 x v) = v := by rw [<-h8, l]
  exact h9

theorem t0110 (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (v : EuclideanSpace ℝ (Fin 1)) :
 MyCoordChange 0 1 x (MyCoordChange 1 0 x v) = v := by
  have h3 : ∀ v, f x v = MyCoordChange 0 1 x v := by
   intro h
   rfl
  have h4 : ∀ v, f x v = MyCoordChange 1 0 x v := by
    intro h
    rfl
  have h8 : f x (f x v) = MyCoordChange 1 0 x (MyCoordChange 0 1 x v) := by rw [h3 v, h4]
  have h9 : MyCoordChange 1 0 x (MyCoordChange 0 1 x v) = v := by rw [<-h8, l]
  exact h9

theorem MyCoordChange_comp : ∀ (i j k : Fin 2),
  ∀ x ∈ (fun i => if i = 0 then chart_excluding_minus_1.source else chart_excluding_1.source) i ∩
        (fun i => if i = 0 then chart_excluding_minus_1.source else chart_excluding_1.source) j ∩
        (fun i => if i = 0 then chart_excluding_minus_1.source else chart_excluding_1.source) k,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange j k x (MyCoordChange i j x v) = MyCoordChange i k x v := by
    intro i j k x h v
    have h : MyCoordChange j k x (MyCoordChange i j x v) = MyCoordChange i k x v :=
      match i, j, k with
        | 0, 0, 0 => rfl
        | 0, 0, 1 => rfl
        | 0, 1, 0 => t1001 x v
        | 0, 1, 1 => rfl
        | 1, 0, 0 => rfl
        | 1, 0, 1 => t0110 x v
        | 1, 1, 0 => rfl
        | 1, 1, 1 => rfl
    exact h

noncomputable
def Mobius : FiberBundleCore (Fin 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) :=
{
  baseSet := λ i => if i = 0 then chart_excluding_minus_1.source
                             else chart_excluding_1.source,

  -- isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  isOpen_baseSet := by
    intro i
    dsimp only
    split
    · exact chart_excluding_minus_1.open_source
    · exact chart_excluding_1.open_source

  indexAt := λ x => if (x.val 0) < 0 then 0 else 1,

  -- mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  mem_baseSet_at := sorry,

  coordChange := MyCoordChange,
  coordChange_self := MyCoordChange_self,
  continuousOn_coordChange := by
    intro i j
    exact MyContinuousOn_coordChange i j
  coordChange_comp := MyCoordChange_comp
}

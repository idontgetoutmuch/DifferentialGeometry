import Mathlib

open Bundle Topology MulAction Set
open Complex

#check ChartedSpace (EuclideanSpace ℝ (Fin 1)) ↑(Metric.sphere 0 1)
#check ChartedSpace.chartAt (sorry : ↑(Metric.sphere 0 1))

example : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} :=
   EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)

def x := (![1, 0] : EuclideanSpace ℝ (Fin 2))

theorem bor : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 <->  y 0 ^ 2 + y 1 ^ 2 = 1 := by
  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  exact sorry

theorem bor1 : y 0 ^ 2 + y 1 ^ 2 = 1 -> y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  intro h
  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h5 : (y 0)^2 + (y 1)^2 = 1 := h
  have h6 : y ∈  {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    simp [h5]
  have h7 : y ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
   rw [h1]
   exact h6
  exact h7

theorem bor2 : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ->  y 0 ^ 2 + y 1 ^ 2 = 1 := by
  intro h

  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)

  have h2 : y ∈ {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
   rw [h1] at h
   exact h

  have h3 : ∑ i : Fin 2, y i ^ 2 = 1 ^ 2 := by
    rw [Set.mem_setOf_eq] at h2
    exact h2

  have h6 :  y 0 ^ 2 + y 1 ^ 2 = 1 := by
    calc
      y 0 ^ 2 + y 1 ^ 2 = ∑ i : Fin 2, y i ^ 2 := by simp
      _ = 1 := by simp [h3, one_pow]

  exact h6

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

#check (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

example (y : Fin 2 -> ℝ) : y ∈ Metric.sphere z 1 <-> dist y z = 1 := Metric.mem_sphere

#check ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

#check chartAt (EuclideanSpace ℝ (Fin 1)) (sorry : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

noncomputable def U := chartAt (EuclideanSpace ℝ (Fin 1)) (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))
noncomputable def V := chartAt (EuclideanSpace ℝ (Fin 1)) (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

noncomputable
def chart_excluding_1 : PartialHomeomorph { x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} (EuclideanSpace ℝ (Fin 1)) := V
noncomputable
def chart_excluding_minus_1 : PartialHomeomorph { x // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} (EuclideanSpace ℝ (Fin 1)) := U

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)⟩

theorem chartAt_source (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (chartAt (EuclideanSpace ℝ (Fin 1)) y).source = (stereographic' 1 (-y)).source := rfl

def xh := ((⟨x, h⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))
def ug := ((⟨u, g⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))

theorem foo : (stereographic' 1 xh).source = {xh}ᶜ := stereographic'_source xh

theorem bar : {xh}ᶜ = { x | x ≠ xh } := rfl

theorem ric (a : EuclideanSpace ℝ (Fin 2)) : (a 0)^2 + (a 1)^2 = 1 -> a ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  exact sorry

theorem cir (a : EuclideanSpace ℝ (Fin 2)) : a ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 -> (a 0)^2 + (a 1)^2 = 1 := by
  intro h
  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h2 : a ∈ {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
   rw [h1] at h
   exact h
  have h3 : ∑ i : Fin 2, a i ^ 2 = 1 ^ 2 := by
   rw [h2]
  have h4 : 1 = (a 0)^2 + (a 1)^2 := by
   calc 1 = ∑ i : Fin 2, a i ^ 2 := by simp [h3, one_pow]
        _ = (a 0)^2 + (a 1)^2 := by simp
  exact h4.symm

theorem sphere_eq_set1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ { a | (a 0)^2 + (a 1)^2 = 1 } := by
  intro a ha
  exact cir a ha

theorem sphere_eq_set2 : { a | (a 0)^2 + (a 1)^2 = 1 } ⊆ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  intro a ha
  exact ric a ha

#check  { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (x 0, x 1) }
#check { x | x ≠ xh }

theorem bir : { x | x ≠ xh } = { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (x 0, x 1) } := sorry

theorem bir1 : y ∈ { x | x ≠ xh } -> y.val ∈ { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (x 0, x 1) } := sorry

theorem bir2 : y ∈ { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (x 0, x 1) } -> true := by
  intro h
  have h1 : y 0 ^ 2 + y 1 ^ 2 = 1 ∧ (y 0, y 1) ≠ (x 0, x 1) := by
    rw [Set.mem_setOf_eq] at h
    exact h
  have h2 : y 0 ^ 2 + y 1 ^ 2 = 1 := h1.left
  have h3 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
   exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h5 : y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := bor1 h2
  have h4 : ⟨y, h5⟩ ∈ { x | x ≠ xh } := sorry
  sorry

#check bor1
#check bor2

theorem dir (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ) : a ≠ xh -> (a.val 0, a.val 1) ≠ (x 0, x 1) := sorry


#check  Membership (Metric.sphere 0 1)

theorem ber : {x | x ≠ xh} ⊆ {a | a ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ a ≠ xh} := sorry


theorem ber : { x | x ≠ xh } ⊆ { a | a ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ a ≠ x } := by
  ext a
  simp only [Set.mem_setOf_eq]
  exact ⟨λ h => ⟨(sorry : a ∈ Metric.sphere 0 1), (sorry : a ≠ x)⟩, λ ⟨_, h⟩ => (sorry : a ∈ Subtype.val '' {x | x ≠ xh})⟩

theorem boz : { a | a ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ a ≠ x } =
              { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (x 0, x 1) }  := sorry

theorem buz : { a | a ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧ a ≠ x } =
              { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (u 0, u 1) }  := sorry

theorem bez : { y : Fin 2 -> ℝ | (y 0)^2 + (y 1)^2 = 1 && y 1 > 0 } ∩
              { y : Fin 2 -> ℝ | (y 0)^2 + (y 1)^2 = 1 && y 1 < 0 }  = ∅ := sorry

#check 1 ∉ {(1 : ℝ)}ᶜ

example (cs : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))
        (v : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))) :
  cs.chartAt v = stereographic' 1 (-v) := by exact sorry

noncomputable
def MyCoordChange : Fin 2 → Fin 2 → (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
      | 0, 0, _, α => α
      | 0, 1, x, α => if (x.val 1) > 0 then α else -α
      | 1, 0, x, α => if (x.val 1) > 0 then α else -α
      | 1, 1, _, α => α

instance : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'

theorem MyCoordChange_self : ∀ (i : Fin 2),
    ∀ x ∈ (fun i => if i = 0 then chart_excluding_minus_1.source else chart_excluding_1.source) i,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange i i x v = v := by
    intro i x h v
    have h : MyCoordChange i i x v = v :=
      match i with
        | 0 => rfl
        | 1 => rfl
    exact h

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
  continuousOn_coordChange := sorry,
  coordChange_comp := MyCoordChange_comp
}

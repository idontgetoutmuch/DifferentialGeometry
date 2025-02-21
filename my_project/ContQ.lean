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

#check bor1
#check bor2

theorem bir1 : y ∈ { x | x ≠ xh } -> y.val ∈ { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (x 0, x 1) } := by
  intro h
  rw [Set.mem_setOf_eq] at h
  obtain h1 := h
  sorry

variable {y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}
variable {xh : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}

theorem bir4 : ∀ xh, y.val ∈ { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (xh.val 0, xh.val 1) } → y ≠ xh :=
by
  intro xh h
  simp only [Set.mem_setOf_eq] at h
  intro h_eq
  rw [h_eq] at h
  exact h.2 rfl

theorem bir5 : ∀ xh, y ∈ { x | x ≠ xh } -> y.val ∈ { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (xh.val 0, xh.val 1) } := by
  intro xh h
  rw [Set.mem_setOf_eq] at h
  obtain h1 := h
  have hy_sphere := bor2 y.property
  have h2 : y.val ≠ xh.val := by
    intro h_eq
    apply h
    exact Subtype.ext h_eq
  have h_neq : (y.val 0, y.val 1) ≠ (xh.val 0, xh.val 1) := by
    intro h_eq
    apply h2
    ext i
    fin_cases i
    · exact sorry -- congr_fun (congr_arg Prod.fst h_eq) ()
    · exact sorry -- congr_fun (congr_arg Prod.snd h_eq) ()
  exact ⟨hy_sphere, by exact h_neq⟩

def Su := { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ a 1 > 0 }
def Sl := { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ a 1 < 0 }

#check {xh}ᶜ ∩ {ug}ᶜ
#check  { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (x 0, x 1) } ∩
        { a : EuclideanSpace ℝ (Fin 2) | (a 0)^2 + (a 1)^2 = 1 ∧ (a 0, a 1) ≠ (u 0, u 1) } = Su ∪ Sl
#check  Su ∩ Sl = ∅

theorem dir (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ) : a ≠ xh -> (a.val 0, a.val 1) ≠ (x 0, x 1) := sorry


#check  Membership (Metric.sphere 0 1)

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

def fn1 : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := λ (x, y) => y

example : ContinuousOn fn1 ((univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  have h1 : fn1 = Prod.snd := rfl
  rw [h1]
  exact continuousOn_snd

#check ContinuousMap.continuous_restrict

theorem fn1Cont : ContinuousOn fn1 ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  have h1 : fn1 = Prod.snd := rfl
  rw [h1]
  exact continuousOn_snd

theorem continuous_MyCoordChange_onP :
  ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
               ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by

  have h1 : Set.EqOn (λ p => MyCoordChange 0 1 p.1 p.2) fn1
            ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
    intro a ha
    simp only [MyCoordChange]
    have h3 : a ∈ {x | x.val 1 > 0} ×ˢ univ := ha
    have h1 : fn1 a = a.2 := rfl
    rw [h1]
    have h4 : a.1.val 1 > 0 := h3.1
    rw [if_pos h4]

  have h2 : ContinuousOn  (λ p => MyCoordChange 0 1 p.1 p.2)
                          ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) :=
    ContinuousOn.congr fn1Cont h1

  exact h2

theorem continuous_MyCoordChange_onN :
  ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
               ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  exact sorry

theorem SemiCircles : ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) ∪
                      ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) =
                      ((chart_excluding_minus_1.source ∩ chart_excluding_1.source) ×ˢ univ) := by
  exact sorry

variables {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variables {S T : Set X} {f : S → Y} {g : T → Y}


def fa : ℝ → ℝ := λ x => x
def fb : ℝ → ℝ := λ x => -x
noncomputable
def fab : ℝ → ℝ := λ x => if x > 0 then fa x else fb x

theorem fab_ne_0_of_x_ne_0 (x : ℝ) (hx : x ≠ 0) : fab x ≠ 0 :=
  have h1 : x > 0 -> fab x ≠ 0 := λ h => by rw [fab]; exact sorry
  have h2 : ¬x > 0 → fab x ≠ 0 := sorry
  by_cases h1 h2

theorem zzz : ContinuousOn fab {x | x ≠ 0} := by
  intro x hx S hS
  have h_preimage : fab ⁻¹' S = ({ x | x > 0 } ∩ { x | fa x ∈ S }) ∪ ({ x | x < 0 } ∩ { x | fb x ∈ S }) := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_union, mem_setOf_eq]
    have ha : fab y ∈ S -> y > 0 ∧ fa y ∈ S ∨ y < 0 ∧ fb y ∈ S := by
      intro hy
      dsimp [fab] at hy
      by_cases h_pos : y > 0
      · left
        rw [if_pos h_pos] at hy
        exact ⟨h_pos, hy⟩
      · right
        rw [if_neg h_pos] at hy
        have h1 : x ≠ 0 := hx
        have h2 : y ≤ 0 := le_of_not_gt h_pos
        have h_neg : y < 0 := lt_of_le_of_ne h2 (sorry : y ≠ 0)
        exact ⟨h_neg, hy⟩
    have hb : y > 0 ∧ fa y ∈ S ∨ y < 0 ∧ fb y ∈ S  -> fab y ∈ S := sorry
    exact (sorry : fab y ∈ S ↔ y > 0 ∧ fa y ∈ S ∨ y < 0 ∧ fb y ∈ S)
  sorry

def fa1 : ℝ -> ℝ := (λ x => x)
def fb1 : ℝ -> ℝ := (λ x => -x)

noncomputable
def fab1 : ℝ -> ℝ := (λ x => if x > 0 then fa x else fb x)

theorem zzz1 : ContinuousOn fab {x | x ≠ 0} := by
  have h1 : ContinuousOn fa {x | x > 0} := continuousOn_id
  have h2 : ContinuousOn fb {x | x < 0} := continuousOn_neg
  intro x hx S hS
  have h3 : fab ⁻¹' S = ({ x | x > 0 } ∩ { x | fa x ∈ S }) ∪ ({ x | x < 0 } ∩ { x | fb x ∈ S }) := by
    ext y
    sorry
  sorry

#check ContinuousWithinAt.union (ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP sorry)
                                (ContinuousOn.continuousWithinAt continuous_MyCoordChange_onN sorry)

#check continuousWithinAt_union

theorem xxx : true := by
  let s := ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))))
  let t := ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))))
  have h1 : ContinuousWithinAt fn1 (s ∪ t) sorry ↔ ContinuousWithinAt fn1 s sorry ∧ ContinuousWithinAt fn1 t sorry := continuousWithinAt_union
  have h2 : ContinuousWithinAt fn1 s sorry := (ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP sorry)
  exact sorry

theorem continuous_on_union {f : α → β} {s t : Set α} [TopologicalSpace α] [TopologicalSpace β] (hs : ContinuousOn f s) (ht : ContinuousOn f t) :
  ContinuousOn f (s ∪ t) := by
  intro p hp
  -- Use the fact that p ∈ s ∪ t is equivalent to p ∈ s or p ∈ t
  cases hp with
  | inl hpos => exact hs hpos
  | inr hneg => exact ht hneg

theorem continuous_on_union1 {f : α → β} {s t : Set α} (p : α) [TopologicalSpace α] [TopologicalSpace β] (hs : ContinuousWithinAt f s p) (ht : ContinuousWithinAt f t p) :
  ContinuousWithinAt f (s ∪ t) p := ContinuousWithinAt.union hs ht

theorem t01PreL : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
                              ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  intro p hp
  exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP hp

theorem t01Pre : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
                              (({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) ∪
                              ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))))) := by
  intro p hp
  apply ContinuousWithinAt.union
  · exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP sorry -- (Or.inl hp)
  · exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onN (Or.inr hp)

theorem t01Pre : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
                              ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by


  exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP sorry

theorem t01Pre : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
                              (({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) ∪
                              ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))))) := by
  intro p hp
  cases hp with
  | inl hpos =>
    exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP hpos
  | inr hneg =>
    exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onN hneg


theorem t01Pre : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
                              (({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) ∪
                              ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))))) := by
  intro p hp
  cases hp with
  | inl hpos =>
    have h1 : ContinuousWithinAt (fun p => MyCoordChange 0 1 p.1 p.2) ({x | x.val 1 > 0} ×ˢ univ) p:= by
      exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP hpos
    exact sorry
  | inr hneg =>
    obtain ⟨h_xneg, _⟩ := hneg
    exact sorry

theorem t01 : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2) ((chart_excluding_minus_1.source ∩ chart_excluding_1.source) ×ˢ univ) := by
  intro p hp
  rw [<-SemiCircles] at hp
  cases hp with
  | inl hpos =>
    have h1 : ContinuousWithinAt (fun p => MyCoordChange 0 1 p.1 p.2) ({x | x.val 1 > 0} ×ˢ univ) p:= by
      exact ContinuousOn.continuousWithinAt continuous_MyCoordChange_onP hpos
    exact (sorry : ContinuousWithinAt (fun p => MyCoordChange 0 1 p.1 p.2) ((chart_excluding_minus_1.source ∩ chart_excluding_1.source) ×ˢ univ) p)
  | inr hneg =>
    obtain ⟨h_xneg, _⟩ := hneg
    exact (sorry : ContinuousWithinAt (fun p => MyCoordChange 0 1 p.1 p.2) ((chart_excluding_minus_1.source ∩ chart_excluding_1.source) ×ˢ univ) p)

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

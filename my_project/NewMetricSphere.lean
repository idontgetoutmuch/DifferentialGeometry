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

#check (chart_excluding_1.source ∩ chart_excluding_1.source) ×ˢ (univ : Set ℝ)

theorem SulSource : chart_excluding_minus_1.source ∩ chart_excluding_1.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
  exact sorry

theorem t00 : ContinuousOn (λ p => MyCoordChange 0 0 p.1 p.2) (chart_excluding_minus_1.source ×ˢ univ) := by
  have h1 : (λ (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) =>
    MyCoordChange 0 0 p.fst p.snd) = (λ p => p.snd) := by rfl
  rw [h1]
  exact continuousOn_snd


#check { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 }
#check (univ : Set (EuclideanSpace ℝ (Fin 1)))
#check { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))

variable {X Y : Type*}
(V : Set Y)

def ff : X × Y -> Y := λ ⟨x, y⟩ => y

theorem preimage_subset_X_times_V :
  ff ⁻¹' V ⊆ (univ : Set X) ×ˢ V := by
  intros p hp
  rw [Set.preimage] at hp
  have h1 : ff p ∈ V := hp
  have h2 : ff ⟨p.1, p.2⟩ = p.2 := rfl
  have h3 : p.2 ∈ V := by rw [h2] at h1; exact h1
  have h4 : p.1 ∈ (univ : Set X) := trivial
  have h5 : ⟨p.1, p.2⟩ ∈ (univ : Set X) ×ˢ V := ⟨h4, h3⟩
  exact h5

theorem X_times_V_subset_preimage :
  (univ : Set X) ×ˢ V ⊆ ff ⁻¹' V:= by
  intros p hp
  rw [Set.preimage]
  have h4 : p.1 ∈ (univ : Set X) := trivial
  have h3 : p.2 ∈ V := hp.2
  have h2 : ff ⟨p.1, p.2⟩ = p.2 := rfl
  have h0 : ff p = p.2 := rfl
  have hb : ff p ∈ V := by exact h3
  have ha : p ∈ {x | ff x ∈ V} := by exact hb
  exact ha

def PositiveY := Subtype (λ (p :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) => p.val 1 > 0)

#check (univ : Set PositiveY)

def gg : PositiveY × Y -> Y := λ ⟨x, y⟩ => y

example : gg ⁻¹' { y : ℝ | y > 0} ⊆ (univ : Set PositiveY) ×ˢ { y : ℝ | y > 0} := preimage_subset_X_times_V { y : ℝ | y > 0}

example : (univ : Set PositiveY) = {p : PositiveY | p.val.val 1 > 0} := sorry

theorem preimage_subset_X_times_Va :
  gg ⁻¹' V ⊆ (univ : Set PositiveY) ×ˢ V := sorry

theorem X_times_V_subset_preimageA :
  (univ : Set PositiveY) ×ˢ V ⊆ gg ⁻¹' V := sorry

def fn1 : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := λ (x, y) => y

example : ContinuousOn fn1 ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  have h1 : fn1 ⁻¹' V = (univ : Set PositiveY) ×ˢ V := sorry
  exact sorry

theorem continuous_MyCoordChange_on :
  ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2)
               ({ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 2 > 0 } ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := by
  intros _ _ V

  have hpreimage : (λ (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => MyCoordChange 0 1 p.1 p.2) ⁻¹' V =
   { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 2 > 0 } ×ˢ V := by
    ext p
    split
    sorry
    sorry

  sorry

theorem t01 : ContinuousOn (λ p => MyCoordChange 0 1 p.1 p.2) ((chart_excluding_minus_1.source ∩ chart_excluding_1.source) ×ˢ univ) := by
  have h1 : (chart_excluding_minus_1.source ∩ chart_excluding_1.source) = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  rw [h1, Set.union_prod]
  intro p hp
  cases hp with
  | inl hpos =>
    obtain ⟨h_xpos, _⟩ := hpos
    sorry
  | inr hneg =>
    obtain ⟨h_xneg, _⟩ := hneg
    sorry

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

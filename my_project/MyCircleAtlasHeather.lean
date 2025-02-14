import Mathlib

open Bundle Topology MulAction Set
open Complex

def S1 : Type := Submonoid.unitSphere ℂ
deriving TopologicalSpace

noncomputable def U := chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp 0 : Circle)
noncomputable def V := chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp Real.pi : Circle)

noncomputable
def chart_at_S1_excluding_1 : PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1)) := U
noncomputable
def chart_at_S1_excluding_minus_1 : PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1)) := V

#check {x : Circle | x ≠ (Circle.exp 0 : Circle)}

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)⟩

#check stereographic
#check stereographic'

theorem chartAt_source (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (chartAt (EuclideanSpace ℝ (Fin 1)) y).source = (stereographic' 1 (-y)).source := rfl

theorem mem_chartAt_source (y x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (h : x ≠ -y) :
    x ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) y).source := by
  rw [chartAt_source, stereographic'_source]
  exact Set.mem_compl_singleton_iff.mpr h

def Circle.toEuclidean (z : Circle) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have h1 : Complex.abs z ^ 2 = 1 := by
   rw [Circle.abs_coe z, pow_two, mul_one]
  have h2 : Complex.abs z ^ 2 = Complex.normSq z := Complex.sq_abs z
  have h3 : normSq z = z.val.re * z.val.re + z.val.im * z.val.im :=  Complex.normSq_apply z
  have hb :  (z.val.re)^2 + (z.val.im)^2 = z.val.re * z.val.re + z.val.im * z.val.im := by rw [sq z.val.re, sq z.val.im]
  have h4 : (z.val.re)^2 + (z.val.im)^2 = 1 := by
    calc
     (z.val.re)^2 + (z.val.im)^2 = z.val.re * z.val.re + z.val.im * z.val.im := hb
    _ = normSq z := by rw [<-h3]
    _ = abs z ^ 2 := by rw [<-h2]
    _ = 1 := by exact h1

  have h5 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} :=
   EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)

  have h6 : ![((z.val.re) : ℝ), ((z.val.im) : ℝ)] ∈ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    rw [h5]
    have g1 : ![(z.val).re, (z.val).im] ∈ {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by simp [h4]
    exact g1

  exact ⟨![(z.val.re), (z.val.im)], h6⟩

def Circle.fromEuclidean (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : Circle := by
  let ⟨x, h⟩ := p
  have h1 : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := h
  have h2 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} :=
   EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h3 : x ∈ {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    rw [h2] at h1
    exact h1
  have h4 : ∑ i : Fin 2, x i ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by simp
  have h5 : ∑ i : Fin 2, x i ^ 2 = 1 ^ 2 := by exact h3

  have h6 : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    calc
     x 0 ^ 2 + x 1 ^ 2 = ∑ i : Fin 2, x i ^ 2 := by rw[<-h4]
     _ = 1 ^ 2 := by exact h5
     _ = 1 := by simp

  have h6a : x 0 * x 0 + x 1 * x 1 = 1 := by
    simp only [pow_two] at h6
    exact h6

  have h7 : Complex.abs (Complex.mk (x 0) (x 1)) = 1 := by
    simp [Complex.abs]
    exact h6a

  have h8 : Complex.mk (x 0) (x 1) ∈ Submonoid.unitSphere ℂ := by
    simp [Submonoid.unitSphere]
    exact h7

  exact ⟨Complex.mk (x 0) (x 1), by exact h8⟩

example (z : Circle) : Circle.fromEuclidean (Circle.toEuclidean z) = z := by exact sorry
example (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : Circle.toEuclidean (Circle.fromEuclidean p) = p := by exact sorry

noncomputable
def Mobius : FiberBundleCore (Fin 2) S1 (EuclideanSpace ℝ (Fin 1)) :=
{
  baseSet := λ i => if i = 0 then chart_at_S1_excluding_minus_1.source
                             else chart_at_S1_excluding_1.source,

  -- isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  isOpen_baseSet := by
    intro i
    dsimp only
    split
    · exact chart_at_S1_excluding_minus_1.open_source
    · exact chart_at_S1_excluding_1.open_source

  indexAt := λ x => if re x.val < 0 then 0 else 1,

  -- mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  mem_baseSet_at := by
    intro x
    let z := Circle.toEuclidean x
    let m1 := Circle.toEuclidean (Circle.exp 0)
    let m2 := Circle.toEuclidean (Circle.exp Real.pi)
    have h1 : -m2 = m1 := sorry
    have h2 : -m1 = m2 := sorry
    have ha : z ≠ m1 -> z ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) (m2)).source :=
      h1 ▸ mem_chartAt_source m2 z
    have hb : z ≠ m2 -> z ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) (m1)).source :=
      h2 ▸ mem_chartAt_source m1 z

    have hc : re x.val < 0 -> x ≠ Circle.exp 0 := sorry
    have hd : re x.val ≥ 0 -> x ≠ Circle.exp 1 := sorry

    set indexAt : S1 -> Fin 2 := λ x => if re x.val < 0 then 0 else 1
    set baseSet : Fin 2 -> Set S1:= λ i => if i = 0 then chart_at_S1_excluding_minus_1.source
                                            else chart_at_S1_excluding_1.source

    unfold indexAt baseSet
    by_cases h : (x.val).re < 0
    rw [if_pos h]
    rw [if_pos rfl]
    have hc : z ≠ m1 := sorry
    have g1 : z ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) m2).source := by exact ha hc
    have k1 : x ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp Real.pi)).source := sorry
    exact k1
    have ga : chart_at_S1_excluding_minus_1 = chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp Real.pi : Circle) := rfl
    rw [if_neg h]
    have hd : z ≠ m2 := sorry
    have g2 : z ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) m1).source := by exact hb hd
    have k2 : x ∈ (chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp 0)).source := sorry
    exact k2,

  coordChange := sorry,
  coordChange_self := sorry,
  continuousOn_coordChange := sorry,
  coordChange_comp := sorry
}

def north_pole : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨ ![0, 0, 1], by simp [Real.sqrt_eq_rpow, EuclideanSpace.norm_eq, Fin.sum_univ_succ] ⟩

#check stereographic'
#check (finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1)

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)⟩

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)⟩

def north_polea : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  ⟨ ![0, 1], by simp [Real.sqrt_eq_rpow, EuclideanSpace.norm_eq, Fin.sum_univ_succ] ⟩

#check stereographic' 2 (-north_pole)

#check ((stereographic' 1 (-north_polea)) :
  PartialHomeomorph (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1))).source

def north_pole2 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  ⟨ ![0, 1], by simp [Real.sqrt_eq_rpow, EuclideanSpace.norm_eq, Fin.sum_univ_succ] ⟩

#check ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle

theorem foo : (1 : ℂ) ∈ Submonoid.unitSphere ℂ := by
  have h1 : (1 : ℂ) ∈ Metric.sphere 0 1 ↔ dist (1 : ℂ) 0 = 1 := Metric.mem_sphere
  have h4 : dist (1 : ℂ) 0 = 1 := by simp
  exact h1.mpr h4

#check chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp 0 : Circle)

example (y : ℂ) : y ∈ Metric.sphere 0 1 ↔ dist y 0 = 1 := Metric.mem_sphere

#check stereographic'_source (-north_pole2)

#check {x | x ≠ -north_pole2}

#check (north_pole2 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
#check (stereographic' 1 (-north_pole2)).source

noncomputable def U := chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp 0 : Circle)
noncomputable def V := chartAt (EuclideanSpace ℝ (Fin 1)) (Circle.exp Real.pi : Circle)

noncomputable
def chart_at_S1_excluding_1 : PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1)) := U
noncomputable
def chart_at_S1_excluding_minus_1 : PartialHomeomorph S1 (EuclideanSpace ℝ (Fin 1)) := V

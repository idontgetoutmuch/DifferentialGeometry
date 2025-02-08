import Mathlib

open Bundle Topology MulAction Set

structure GBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B] (F : Type*)
    [TopologicalSpace F] (G : Type*) [Group G] [MulAction G F] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (baseSet i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ baseSet (indexAt x)
  coordChange : ι → ι → B → F → F
  coordChange_self : ∀ i, ∀ x ∈ baseSet i, ∀ v, coordChange i i x v = v
  continuousOn_coordChange : ∀ i j,
    ContinuousOn (fun p : B × F => coordChange i j p.1 p.2) ((baseSet i ∩ baseSet j) ×ˢ univ)
  coordChange_comp : ∀ i j k, ∀ x ∈ baseSet i ∩ baseSet j ∩ baseSet k, ∀ v,
    (coordChange j k x) (coordChange i j x v) = coordChange i k x v
  coordChange_structure_group : ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∃ g : G, ∀ v : F, coordChange i j x v = g • v

/- Let's try this out with the circle as the base space, the real line as the fibre and the trivial group
(the only element is the identity) which btw shows that this is a trivial bundle. With the möbius bundle,
when we are able to specify it, the structure group would have to contain 2 elements to capture the twist.

But first we start with ℝˣ as the structure group!
 -/

noncomputable
def ioo : GBundleCore (atlas (EuclideanSpace ℝ (Fin 1)) Circle) Circle ℝ ℝˣ where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart (EuclideanSpace ℝ (Fin 1))
  mem_baseSet_at := mem_chart_source (EuclideanSpace ℝ (Fin 1))
  coordChange i j x v := v
  coordChange_self _ _ _ _ := rfl
  continuousOn_coordChange i j := continuous_snd.continuousOn
  coordChange_comp _ _ _ _ _ _ := rfl
  coordChange_structure_group := by
    intro i j x hx
    have h1 : ∃ g : ℝˣ, ∀ v : ℝ, v = g • v := by
      existsi 1
      intro v
      have h2 : (1 : ℝ) • v = v := one_smul ℝ v
      exact h2.symm
    exact h1

open MulAction Set

open LinearMap Matrix UnitaryGroup

instance : MulAction (orthogonalGroup (Fin n) ℝ) (Fin n -> ℝ) where
  smul := λ g x => g.1.mulVec x
  one_smul := λ x => by
    have h1 : (1 : orthogonalGroup (Fin n) ℝ).1.mulVec x = x := by
      simp [Matrix.mulVec_one]
    exact h1
  mul_smul := λ f g x => by
    show (f * g).1.mulVec x = f.1.mulVec (g.1.mulVec x)
    simp [Matrix.mulVec_mulVec]

#check atlas (EuclideanSpace ℝ (Fin 1)) Circle
#check chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle)
#check (chartAt (EuclideanSpace ℝ (Fin 1)) (1 : Circle)).source
#check PartialHomeomorph
#print chartAt
#check Subtype
#synth TopologicalSpace ℂ
#check Iic
#check Ioo (0 : ℝ) (0 : ℝ)
#check Circle.exp.toFun
#check Circle.exp.toFun 1
#check ((Circle.exp.toFun 1) : Circle)
#check λ r => Complex.exp (r * Complex.I) ∈ Submonoid.unitSphere ℂ
#check ((Circle.exp.toFun 1) : Circle) ∈ Circle <-> mem_circle_iff_abs


open Complex

def S1 : Type := Submonoid.unitSphere ℂ
deriving TopologicalSpace

theorem bar (r : ℝ) : exp (r * I) ∈ Submonoid.unitSphere ℂ := by
  have h1 : abs (exp (r * I)) = 1 := abs_exp_ofReal_mul_I r
  have h2 : exp (r * I) ∈ Metric.sphere 0 1 ↔ ‖exp (r * I)‖ = 1 := mem_sphere_zero_iff_norm
  have h3 : ‖exp (r * I)‖ = abs (exp (r * I)) := rfl
  have h5 : ‖exp (r * I)‖ = 1 := by
    rw [h3, h1]
  have h6 : exp (r * I) ∈ Metric.sphere 0 1 := h2.2 h5
  have h7 : exp (r * I) ∈ Submonoid.unitSphere ℂ := h6
  exact h7

def chart_at_S1_excluding_1 : PartialHomeomorph S1 ℝ :=
{
  toFun := λ z => arg z.val,
  invFun := λ r => ⟨exp (r * Complex.I), bar r⟩,
  source := Ioo (0 : S1) (2 * pi),
  target := Ioi 0,
  continuousOn_toFun := continuous_arg,
  continuousOn_invFun := continuous_exp,
}

-- Second chart for S^1 excluding -1, mapping argument (π, 2π)
def chart_at_S1_excluding_minus_1 : PartialHomeomorph S1 ℝ :=
{
  to_fun := λ z, complex.arg z,  -- The coordinate map is the argument of the complex number
  inv_fun := λ x, exp (x * complex.I),  -- The inverse map is the exponential of the angle
  source := set.Ioo π (2 * π),  -- This is (π, 2π) excluding -1
  target := Ioi 0,  -- The target is ℝ (open ray starting at 0)
  continuous_to_fun := continuous_arg,  -- Argument is continuous
  continuous_inv_fun := continuous_exp,  -- Exponential is continuous
}

noncomputable
def joo : GBundleCore (atlas (EuclideanSpace ℝ (Fin 1)) Circle) Circle (Fin 1 -> ℝ) (orthogonalGroup (Fin 1) ℝ) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart (EuclideanSpace ℝ (Fin 1))
  mem_baseSet_at := mem_chart_source (EuclideanSpace ℝ (Fin 1))
  coordChange i j x v := v
  coordChange_self _ _ _ _ := rfl
  continuousOn_coordChange i j := continuous_snd.continuousOn
  coordChange_comp _ _ _ _ _ _ := rfl
  coordChange_structure_group := by sorry

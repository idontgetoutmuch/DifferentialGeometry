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

open Complex

def S1 : Type := Submonoid.unitSphere ℂ
deriving TopologicalSpace

theorem exp_mem_unitSphere (r : ℝ) : exp (r * I) ∈ Submonoid.unitSphere ℂ := by
  have h1 : abs (exp (r * I)) = 1 := abs_exp_ofReal_mul_I r
  have h2 : exp (r * I) ∈ Metric.sphere 0 1 ↔ ‖exp (r * I)‖ = 1 := mem_sphere_zero_iff_norm
  have h3 : ‖exp (r * I)‖ = abs (exp (r * I)) := rfl
  have h5 : ‖exp (r * I)‖ = 1 := by
    rw [h3, h1]
  have h6 : exp (r * I) ∈ Metric.sphere 0 1 := h2.2 h5
  have h7 : exp (r * I) ∈ Submonoid.unitSphere ℂ := h6
  exact h7

theorem arg_exp_of_range (r : ℝ) (hr : -Real.pi < r ∧ r < Real.pi) :
  arg (exp (r * I)) = r := by
  have h_in_range : r ∈ Ioo (-Real.pi) Real.pi := hr
  have h_in_range : r ∈ Ioc (-Real.pi) Real.pi := by
    exact Ioo_subset_Ioc_self h_in_range
  have bik : arg (exp (r * I)) = toIocMod (mul_pos two_pos Real.pi_pos) (-Real.pi) r := Complex.arg_exp_mul_I r
  have bil : toIocMod (mul_pos two_pos Real.pi_pos) (-Real.pi) r = r ↔ r ∈ Ioc (-Real.pi) ((-Real.pi) + (2 * Real.pi)) :=
    toIocMod_eq_self (mul_pos two_pos Real.pi_pos)
  have h_eq : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have bin : toIocMod (mul_pos two_pos Real.pi_pos) (-Real.pi) r = r ↔ r ∈ Ioc (-Real.pi) Real.pi := by
    rwa [h_eq] at bil
  have bim : toIocMod (mul_pos two_pos Real.pi_pos) (-Real.pi) r = r := bin.mpr h_in_range
  have crk : arg (exp (r * I)) = r := by rw [bik, bim]
  exact crk

noncomputable
def chart_at_S1_excluding_minus_1 : PartialHomeomorph S1 ℝ :=
{
  toFun := λ z => arg z.val,
  invFun := λ r => ⟨exp (r * Complex.I), exp_mem_unitSphere r⟩,
  source := {z : S1 | arg z.val ∈ Ioo (-Real.pi) (Real.pi)},
  target := Ioo (-Real.pi) (Real.pi),
  map_source' := λ z hz => hz,
  map_target' := λ r hr => by
    have h1 : (exp (r * I)).arg = r := arg_exp_of_range r hr
    have h2a : (-Real.pi) < r := hr.1
    have h2b : r < Real.pi := hr.2
    have h3a : (-Real.pi) < (exp (r * I)).arg := by
      rw [h1]
      exact h2a
    have h3b : (exp (r * I)).arg < (Real.pi) := by
      rw [h1]
      exact h2b
    exact ⟨(h3a : (-Real.pi) < (exp (r * I)).arg), (h3b : (exp (r * I)).arg < (Real.pi))⟩,
  left_inv' := λ z hz => by
    have h0 : (Complex.abs z.val) * exp ((z.val).arg * I) = z.val := by exact abs_mul_exp_arg_mul_I z.val
    have h4 : z.val ∈ Submonoid.unitSphere ℂ := by exact z.prop
    have h5 : z.val ∈ Metric.sphere 0 1 ↔ ‖z.val‖ = 1 := mem_sphere_zero_iff_norm
    have h7 : z.val ∈ Metric.sphere 0 1 := h4
    have h6 : ‖z.val‖ = 1 := by rwa [h5] at h7
    have h8 : ‖z.val‖ * exp ((z.val).arg * I) = z.val := by exact abs_mul_exp_arg_mul_I z.val
    have h9 : z.val = exp ((z.val).arg * I) := by
      calc z.val = ‖z.val‖ * exp ((z.val).arg * I) := by rw [h8]
                _ = (1 : ℝ) *  exp ((z.val).arg * I) := by rw [h6]
                _ = (1 : ℂ) * exp ((z.val).arg * I) := by norm_cast
                _ = exp ((z.val).arg * I) := by rw [one_mul]
    have h3 : (fun r => ⟨exp (r * I), by exact exp_mem_unitSphere r⟩) (z.val).arg = z := by
      apply Subtype.ext
      exact h9.symm
    exact h3
  right_inv' := λ r hr => by
   have h1 : arg (exp (r * I)) = r := arg_exp_of_range r hr
   exact h1
  open_source := by
    exact sorry,
  open_target := isOpen_Ioo,
  continuousOn_toFun  := (sorry : (ContinuousOn (λ z => arg z.val)) {z : S1 | arg z.val ∈ Ioo (-Real.pi) (Real.pi)}),
  continuousOn_invFun := sorry
}

variables (z : S1)

#check z.1
#check z.2

#check ((λ r => ⟨exp (r * Complex.I), exp_mem_unitSphere r⟩) : ℝ → ↥(Submonoid.unitSphere ℂ))
#check Complex.arg_exp_mul_I
#check toIocMod (mul_pos two_pos Real.pi_pos) (-Real.pi) (Real.pi / 4) = (Real.pi / 4)
#check toIocMod (mul_pos two_pos Real.pi_pos) (-Real.pi) (Real.pi / 4) = (Real.pi / 4)
#check toIocMod_eq_self

noncomputable
def chart_at_S1_excluding_1 : PartialHomeomorph S1 ℝ :=
{
  toFun := λ z => arg z.val,
  invFun := λ r => ⟨exp (r * Complex.I), exp_mem_unitSphere r⟩,
  source := {z : S1 | arg z.val ∈ Ioo 0 (2 * Real.pi)},
  target := Ioo 0 (2 * Real.pi),
  map_source' := λ z hz => hz,
  map_target' := λ r hr => ⟨sorry, sorry⟩,
                 -- λ r hr => ⟨exp (r * Complex.I), by simp; exact hr⟩,
  -- left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
  -- left_inv' := λ z hz => Subtype.ext (by rw [baz z hz]),
  left_inv' := λ z hz => sorry
  right_inv' := λ r hr => sorry, -- by simp [hr],
  open_source := sorry, -- Needs proof that {z : S1 | arg z.val ∈ Ioo 0 (2 * π)} is open
  open_target := isOpen_Ioo,
  continuousOn_toFun := sorry, -- Needs proof that `arg` is continuous on `source`
  continuousOn_invFun := sorry  -- Needs proof that `exp` is continuous on `target`
}

def source : Set S1 := {z : S1 | arg z.val ∈ Ioo (-Real.pi) Real.pi}

#check ContinuousAt arg

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

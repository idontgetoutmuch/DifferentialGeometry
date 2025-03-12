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

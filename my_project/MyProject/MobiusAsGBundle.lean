import Mathlib
import «MyProject».Mobius
import «MyProject».GBundleDefs

open Bundle Topology MulAction Set

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

-- instance : MulAction (orthogonalGroup (Fin n) ℝ) (Fin n -> ℝ) where
--   smul := λ g x => g.1.mulVec x
--   one_smul := λ x => by
--     have h1 : (1 : orthogonalGroup (Fin n) ℝ).1.mulVec x = x := by
--       simp [Matrix.mulVec_one]
--     exact h1
--   mul_smul := λ f g x => by
--     show (f * g).1.mulVec x = f.1.mulVec (g.1.mulVec x)
--     simp [Matrix.mulVec_mulVec]

instance : MulAction (orthogonalGroup (Fin n) ℝ) (EuclideanSpace ℝ (Fin n)) where
  smul := λ g x => g.1.mulVec x
  one_smul := λ x => by
    have h1 : (1 : orthogonalGroup (Fin n) ℝ).1.mulVec x = x := by
      simp [Matrix.mulVec_one]
    exact h1
  mul_smul := λ f g x => by
    show (f * g).1.mulVec x = f.1.mulVec (g.1.mulVec x)
    simp [Matrix.mulVec_mulVec]

lemma orthGroupInv {n} {v : (EuclideanSpace ℝ (Fin n))} : (-1 : (orthogonalGroup (Fin n) ℝ)) • v = -v := by
 have h1 : (-1 : (orthogonalGroup (Fin n) ℝ)) • v = (-1 : (orthogonalGroup (Fin n) ℝ)).1.mulVec v := rfl
 have h2 : -1 *ᵥ v = -(1 *ᵥ v) := Matrix.neg_mulVec v (1 : Matrix (Fin n) (Fin n) ℝ)
 have h3 : -(1 *ᵥ v) = -v := by simp
 calc (-1 : (orthogonalGroup (Fin n) ℝ)) • v = (-1 : (orthogonalGroup (Fin n) ℝ)).1.mulVec v := rfl
      _ = -(1 *ᵥ v) := Matrix.neg_mulVec v (1 : Matrix (Fin n) (Fin n) ℝ)
      _ = -v := by simp

lemma orthGroup1 (a : ℝ) : !![a] ∈ Matrix.orthogonalGroup (Fin 1) ℝ <-> a = 1 ∨ a = -1 := by
  have h1 : !![a] ∈ Matrix.orthogonalGroup (Fin 1) ℝ ↔ !![a] * star !![a] = 1 := Matrix.mem_orthogonalGroup_iff (Fin 1) ℝ
  have h2 : !![a] ∈ Matrix.orthogonalGroup (Fin 1) ℝ <-> !![a * a] = 1 := by
    rw [(mulᵣ_eq _ _).symm] at h1
    exact h1
  have h3 : !![1] = (1 : Matrix (Fin 1) (Fin 1) ℝ) := etaExpand_eq 1
  have h4 : !![a] ∈ Matrix.orthogonalGroup (Fin 1) ℝ <-> !![a * a] = !![1] := by
    rw [h3.symm] at h2
    exact h2
  have h5 : !![a * a] = !![1] ↔ a * a = 1 := by
    apply Iff.intro
    · intro h
      have := Matrix.ext_iff.mpr h 0 0
      exact this
    · intro h
      apply Matrix.ext
      intros i j
      fin_cases i; fin_cases j
      exact h
  have he : !![a] ∈ orthogonalGroup (Fin 1) ℝ ↔ a * a = 1 := Iff.trans h4 h5
  have hd : a * a = 1 ↔ a = 1 ∨ a = -1 := mul_self_eq_one_iff
  have hf : !![a] ∈ orthogonalGroup (Fin 1) ℝ ↔ a = 1 ∨ a = -1 := Iff.trans he hd
  exact hf

lemma orthGroup1' {m} : m ∈ Matrix.orthogonalGroup (Fin 1) ℝ <-> m = 1 ∨ m = -1 := sorry

theorem MyCoordChange_structure_group : ∀ (i j : Fin 2),
  ∀ x ∈ (fun i ↦ if i = 0 then U.source else V.source) i ∩ (fun i ↦ if i = 0 then U.source else V.source) j,
    ∃ g : (orthogonalGroup (Fin 1) ℝ), ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange i j x v = g • v := by
    intro i j x hx
    have h0 : x ∈ (fun i ↦ if i = 0 then U.source else V.source) i ∩ (fun i ↦ if i = 0 then U.source else V.source) j := hx
    fin_cases i
    · fin_cases j
      . have h1 : ∃ g : (orthogonalGroup (Fin 1) ℝ), ∀ v : (EuclideanSpace ℝ (Fin 1)), v = g • v := by
            existsi 1
            intro v
            have h2 : (1 : (orthogonalGroup (Fin 1) ℝ)) • v = v := one_smul (orthogonalGroup (Fin 1) ℝ) v
            exact h2.symm
        exact h1
      · have h2 : ∃ (g : ↥(orthogonalGroup (Fin 1) ℝ)), ∀ (v : EuclideanSpace ℝ (Fin 1)),
          MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = g • v := by
            by_cases h : (x.val 1) > (0 : ℝ)
            . existsi 1
              intro v
              have h5 : MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = (1 : (orthogonalGroup (Fin 1) ℝ)) • v := by
                calc MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = if (x.val 1) > 0 then v else -v := rfl
                     _ = v := if_pos h
                     _ = (1 : (orthogonalGroup (Fin 1) ℝ)) • v := (one_smul (orthogonalGroup (Fin 1) ℝ) v).symm
              exact h5
            . exists -1
              intro v
              have h5 : MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = (-1 : (orthogonalGroup (Fin 1) ℝ)) • v := by
                calc MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = if (x.val 1) > 0 then v else -v := rfl
                     _ = -v := if_neg h
                     _ = (-1 : (orthogonalGroup (Fin 1) ℝ)) • v := by exact orthGroupInv.symm
              exact h5
        exact h2
    · fin_cases j
      · exact sorry
      · exact sorry

noncomputable
def MobiusAsGBundle : GBundleCore (Fin 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) (orthogonalGroup (Fin 1) ℝ) where
  baseSet := λ i => if i = 0 then U.source
                             else V.source

  isOpen_baseSet := by
    intro i
    dsimp only
    split
    · exact U.open_source
    · exact V.open_source

  indexAt := λ x => if (x.val 0) > 0 then 0 else 1

  mem_baseSet_at := my_mem_baseSet_at

  coordChange := MyCoordChange

  coordChange_self := MyCoordChange_self

  continuousOn_coordChange := by
    intro i j
    exact MyContinuousOn_coordChange i j

  coordChange_comp := MyCoordChange_comp

  coordChange_structure_group := MyCoordChange_structure_group

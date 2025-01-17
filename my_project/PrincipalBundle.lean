import Mathlib

open Manifold

open SmoothManifoldWithCorners

open MulAction

open Bundle

lemma foo {G P : Type*} (p q : P)
[Group G]
[MulAction G P] : (orbitRel G P) q p ↔ ∃ (g : G), g • p = q := by
  have h3 : orbitRel G P q p ↔ q ∈ orbit G p := by apply orbitRel_apply
  have h4 : q ∈ orbit G p ↔ ∃ g : G, g • p = q := by apply mem_orbit_iff
  have h5 : orbitRel G P q p ↔ ∃ g : G, g • p = q := by
    rw [h3, h4]
  exact h5

example {G B : Type*} {E : B → Type*} (k n : ℕ)
[TopologicalSpace B]
[ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
[TopologicalSpace G]
[ChartedSpace (EuclideanSpace ℝ (Fin k)) G]
[Group G]
[MulAction G P]
[TopologicalGroup G]
[TopologicalSpace (TotalSpace G E)]
[(b : B) → TopologicalSpace (E b)]
[LieGroup (𝓡 k) G]
[FiberBundle G E] (p q r : P) :
  true := by

    have h_refl : orbitRel G P p p := by
      have hr1 : orbitRel G P p p ↔ ∃ g : G, g • p = p := by
        apply foo p p
      have hr2 : ∃ g : G, g • p = p := Exists.intro 1 (one_smul _ _)
      apply hr1.mpr hr2

    have h_symm : orbitRel G P p q -> orbitRel G P q p := by
      intro h
      have hs1 : ∃ (g : G), g • q = p := by
        apply (foo q p).mp h
      have hs2 : ∃ (g : G), g • p = q :=
        Exists.elim hs1 (λ g => λ hg =>
         by
          have hs2a : g • q = p := hg
          have hs2b :  q = g⁻¹ • p := by
            calc q = (1 : G) • q := by apply (Eq.symm (one_smul _ _))
            _ = (g⁻¹ * g) • q := by rw [inv_mul_cancel]
            _ = g⁻¹ • (g • q) := by apply (mul_smul g⁻¹ g q)
            _ = g⁻¹ • p := by rw [hs2a]
          exact Exists.intro g⁻¹ (Eq.symm hs2b))
      have hs3 : orbitRel G P q p := by
        apply (foo p q).mpr hs2
      exact hs3

    have h_tran : orbitRel G P p q -> orbitRel G P q r -> orbitRel G P p r := by
      intro h1 h2
      have ht1 : ∃ (g1 : G), g1 • q = p := by
        apply (foo q p).mp h1
      have ht2 : ∃ (g2 : G), g2 • r = q := by
        apply (foo r q).mp h2
      let ⟨g1, hx⟩ := ht1
      let ⟨g2, hy⟩ := ht2
      have ht3: (g1 * g2) • r = p := by
        calc (g1 * g2) • r = g1 • (g2 • r) := by apply (mul_smul g1 g2 r)
              _ = g1 • q := by rw [hy]
              _ = p := by apply hx
      have ht4 : ∃ (g3 : G), g3 • r = p := by
        exact Exists.intro (g1 * g2) ht3
      have ht5 : orbitRel G P p r := by
        apply (foo r p).mpr ht4
      exact ht5

    trivial

def f (x : ℂ) : Fin 2 -> ℝ := λ i => if i = 0 then x.re else x.im
def g (x : Fin 2 -> ℝ) : ℂ := Complex.mk (x 0) (x 1)

lemma gf_inv_ext (x : ℂ) : g (f x) = x := by
  simp [f, g]

def Circle.smul (x : Circle) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  f (x * (g z))

lemma Circle.one_smul : Circle.smul (1 : Circle) z = z := by
  ext i
  simp [Circle.smul, g, Complex.mk, f]
  match i with
    | Fin.mk 0 _ => simp [f, g]
    | Fin.mk 1 _ => simp [f, g]

lemma Circle.mul_smul : Circle.smul (x * y) b = Circle.smul x (Circle.smul y  b) := by
  have h1 : Circle.smul (x * y) b = f ((x * y) * g b) := by rfl
  have h2 : f ((x * y) * g b) = f (x * (y * g b)) := by rw [mul_assoc]
  have h3 : f (x * (y * g b)) = f (x * g ( f (y * g b))) := by rw [gf_inv_ext]
  have h4 : f (x * g ( f (y * g b))) = Circle.smul x (Circle.smul y b) := by rfl
  have h5 :  Circle.smul (x * y) b = Circle.smul x (Circle.smul y b) := by rw [h1, h2, h3, h4]
  exact h5

instance : MulAction Circle (Fin 2 -> ℝ) where
  mul_smul _ _ _ := Circle.mul_smul
  smul := Circle.smul
  one_smul _ := Circle.one_smul

def ξ := (λ (i : Fin 2) => if i = 0 then (1 : ℝ) else 0)

lemma bbs_mul (a b : ℂ) : Complex.abs (a * b) = Complex.abs a * Complex.abs b := by
  have hab : ‖a * b‖ = Complex.abs (a * b) := by
    rw [Complex.norm_eq_abs]
  have ha : ‖a‖ = Complex.abs a := by
    rw [Complex.norm_eq_abs]
  have hb : ‖b‖ = Complex.abs b := by
    rw [Complex.norm_eq_abs]
  calc
   Complex.abs (a * b) =  ‖a * b‖ := by exact hab.symm
   _ = ‖a‖ * ‖b‖ := by exact norm_mul a b
   _ = Complex.abs a * Complex.abs b := by rw [ha, hb]

example (x : Fin 2 → ℝ) (ξ : Fin 2 → ℝ) (h : Circle) :
  x ∈ orbit Circle ξ → (x 0)^2 + (x 1)^2 = (ξ 0)^2 + (ξ 1)^2 := by
  -- have h1 : h • ξ ∈ orbit Circle ξ := mem_orbit _ _
  -- have h2 : ξ ∈ orbit Circle ξ := mem_orbit_self _
  intro hx
  have h3 : orbit Circle ξ = Set.range (λ m : Circle => m • ξ) := by rfl
  have h4 : Set.range (λ m : Circle => m • ξ) = {x | ∃ y : Circle, y • ξ = x} := by rfl
  have h5 : x ∈ orbit Circle ξ ↔ ∃ y : Circle, y • ξ = x := by rfl
  have h6 : ∀ z : Circle, z • ξ = f (z * (g ξ)) := by
    intro z
    exact rfl
  have h7 : x ∈ orbit Circle ξ ↔ ∃ y : Circle, f (y * (g ξ)) = x := by
    rw [h3, h4]
    simp [h6]
  obtain ⟨y, hy⟩ := h7.mp hx -- Extract `y` such that `f (y * (g ξ)) = x`
  rw [← hy] -- Replace `x` with `f (y * (g ξ))`
  have hz : ∀ y, (f (y * (g ξ)) 0)^2 + (f (y * (g ξ)) 1)^2 = (y * (g ξ)).re^2 + (y * (g ξ)).im^2 := by
    intro y
    rfl
  rw [hz y] -- Replace the LHS with `(y * (g ξ)).re^2 + (y * (g ξ)).im^2`

  have hy : ∀ a, a.re^2 + a.im^2 = (Complex.abs a)^2 := by
    intro a
    rw [<-Complex.normSq_eq_abs, Complex.normSq_apply, sq, sq]

  rw [hy (y * (g ξ))] -- Replace with `(Complex.abs (y * (g ξ)))^2`
  have h9 : Complex.abs (y * (g ξ)) = Complex.abs y * Complex.abs (g ξ) := by rw [bbs_mul]

  rw [h9] -- Replace `Complex.abs (y * (g ξ))` with `Complex.abs y * Complex.abs (g ξ)`
  have ha : ∀ y : Circle, Complex.abs y = 1 := by
    exact Circle.abs_coe -- Circle.norm_eq_one y
  rw [ha y] -- Replace `Complex.abs y` with `1`
  simp -- Simplify to `(Complex.abs (g ξ))^2`

  have h_nonneg : 0 ≤ ξ 0 * ξ 0 + ξ 1 * ξ 1 := by
    exact add_nonneg (mul_self_nonneg (ξ 0)) (mul_self_nonneg (ξ 1))

  have hb : Complex.abs (g ξ)^2 = (ξ 0)^2 + (ξ 1)^2 := by
    dsimp [g, Complex.abs, Complex.normSq, Complex.re, Complex.im]
    simp [pow_two]
    exact Real.mul_self_sqrt h_nonneg

  rw [hb] -- Replace `Complex.abs (g ξ)^2` with `(ξ 0)^2 + (ξ 1)^2`

#synth LieGroup (𝓡 1) Circle

variables {G P : Type*} (p q : P)
[Group G]
[MulAction G P]

#check ((orbitRel G P) : Setoid P)
#check Quotient (orbitRel G P)
#check orbitRel G P
#check (orbitRel G P).r
#check (orbitRel G P).r p q
#check mem_orbit_symm
#check mem_orbit_self

#check (1 : Circle).1.re
#check (1 : Circle).2

variable [Ring R] [AddCommMonoid M] [Module R M] (r : R) (N : Submodule R M) (m : M) (n : N)
#check m + r • n

#check orbit Circle (λ (i : Fin 2) => if i = 0 then (3.14 : ℝ) else (2.17 : ℝ))
#check orbit Circle (λ (i : Fin 2) => if i = 0 then (3.14 : ℝ) else (2.17 : ℝ))
#check stabilizer Circle (λ (i : Fin 2) => if i = 0 then (3.14 : ℝ) else (2.17 : ℝ))
#check mem_orbit Circle
#check mem_orbit_self

#check QuotientAction Circle

#check polarCoord
#check Complex.exp_add
#check Complex.abs_abs
#check norm_mul (g ξ)
#check  ‖ξ‖
#synth NormedDivisionRing ℂ
#check norm (g ξ)
#check Complex.norm_eq_abs

example (a b : ℂ) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
 exact norm_mul a b

 example : ‖g ξ‖ = Complex.abs (g ξ) := by
  rw [Complex.norm_eq_abs]

variable [SMul Circle (Fin 2 → ℝ)] [MulAction Circle (Fin 2 → ℝ)] (h : Circle) (x : Fin 2 → ℝ)
#check h • x
#check Circle.smul h x
#check ℂ

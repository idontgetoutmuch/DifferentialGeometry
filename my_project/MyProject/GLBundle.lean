import Mathlib

#synth TopologicalSpace (GL (Fin 1) ℝ)

#synth ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin (1 + 1))) 1)

variable
(n : ℕ)
(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
(x' : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

#check contDiffOn_ext_coord_change x x'

open SmoothManifoldWithCorners
open scoped Manifold

#check ContDiffOn ℝ ⊤ ((extChartAt (𝓡 n) x').symm ≫ extChartAt (𝓡 n) x) sorry

example : ContDiffOn ℝ ⊤
          ((extChartAt (𝓡 n) x').symm ≫ extChartAt (𝓡 n) x)
          ((extChartAt (𝓡 n) x').symm.trans (extChartAt (𝓡 n) x)).source
 := contDiffOn_ext_coord_change x x'

#check ((extChartAt (𝓡 n) x').symm ≫ extChartAt (𝓡 n) x)
#check mfderiv
#check fderiv
#check MDifferentiable

variable
(y : EuclideanSpace ℝ (Fin n))

#check (contDiffGroupoid ⊤) (𝓡 n)
#check HasGroupoid (EuclideanSpace ℝ (Fin n)) ((contDiffGroupoid ⊤) (𝓡 n))
#check HasGroupoid.compatible

#check fderiv ℝ ((extChartAt (𝓡 n) x').symm ≫ extChartAt (𝓡 n) x).toFun y
#check LinearMap.toMatrix
#check LinearMap.toMatrix (sorry : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
                          (sorry : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))

noncomputable
example : true := by
  have h1 : (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    LinearMap.toMatrix (sorry : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
                       (sorry : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
  let foo n (f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n) ) f.toLinearMap
  let bar := fderiv ℝ ((extChartAt (𝓡 n) x').symm ≫ extChartAt (𝓡 n) x).toFun y
  let baz := foo n bar
  exact sorry

noncomputable
example {n : ℕ} (f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  let B := Pi.basisFun ℝ (Fin n) -- Standard basis
  LinearMap.toMatrix B B f.toLinearMap

#check Matrix.GeneralLinearGroup.mk'

noncomputable
def GLBundle {n : ℕ} : FiberBundleCore
  (atlas (EuclideanSpace ℝ (Fin n)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
  (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  (GL (Fin n) ℝ)
  where

  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart (EuclideanSpace ℝ (Fin n))
  mem_baseSet_at := mem_chart_source (EuclideanSpace ℝ (Fin n))

  coordChange i j x v := by
    let ii := i.1
    have h1 : i.1 ∈ (atlas (EuclideanSpace ℝ (Fin n)) (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
      exact sorry
    have h2 : i.1 ∈ atlas (EuclideanSpace ℝ (Fin n)) ↑(Metric.sphere 0 1) := i.2
    have h3 : j.1 ∈ atlas (EuclideanSpace ℝ (Fin n)) ↑(Metric.sphere 0 1) := j.2
    have h4 :  (i).symm ≫ₕ ↑j ∈ G := HasGroupoid.compatible h2 h3

    let bar := (fderiv ℝ (j.1 ∘ (i.1).symm) (i.1 x)).toLinearMap
    let B := Pi.basisFun ℝ (Fin n)
    let urk := LinearMap.toMatrix B B bar
    let foo := urk * v
    exact sorry

  coordChange_self := sorry

  continuousOn_coordChange := sorry

  coordChange_comp := sorry

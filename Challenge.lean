module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

public section

open Filter MeasureTheory
open scoped ENNReal

namespace Grokability

/-- The integral of the standard Gaussian density over the boundary.
Mathlib's diameter-based Hausdorff measure in dimension (k) is scaled by the
volume of the Euclidean unit (k)-ball divided by (2^k).
In dimension zero every set has empty boundary. -/
noncomputable def gaussianPerimeter : {n : ℕ} → Set (EuclideanSpace ℝ (Fin n)) → ℝ≥0∞
  | 0, _ => 0
  | k + 1, K =>
    let normalization := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) / 2 ^ k
    let density (x : EuclideanSpace ℝ (Fin (k + 1))) :=
      ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
    normalization * (∫⁻ x in frontier K, density x ∂μH[(k : ℝ)])

/-- The supremum of Gaussian perimeters over convex subsets of Euclidean n-space. -/
noncomputable def Γ (n : ℕ) : ℝ≥0∞ :=
  ⨆ (K : Set (EuclideanSpace ℝ (Fin n))) (_ : Convex ℝ K), gaussianPerimeter K

/-- Theorem 1 of Ivanisvili and Xie, *Grokability in five inequalities* (arXiv:2605.05193). -/
theorem theorem1 :
    ENNReal.ofReal (0.31258 : ℝ) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by
  sorry

end Grokability

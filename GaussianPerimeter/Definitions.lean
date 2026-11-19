module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

meta import Lean

public section

open Filter MeasureTheory
open scoped ENNReal

/- The equation compiler gives a private matcher a name derived from the
module. Elaborate the copied definition with the challenge module name so
the matcher and the definition have the same kernel declarations in both
exports. These declarations are still compiled in this solution module. -/
open Lean Elab Command in
local elab "with_challenge_matcher " declaration:command : command => do
  let originalModule := (← getEnv).mainModule
  modifyEnv (·.setMainModule `Challenge)
  try
    elabCommand declaration
  finally
    modifyEnv (·.setMainModule originalModule)

namespace GaussianPerimeter

with_challenge_matcher
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

/-- The perimeter formula in positive dimension. -/
theorem gaussianPerimeter_succ (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin (k + 1)))) :
    gaussianPerimeter K =
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) / (2 : ℝ≥0∞) ^ k) *
        (∫⁻ x in frontier K, ENNReal.ofReal
          ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2)) ∂μH[(k : ℝ)]) := by
  unfold gaussianPerimeter
  rfl

/-- The maximal perimeter bounds the perimeter of each convex set. -/
theorem gaussianPerimeter_le_Γ {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : Convex ℝ K) : gaussianPerimeter K ≤ Γ n :=
  le_iSup₂ (f := fun K _ => gaussianPerimeter K) K hK

end GaussianPerimeter

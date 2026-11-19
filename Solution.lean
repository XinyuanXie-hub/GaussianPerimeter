module

public import GaussianPerimeter.Construction
public import GaussianPerimeter.QuadratureCertificate

public section

open Filter MeasureTheory
open scoped ENNReal

namespace Grokability

/-- Theorem 1 of Ivanisvili and Xie, *Grokability in five inequalities*. -/
theorem theorem1 :
    ENNReal.ofReal (0.31258 : ℝ) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop :=
  (ENNReal.ofReal_le_ofReal gaussianLowerBound_numeric).trans
    (lowerBound_gaussianPerimeter
      (a := 6131 / 5000) (b := 2387 / 1000) (W := 6)
      (by norm_num) (by norm_num) (by norm_num))

end Grokability

module

public import GaussianPerimeter.ExpBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace GaussianPerimeter

/-- The prefactor in equation (14) for the paper's rational parameters. -/
theorem gaussianPrefactor_lower :
    (0.938393 : ℝ) ≤
      (2387 / 1000 : ℝ) * (6131 / 5000) *
        Real.exp (-((6131 / 5000 : ℝ) ^ 4) / 4) / Real.sqrt Real.pi := by
  let q : ℚ := -((6131 / 5000 : ℚ) ^ 4) / 4
  have hq : (q : ℝ) = -((6131 / 5000 : ℝ) ^ 4) / 4 := by
    norm_num [q]
  have hcert : (56825898 / 100000000 : ℚ) ≤ expLower q := by decide +kernel
  have hexp : (56825898 / 100000000 : ℝ) ≤ Real.exp (q : ℝ) := by
    have hcast : (((56825898 / 100000000 : ℚ)) : ℝ) ≤ (expLower q : ℝ) :=
      Rat.cast_le.mpr hcert
    simpa using hcast.trans (expLower_le_exp q)
  have hsqrt : Real.sqrt Real.pi ≤ (1772454 / 1000000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith [Real.pi_lt_d6]
  rw [← hq]
  calc
    (0.938393 : ℝ) ≤ (2387 / 1000 : ℝ) * (6131 / 5000) *
        (56825898 / 100000000) / (1772454 / 1000000) := by norm_num
    _ ≤ _ :=
      (div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 Real.pi_pos) hsqrt).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (Real.sqrt_nonneg _))

end GaussianPerimeter

module

public import GaussianPerimeter.LimitBound
public import GaussianPerimeter.CapAsymptotics
public import GaussianPerimeter.Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Grokability

theorem tendsto_capScale_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (capScale a) atTop (𝓝 0) := by
  have hRho : Tendsto (capRho a) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
      |>.const_mul_atTop ha
  have hSq := (tendsto_pow_atTop (Nat.succ_ne_zero 1)).comp hRho
  have hNeg : Tendsto (fun n => -(capRho a n ^ 2) / 2) atTop atBot := by
    convert hSq.const_mul_atTop_of_neg (show (-1 / 2 : ℝ) < 0 by norm_num) using 1
    ext n
    simp only [Function.comp_apply]
    ring
  have hExp := Real.tendsto_exp_atBot.comp hNeg
  have hDen := hRho.const_mul_atTop (Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.pi))
  change Tendsto (fun n => capScale a n) atTop (𝓝 0)
  simpa only [capScale, Function.comp_def, zero_mul] using
    (hExp.div_atTop hDen).mul_const (Real.exp (a ^ 4 / 4))

theorem capScale_mul_density {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi) =
      capScale a n * capRho a n * Real.exp (-a ^ 4 / 4) := by
  have hRho := capRho_pos ha hn
  have hπ : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hExp : Real.exp (a ^ 4 / 4) * Real.exp (-a ^ 4 / 4) = 1 := by
    rw [← Real.exp_add, show a ^ 4 / 4 + -a ^ 4 / 4 = 0 by ring, Real.exp_zero]
  rw [capScale]
  calc
    _ = (Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi)) *
        (Real.exp (a ^ 4 / 4) * Real.exp (-a ^ 4 / 4)) := by rw [hExp, mul_one]
    _ = _ := by field_simp

/-- The radial density observed at distance `w` from the mode. -/
@[expose] noncomputable def shiftedRadialDensity (n : ℕ) (w : ℝ) : ℝ :=
  radialDensity n (Real.sqrt ((n : ℝ) - 1) + w)

/-- The probability that one random half-space removes the point at radial
offset `w` from a distinguished facet. -/
@[expose] noncomputable def shiftedCapTail (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  if 2 ≤ n then capTail n (capThreshold a n w) else 0

theorem shiftedRadialDensity_measurable (n : ℕ) : Measurable (shiftedRadialDensity n) :=
  (radialDensity_measurable n).comp (by fun_prop)

theorem shiftedCapTail_measurable (a : ℝ) (n : ℕ) : Measurable (shiftedCapTail a n) := by
  change Measurable (fun w => shiftedCapTail a n w)
  by_cases hn : 2 ≤ n
  · simp only [shiftedCapTail, ite_eq_left hn]
    have hInt := intervalIntegral.continuous_primitive (μ := volume)
      (capProfile_continuous hn).intervalIntegrable (1 : ℝ)
    have hFlip : Continuous (fun t : ℝ => ∫ u in t..1, capProfile n u) := by
      simpa only [intervalIntegral.integral_symm 1, Function.comp_def] using continuous_neg.comp hInt
    exact (hFlip.div_const _).measurable.comp (by
      unfold capThreshold capRadius
      fun_prop)
  · simp only [shiftedCapTail, ite_eq_right hn]
    exact measurable_const

/-- The integral expression of equation (14), given the expected-perimeter
bound for Nazarov's random polytope. -/
theorem lowerBound_of_nazarov {a b W : ℝ} (ha : 0 < a) (hb : 0 < b) (hW : 0 ≤ W)
    (hPolytope : ∀ᶠ n in atTop,
      ENNReal.ofReal ((⌊b / capScale a n⌋₊ : ℝ) *
        (Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi))) *
        (∫⁻ w in Set.Ioc (-W) W, ENNReal.ofReal
          (shiftedRadialDensity n w * (1 - shiftedCapTail a n w) ^ (⌊b / capScale a n⌋₊ - 1)))
        ≤ Γ (n + 1)) :
    ENNReal.ofReal ((b * a * Real.exp (-a ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ w in (-W)..W, Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w)))) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by
  apply lowerBound_of_polytope_estimates ha hb hW (s := capScale a)
    (radial := shiftedRadialDensity) (p := shiftedCapTail a) (q := capMajorant a)
  · exact tendsto_capScale_zero ha
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact capScale_pos ha hn
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact capScale_mul_density ha hn
  · intro w
    apply (tendsto_radialDensity_shift w).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    unfold shiftedRadialDensity
    rw [Nat.cast_sub hn, Nat.cast_one]
  · intro n w
    exact radialDensity_nonneg _ _
  · intro w
    exact tendsto_capMajorant_div_capScale a w ha
  · intro w
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_capTail_le_capMajorant a w ha]
      with n hn hCap
    simpa only [shiftedCapTail, ite_eq_left hn] using hCap
  · intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      ((shiftedRadialDensity_measurable n).mul
        ((measurable_const.sub (shiftedCapTail_measurable a n)).pow_const _))
  · exact hPolytope

end Grokability

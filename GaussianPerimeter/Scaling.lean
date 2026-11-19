module

public import GaussianPerimeter.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

open Filter
open scoped Topology

namespace GaussianPerimeter

/-- Replacing the dimension in the fourth root by its predecessor has no
effect in the limit. -/
theorem tendsto_quarter_power_ratio :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (n + 1 : ℝ) ^ (1 / 4 : ℝ))
      atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hInv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    hden.const_div_atTop 1
  have hRatio : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) by
      simpa only [sub_zero] using tendsto_const_nhds.sub hInv).congr
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    field_simp
    ring
  have hPower := (Real.continuousAt_rpow_const 1 (1 / 4 : ℝ)
    (Or.inl one_ne_zero)).tendsto.comp hRatio
  rw [Real.one_rpow] at hPower
  apply hPower.congr
  intro n
  exact Real.div_rpow (Nat.cast_nonneg _) (by positivity) _

theorem fourthRoot_eq_rpow (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

/-- The exponential prefactor in the expectation, divided by its scale,
converges after normalization by the dimension's fourth root. -/
theorem tendsto_normalized_prefactor {s : ℕ → ℝ} {a b : ℝ}
    (hs : Tendsto s atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b)
    (hscale : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi) =
        s n * (a * Real.sqrt (Real.sqrt n)) * Real.exp (-a ^ 4 / 4)) :
    Tendsto (fun n : ℕ => (⌊b / s n⌋₊ : ℝ) *
      (Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) /
        (n + 1 : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 (b * a * Real.exp (-a ^ 4 / 4))) := by
  have h := (((tendsto_floor_mul_scale hs hpos hb).mul tendsto_quarter_power_ratio).mul_const a)
    |>.mul_const (Real.exp (-a ^ 4 / 4))
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [hscale] with n hn
  rw [hn, fourthRoot_eq_rpow _ (Nat.cast_nonneg _)]
  ring

end GaussianPerimeter

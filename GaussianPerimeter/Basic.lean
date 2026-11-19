module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Order.LiminfLimsup

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianPerimeter

/-- The integer part of a growing trial count preserves its product with the vanishing scale. -/
theorem tendsto_floor_mul_scale {s : ℕ → ℝ} {b : ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b) :
    Tendsto (fun n => (⌊b / s n⌋₊ : ℝ) * s n) atTop (𝓝 b) := by
  have hlo : ∀ᶠ n in atTop, b - s n ≤ (⌊b / s n⌋₊ : ℝ) * s n := by
    filter_upwards [hpos] with n hn
    have h := (div_lt_iff₀ hn).mp (Nat.lt_floor_add_one (b / s n))
    linarith
  have hhi : ∀ᶠ n in atTop, (⌊b / s n⌋₊ : ℝ) * s n ≤ b := by
    filter_upwards [hpos] with n hn
    exact (le_div_iff₀ hn).mp (Nat.floor_le (div_nonneg hb hn.le))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds.sub hs)
    tendsto_const_nhds hlo hhi

/-- Removing one trial has no effect on the scaled limit. -/
theorem tendsto_floor_sub_one_mul_scale {s : ℕ → ℝ} {b : ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b) :
    Tendsto (fun n => ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) * s n) atTop (𝓝 b) := by
  have hlo : ∀ᶠ n in atTop,
      b - 2 * s n ≤ ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) * s n := by
    filter_upwards [hpos] with n hn
    have hFloor := (div_lt_iff₀ hn).mp (Nat.lt_floor_add_one (b / s n))
    have hNat : ⌊b / s n⌋₊ ≤ (⌊b / s n⌋₊ - 1) + 1 := by omega
    have hCast : (⌊b / s n⌋₊ : ℝ) ≤ ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hNat
    have h := mul_le_mul_of_nonneg_right hCast hn.le
    linarith
  have hhi : ∀ᶠ n in atTop, ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) * s n ≤ b := by
    filter_upwards [hpos] with n hn
    apply (le_div_iff₀ hn).mp
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (div_nonneg hb hn.le))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub (hs.const_mul 2)) tendsto_const_nhds hlo hhi

/-- The probability of no success in independent trials has the Poisson limit
when the success probabilities vanish and the expected counts converge. -/
theorem tendsto_no_success {q : ℕ → ℝ} {m : ℕ → ℕ} {c : ℝ}
    (hq : Tendsto q atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < q n)
    (hmq : Tendsto (fun n => (m n : ℝ) * q n) atTop (𝓝 c)) :
    Tendsto (fun n => (1 - q n) ^ m n) atTop (𝓝 (Real.exp (-c))) := by
  have hq' : Tendsto q atTop (𝓝[Set.Ioi 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, hpos⟩
  have hInv := tendsto_inv_nhdsGT_zero.comp hq'
  have hLog := (Real.tendsto_mul_log_one_add_div_atTop (-1)).comp hInv
  have h := (Real.continuous_exp.tendsto (c * -1)).comp (hmq.mul hLog)
  rw [mul_neg_one] at h
  apply h.congr'
  filter_upwards [hpos, hq.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with n hn hn₁
  change Real.exp ((m n * q n) * ((q n)⁻¹ * Real.log (1 + -1 / (q n)⁻¹))) =
    (1 - q n) ^ m n
  rw [div_inv_eq_mul, neg_one_mul, ← sub_eq_add_neg, ← mul_assoc,
    mul_inv_cancel_right₀ hn.ne', mul_comm, ← Real.rpow_def_of_pos (sub_pos.mpr hn₁),
    Real.rpow_natCast]

/-- Fatou's lemma applied to lower bounds that hold eventually at each point. -/
theorem lintegral_le_liminf_of_eventually_le_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n))
    (hg : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (F x)))
    (hgf : ∀ x, ∀ᶠ n in atTop, g n x ≤ f n x) :
    (∫⁻ x, F x ∂μ) ≤ liminf (fun n => ∫⁻ x, f n x ∂μ) atTop := by
  refine le_trans (lintegral_mono fun x => ?_) (lintegral_liminf_le hf)
  rw [← (hg x).liminf_eq]
  exact liminf_le_liminf (hgf x)

end GaussianPerimeter

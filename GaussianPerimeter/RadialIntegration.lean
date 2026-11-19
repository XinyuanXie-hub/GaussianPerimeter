module

public import GaussianPerimeter.Radial
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GaussianPerimeter

local notation "Euc" => fun n => EuclideanSpace ℝ (Fin n)

/-- The radial form of a nonnegative integral on Euclidean space. -/
theorem lintegral_norm_euclidean (n : ℕ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Euc (n + 1), f ‖x‖) =
      ((n + 1 : ℕ) : ℝ≥0∞) * volume (Metric.ball (0 : Euc (n + 1)) 1) *
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) * f r) := by
  let E := Euc (n + 1)
  let μ : Measure E := volume
  let e := homeomorphUnitSphereProd E
  let g : Ioi (0 : ℝ) → ℝ≥0∞ := fun r => f r
  have hg : Measurable g := hf.comp measurable_subtype_coe
  have hdim : Module.finrank ℝ E = n + 1 := finrank_euclideanSpace_fin
  have hpres : MeasurePreserving e (μ.comap Subtype.val)
      (μ.toSphere.prod (.volumeIoiPow n)) := by
    simpa [e, hdim] using μ.measurePreserving_homeomorphUnitSphereProd
  calc
    _ = ∫⁻ x : ({(0 : E)}ᶜ : Set E), f ‖(x : E)‖ ∂(μ.comap Subtype.val) := by
      rw [lintegral_subtype_comap (μ := μ) (measurableSet_singleton (0 : E)).compl
        (fun x : E => f ‖x‖), restrict_compl_singleton]
    _ = ∫⁻ z, g z.2 ∂(μ.toSphere.prod (.volumeIoiPow n)) := by
      simpa only [g, e, Function.comp_apply, homeomorphUnitSphereProd_apply_snd_coe] using
        hpres.lintegral_comp_emb e.measurableEmbedding (g ∘ Prod.snd)
    _ = μ.toSphere univ * ∫⁻ r, g r ∂(Measure.volumeIoiPow n) := by
      rw [lintegral_prod (fun z : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => g z.2)
        (hg.comp measurable_snd).aemeasurable]
      change (∫⁻ _x, ∫⁻ y, g y ∂(Measure.volumeIoiPow n) ∂μ.toSphere) = _
      rw [lintegral_const, mul_comm]
    _ = _ := by
      rw [Measure.toSphere_apply_univ, hdim, Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
      simp only [Pi.mul_apply, g, μ]
      rw [lintegral_subtype_comap measurableSet_Ioi (fun r : ℝ => ENNReal.ofReal (r ^ n) * f r)]

private theorem radial_normalizing_constant (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) *
      (Real.sqrt Real.pi ^ (n + 1) / Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) *
      (2 * Real.pi) ^ (-((n + 1 : ℕ) : ℝ) / 2) *
      (∫ r, radialKernel (n + 1) r) = 1 := by
  let d : ℝ := (n + 1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hπ := Real.pi_pos
  rw [integral_radialKernel _ (Nat.succ_pos _), ← Real.rpow_natCast,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hπ.le]
  change d * (Real.pi ^ (1 / 2 * d) / Real.Gamma (d / 2 + 1)) *
    (2 * Real.pi) ^ (-d / 2) *
    ((1 / 2 : ℝ) ^ (-d / 2) * (1 / 2) * Real.Gamma (d / 2)) = 1
  rw [Real.Gamma_add_one (by positivity), Real.div_rpow (by norm_num) (by norm_num),
    Real.one_rpow, Real.mul_rpow (by norm_num) hπ.le]
  rw [show -d / 2 = -(1 / 2 * d) by ring, Real.rpow_neg hπ.le]
  have hG := Real.Gamma_pos_of_pos (show 0 < d / 2 by positivity)
  have hp := Real.rpow_pos_of_pos hπ (1 / 2 * d)
  have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(1 / 2 * d))
  field_simp

/-- Radial integration against the normalized Gaussian density in positive dimension. -/
theorem lintegral_gaussian_radial (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫⁻ x : Euc (n + 1), ENNReal.ofReal
      ((2 * Real.pi) ^ (-((n + 1 : ℕ) : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) * f ‖x‖)) =
      ∫⁻ r : ℝ, ENNReal.ofReal (radialDensity (n + 1) r * f r) := by
  let c : ℝ := (2 * Real.pi) ^ (-((n + 1 : ℕ) : ℝ) / 2)
  let v : ℝ := Real.sqrt Real.pi ^ (n + 1) / Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)
  let C : ℝ := ((n + 1 : ℕ) : ℝ) * v * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hv : 0 ≤ v := by
    unfold v
    exact div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hInv : C = (∫ r, radialKernel (n + 1) r)⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀
      (integral_radialKernel_pos (n + 1) (Nat.succ_pos _)).ne').mp
    exact radial_normalizing_constant n
  have hMeas : Measurable (fun r : ℝ => ENNReal.ofReal (c * Real.exp (-r ^ 2 / 2) * f r)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((measurable_const.mul (by fun_prop)).mul hf)
  have hPower : Measurable (fun r : ℝ => r ^ n) := by fun_prop
  have hMeas' : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ n * Real.exp (-r ^ 2 / 2) * f r)) :=
    ENNReal.continuous_ofReal.measurable.comp ((hPower.mul (by fun_prop)).mul hf)
  rw [lintegral_norm_euclidean n hMeas, EuclideanSpace.volume_ball, Fintype.card_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  change ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal v *
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) *
      ENNReal.ofReal (c * Real.exp (-r ^ 2 / 2) * f r)) = _
  have hPointwise : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) *
      ENNReal.ofReal (c * Real.exp (-r ^ 2 / 2) * f r) =
        ENNReal.ofReal c * ENNReal.ofReal (r ^ n * Real.exp (-r ^ 2 / 2) * f r) := by
    intro r hr
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.out.le _), ← ENNReal.ofReal_mul hc]
    congr 1
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hPointwise, lintegral_const_mul _ hMeas',
    ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hv)]
  change ENNReal.ofReal C * _ = _
  rw [← lintegral_const_mul _ hMeas']
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hr, ← ENNReal.ofReal_mul hC]
    congr 1
    have hrKernel : radialKernel (n + 1) r = r ^ n * Real.exp (-r ^ 2 / 2) := by
      simp [radialKernel, hr]
    rw [hInv, radialDensity, hrKernel, div_eq_mul_inv]
    ring
  · simp [radialDensity, radialKernel, hr]

end GaussianPerimeter

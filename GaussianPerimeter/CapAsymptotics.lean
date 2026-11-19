module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Spherical-cap bounds

The cap numerator is bounded by integrating the density weighted by `u / t`.
A rescaling and dominated convergence give the normalization asymptotic.
The resulting majorant is the pointwise form of the cap estimate used in Theorem 1.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Interval Topology

namespace Grokability

/-- The unnormalized density of a coordinate of a uniform point on the sphere
in Euclidean space of dimension `n + 1`. -/
noncomputable def capProfile (n : ℕ) (u : ℝ) : ℝ :=
  (1 - u ^ 2) ^ (((n : ℝ) - 2) / 2)

noncomputable def capNormalizer (n : ℕ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, capProfile n u

/-- The tail of one coordinate of a uniform point on the sphere, for thresholds in `[0,1]`. -/
noncomputable def capTail (n : ℕ) (t : ℝ) : ℝ :=
  (∫ u in t..1, capProfile n u) / capNormalizer n

/-- The distance of the hyperplanes from the origin in Nazarov's construction. -/
noncomputable def capRho (a : ℝ) (n : ℕ) : ℝ :=
  a * Real.sqrt (Real.sqrt (n : ℝ))

/-- The length of the point being tested against a random half-space. -/
noncomputable def capRadius (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt ((n : ℝ) - 1) + w) ^ 2 + capRho a n ^ 2)

/-- The threshold for the normal component of the random direction. -/
noncomputable def capThreshold (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  capRho a n / capRadius a n w

/-- The dimension-dependent scale of the spherical-cap probabilities. -/
noncomputable def capScale (a : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-(capRho a n ^ 2) / 2) / (Real.sqrt (2 * Real.pi) * capRho a n)) *
    Real.exp (a ^ 4 / 4)

/-- A cap bound obtained by integrating the density with an extra factor `u / t`. -/
noncomputable def capMajorant (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  let t := capThreshold a n w
  (1 - t ^ 2) ^ ((n : ℝ) / 2) / ((n : ℝ) * t * capNormalizer n)

theorem capProfile_continuous {n : ℕ} (hn : 2 ≤ n) : Continuous (capProfile n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact (continuous_const.sub (continuous_id.pow 2)).rpow_const
    (fun _ => Or.inr (by linarith))

private theorem capProfile_nonneg {n : ℕ} {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ capProfile n x := by
  have h := sq_le_sq' hx.1 hx.2
  exact Real.rpow_nonneg (by linarith) _

private theorem capNormalizer_nonneg (n : ℕ) : 0 ≤ capNormalizer n := by
  exact intervalIntegral.integral_nonneg (by norm_num) fun _ hx => capProfile_nonneg hx

/-- Integrating `(u / t) * capProfile n u` gives an upper bound on the cap numerator. -/
theorem capTail_le {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    capTail n t ≤ (1 - t ^ 2) ^ ((n : ℝ) / 2) / ((n : ℝ) * t * capNormalizer n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hcont := capProfile_continuous hn
  have hweighted : Continuous (fun u : ℝ => u / t * capProfile n u) :=
    (continuous_id.div_const t).mul hcont
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht' (hcont.intervalIntegrable _ _)
    (hweighted.intervalIntegrable _ _) (fun u hu => by
      have hsingle : 0 ≤ capProfile n u :=
        capProfile_nonneg ⟨by linarith [hu.1], hu.2⟩
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right ((le_div_iff₀ ht).2 (by simpa using hu.1)) hsingle :
          1 * capProfile n u ≤ _))
  let primitive (u : ℝ) := -(1 - u ^ 2) ^ ((n : ℝ) / 2) / ((n : ℝ) * t)
  have hprimitive : Continuous primitive :=
    (((continuous_const.sub (continuous_id.pow 2)).rpow_const
      (fun _ => Or.inr (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity))).neg).div_const _
  have hderiv (u : ℝ) (_ : u ∈ Ioo t 1) :
      HasDerivAt primitive (u / t * capProfile n u) u := by
    have hb := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)
    have hd := hb.rpow_const (p := (n : ℝ) / 2) (Or.inr (by linarith))
    convert hd.neg.div_const ((n : ℝ) * t) using 1
    simp only [capProfile, Pi.sub_apply]
    rw [show (n : ℝ) / 2 - 1 = ((n : ℝ) - 2) / 2 by ring]
    field_simp
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht'
    hprimitive.continuousOn hderiv (hweighted.intervalIntegrable _ _)
  rw [hFTC] at hmono
  have h1 : primitive 1 = 0 := by
    simp [primitive, Real.zero_rpow (show (n : ℝ) / 2 ≠ 0 by positivity)]
  rw [h1, zero_sub] at hmono
  simp only [primitive, neg_div, neg_neg] at hmono
  rw [capTail, ← div_div]
  exact div_le_div_of_nonneg_right hmono (capNormalizer_nonneg n)

theorem capNormalizer_pos {n : ℕ} (hn : 2 ≤ n) : 0 < capNormalizer n := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((capProfile_continuous hn).intervalIntegrable _ _) (fun x hx => ?_) (by norm_num)
  unfold capProfile
  apply Real.rpow_pos_of_pos
  have hx1 : -1 < x := hx.1
  have hx2 : x < 1 := hx.2
  nlinarith [mul_pos (by linarith : 0 < 1 + x) (by linarith : 0 < 1 - x)]

theorem capTail_nonneg {n : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ capTail n t := by
  apply div_nonneg _ (capNormalizer_nonneg n)
  exact intervalIntegral.integral_nonneg ht.2 fun x hx =>
    capProfile_nonneg ⟨(by linarith [ht.1] : (-1 : ℝ) ≤ t).trans hx.1, hx.2⟩

theorem capTail_le_one {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    capTail n t ≤ 1 := by
  rw [capTail, div_le_one (capNormalizer_pos hn)]
  exact intervalIntegral.integral_mono_interval (by linarith [ht.1]) ht.2 le_rfl
    ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun x hx => capProfile_nonneg (Ioc_subset_Icc_self hx)))
    ((capProfile_continuous hn).intervalIntegrable _ _)

private theorem capProfile_shift {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    capProfile (n + 2) x = (1 - x ^ 2) * capProfile n x := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 ≤ 1 - x ^ 2 := by
    have := sq_le_sq' hx.1 hx.2
    linarith
  unfold capProfile
  rw [show (((n + 2 : ℕ) : ℝ) - 2) / 2 = 1 + ((n : ℝ) - 2) / 2 by push_cast; ring,
    Real.rpow_add_of_nonneg hb zero_le_one (by linarith), Real.rpow_one]

/-- Integrating the derivative of `u * capProfile (n + 2) u` over a tail interval. -/
private theorem capProfile_integral_shift {n : ℕ} (hn : 2 ≤ n) {l : ℝ}
    (hl : -1 ≤ l) (hl' : l ≤ 1) :
    (n : ℝ) * (∫ u in l..1, capProfile n u) =
      ((n : ℝ) + 1) * (∫ u in l..1, capProfile (n + 2) u) + l * capProfile (n + 2) l := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcont := capProfile_continuous hn
  have hcont' := capProfile_continuous (show 2 ≤ n + 2 by omega)
  let primitive (u : ℝ) := u * capProfile (n + 2) u
  have hprimitive : Continuous primitive := continuous_id.mul hcont'
  have hderiv (u : ℝ) (hu : u ∈ Ioo l 1) :
      HasDerivAt primitive (((n : ℝ) + 1) * capProfile (n + 2) u - (n : ℝ) * capProfile n u) u := by
    have hu' : u ∈ Icc (-1 : ℝ) 1 := ⟨hl.trans hu.1.le, hu.2.le⟩
    have heq : ∀ x, capProfile (n + 2) x = (1 - x ^ 2) ^ ((n : ℝ) / 2) := by
      intro x
      simp [capProfile, Nat.cast_add]
    have hb := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)
    have hd := hb.rpow_const (p := (n : ℝ) / 2) (Or.inr (by linarith))
    have hd' := (hasDerivAt_id u).mul hd
    simp only [primitive, heq]
    convert hd' using 1 <;> try rfl
    have hshift := capProfile_shift hn hu'
    rw [heq] at hshift
    rw [show (n : ℝ) / 2 - 1 = ((n : ℝ) - 2) / 2 by ring]
    simp only [Pi.sub_apply]
    rw [show (1 - u ^ 2) ^ (((n : ℝ) - 2) / 2) = capProfile n u by rfl, hshift]
    simp
    ring
  have hderivcont : Continuous (fun u : ℝ => ((n : ℝ) + 1) * capProfile (n + 2) u -
      (n : ℝ) * capProfile n u) := (hcont'.const_mul _).sub (hcont.const_mul _)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hl' hprimitive.continuousOn
    hderiv (hderivcont.intervalIntegrable _ _)
  have h1 : capProfile (n + 2) 1 = 0 := by
    simp [capProfile, Real.zero_rpow (show (n : ℝ) / 2 ≠ 0 by linarith)]
  rw [intervalIntegral.integral_sub ((hcont'.const_mul _).intervalIntegrable _ _)
      ((hcont.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h
  simp [primitive, h1] at h
  linarith

/-- The exact spherical cap probability in terms of cross-sections of the unit ball. -/
theorem capTail_eq_ballSections {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    capTail n t = (t / ((n : ℝ) + 1) * capProfile (n + 2) t +
      (∫ u in t..1, capProfile (n + 2) u)) / capNormalizer (n + 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hmass := capProfile_integral_shift hn (l := -1) le_rfl (by norm_num)
  have htail := capProfile_integral_shift hn (l := t) (by linarith) ht'
  have h1 : capProfile (n + 2) (-1) = 0 := by
    norm_num [capProfile, Real.zero_rpow (show (n : ℝ) / 2 ≠ 0 by linarith)]
  rw [h1, mul_zero, add_zero, ← capNormalizer, ← capNormalizer] at hmass
  have hN := capNormalizer_pos hn
  have hN' := capNormalizer_pos (show 2 ≤ n + 2 by omega)
  unfold capTail
  field_simp [hN.ne', hN'.ne']
  -- Both sides reduce to the same numerator after the integral shifts.
  apply (mul_left_cancel₀ hn0.ne')
  linear_combination capNormalizer (n + 2) * ((n : ℝ) + 1) * htail -
    (((n : ℝ) + 1) * (∫ u in t..1, capProfile (n + 2) u) +
      t * capProfile (n + 2) t) * hmass

/-- The error in the logarithm's degree-`k` expansion stays negligible after
rescaling by `m` when `m * u ^ k` has a finite limit. -/
private theorem tendsto_scaled_log_error {u m : ℕ → ℝ} (k : ℕ) {c : ℝ}
    (hu : Tendsto u atTop (𝓝 0)) (hu0 : ∀ᶠ n in atTop, 0 ≤ u n)
    (hm0 : ∀ᶠ n in atTop, 0 ≤ m n)
    (hm : Tendsto (fun n => m n * u n ^ k) atTop (𝓝 c)) :
    Tendsto (fun n => m n * ((∑ i ∈ Finset.range k, u n ^ (i + 1) / (i + 1)) +
      Real.log (1 - u n))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (g := fun n => (m n * u n ^ k) * (u n / (1 - u n)))
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [hu0, hm0, hu.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)]
      with n hun hmn hlt
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hmn]
    have h := Real.abs_log_sub_add_sum_range_le
      (show |u n| < 1 by rwa [abs_of_nonneg hun]) k
    rw [abs_of_nonneg hun] at h
    calc
      _ ≤ m n * (u n ^ (k + 1) / (1 - u n)) := mul_le_mul_of_nonneg_left h hmn
      _ = _ := by rw [pow_succ, mul_div_assoc, mul_assoc]
  · have h := hm.mul (hu.div (tendsto_const_nhds (x := (1 : ℝ)) |>.sub hu) (by norm_num))
    simpa only [sub_zero, zero_div, mul_zero, Pi.div_apply] using h

private theorem tendsto_inv_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem tendsto_inv_sqrt_nat :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- The unnormalized cap density in the central-limit scaling. -/
private noncomputable def scaledProfile (n : ℕ) (x : ℝ) : ℝ :=
  (max (1 - x ^ 2 / (n : ℝ)) 0) ^ (((n : ℝ) - 2) / 2)

private theorem tendsto_scaledProfile (x : ℝ) :
    Tendsto (fun n => scaledProfile n x) atTop (𝓝 (Real.exp (-(1 / 2) * x ^ 2))) := by
  let u (n : ℕ) := x ^ 2 / (n : ℝ)
  let m (n : ℕ) := ((n : ℝ) - 2) / 2
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa [u, div_eq_mul_inv] using (tendsto_inv_nat.const_mul (x ^ 2))
  have hu0 : ∀ᶠ n in atTop, 0 ≤ u n :=
    Eventually.of_forall fun _ => by dsimp [u]; positivity
  have hn : ∀ᶠ n : ℕ in atTop, 4 ≤ n := eventually_ge_atTop 4
  have hm0 : ∀ᶠ n in atTop, 0 ≤ m n := by
    filter_upwards [hn] with n hn'
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn'
    dsimp [m]
    linarith
  have hm : Tendsto (fun n => m n * u n) atTop (𝓝 (x ^ 2 / 2)) := by
    have h := (tendsto_const_nhds (x := x ^ 2 / 2)).sub (tendsto_inv_nat.const_mul (x ^ 2))
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [hn] with n hn'
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    dsimp [u, m]
    field_simp
  have herr := tendsto_scaled_log_error 1 hu hu0 hm0 (by simpa using hm)
  have hlog : Tendsto (fun n => m n * Real.log (1 - u n)) atTop (𝓝 (-(1 / 2) * x ^ 2)) := by
    rw [show -(1 / 2) * x ^ 2 = 0 - x ^ 2 / 2 by ring]
    convert herr.sub hm using 1
    ext n
    simp
    ring
  refine (Real.continuous_exp.continuousAt.tendsto.comp hlog).congr' ?_
  filter_upwards [hu.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with n hu1
  have hbase : 0 < 1 - u n := by linarith
  change Real.exp (m n * Real.log (1 - u n)) = (max (1 - u n) 0) ^ m n
  rw [max_eq_left hbase.le, Real.rpow_def_of_pos hbase, mul_comm]

private theorem scaledProfile_bound {n : ℕ} (hn : 4 ≤ n) (x : ℝ) :
    ‖scaledProfile n x‖ ≤ Real.exp (-(1 / 4) * x ^ 2) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  let u := x ^ 2 / (n : ℝ)
  let m := ((n : ℝ) - 2) / 2
  have hm : 0 < m := by dsimp [m]; linarith
  have hm' : (n : ℝ) / 4 ≤ m := by dsimp [m]; linarith
  change ‖(max (1 - u) 0) ^ m‖ ≤ _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
  by_cases hbase : 0 < 1 - u
  · rw [max_eq_left hbase.le, Real.rpow_def_of_pos hbase]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log (1 - u) ≤ -u := by
      have := Real.log_le_sub_one_of_pos hbase
      linarith
    calc
      Real.log (1 - u) * m ≤ -u * m := mul_le_mul_of_nonneg_right hlog hm.le
      _ ≤ -u * ((n : ℝ) / 4) := mul_le_mul_of_nonpos_left hm' (neg_nonpos.mpr (by dsimp [u]; positivity))
      _ = -(1 / 4) * x ^ 2 := by
        dsimp [u]
        field_simp
  · rw [max_eq_right (le_of_not_gt hbase), Real.zero_rpow hm.ne']
    exact (Real.exp_pos _).le

private theorem scaledProfile_integral_eq {n : ℕ} (hn : 4 ≤ n) :
    (∫ x, scaledProfile n x) = Real.sqrt (n : ℝ) * capNormalizer n := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  let r := Real.sqrt (n : ℝ)
  have hr : 0 < r := Real.sqrt_pos.2 hn0
  have hr2 : r ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hsupport : Function.support (scaledProfile n) ⊆ Ioc (-r) r := by
    intro x hx
    by_contra hx'
    have hsq : r ^ 2 ≤ x ^ 2 := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx'
      rcases hx' with h | h <;> nlinarith
    have hbase : 1 - x ^ 2 / (n : ℝ) ≤ 0 := by
      have := (le_div_iff₀ hn0).2 (by linarith : 1 * (n : ℝ) ≤ x ^ 2)
      linarith
    exact hx (by simp [scaledProfile, max_eq_right hbase,
      Real.zero_rpow (show ((n : ℝ) - 2) / 2 ≠ 0 by linarith)])
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  have hchange (x : ℝ) (hx : x ∈ [[-r, r]]) :
      scaledProfile n x = capProfile n (x * r⁻¹) := by
    have hx' : -r ≤ x ∧ x ≤ r := by
      simpa only [uIcc_of_le (by linarith : -r ≤ r), mem_Icc] using hx
    have hsq : x ^ 2 ≤ r ^ 2 := sq_le_sq' hx'.1 hx'.2
    have hbase : 0 ≤ 1 - x ^ 2 / (n : ℝ) := by
      have := (div_le_iff₀ hn0).2 (by linarith : x ^ 2 ≤ 1 * (n : ℝ))
      linarith
    rw [scaledProfile, capProfile, max_eq_left hbase, mul_pow, inv_pow, hr2, div_eq_mul_inv]
  rw [intervalIntegral.integral_congr hchange,
    intervalIntegral.integral_comp_mul_right _ (inv_ne_zero hr.ne')]
  simp only [inv_inv, smul_eq_mul, neg_mul, mul_inv_cancel₀ hr.ne', capNormalizer, r]

private theorem tendsto_scaledCapNormalizer :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * capNormalizer n) atTop
      (𝓝 (Real.sqrt (2 * Real.pi))) := by
  have hDCT : Tendsto (fun n => ∫ x, scaledProfile n x) atTop
      (𝓝 (∫ x : ℝ, Real.exp (-(1 / 2) * x ^ 2))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => Real.exp (-(1 / 4) * x ^ 2))
    · filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
      have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
      have hbase : Continuous (fun x : ℝ => max (1 - x ^ 2 / (n : ℝ)) 0) := by
        fun_prop
      exact (hbase.rpow_const (fun _ => Or.inr (by linarith))).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
      exact ae_of_all _ (scaledProfile_bound hn)
    · exact integrable_exp_neg_mul_sq (by norm_num)
    · exact ae_of_all _ tendsto_scaledProfile
  rw [integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  exact scaledProfile_integral_eq hn


theorem capRho_sq (a : ℝ) (n : ℕ) :
    capRho a n ^ 2 = a ^ 2 * Real.sqrt (n : ℝ) := by
  rw [capRho, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]

theorem capRho_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    0 < capRho a n := by
  unfold capRho
  exact mul_pos ha (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn)))

/-- Eventually the threshold is positive and does not exceed one. -/
theorem eventually_capThreshold_mem (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, capThreshold a n w ∈ Ioc (0 : ℝ) 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hρ := capRho_pos ha (show 0 < n by omega)
  have hrad : capRho a n ≤ capRadius a n w := by
    calc
      capRho a n = Real.sqrt (capRho a n ^ 2) := (Real.sqrt_sq hρ.le).symm
      _ ≤ capRadius a n w := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  exact ⟨div_pos hρ (hρ.trans_le hrad), (div_le_one (hρ.trans_le hrad)).2 hrad⟩

theorem eventually_capTail_le_capMajorant (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, capTail n (capThreshold a n w) ≤ capMajorant a n w := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_capThreshold_mem a w ha] with n hn ht
  exact capTail_le hn ht.1 ht.2

theorem capScale_pos {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    0 < capScale a n := by
  unfold capScale
  have := capRho_pos ha hn
  positivity

theorem eventually_capMajorant_nonneg (a w : ℝ) (ha : 0 < a) :
    ∀ᶠ n in atTop, 0 ≤ capMajorant a n w := by
  filter_upwards [eventually_capThreshold_mem a w ha] with n ht
  have hsq := sq_le_sq' (show -(1 : ℝ) ≤ capThreshold a n w by linarith [ht.1]) ht.2
  have hb : 0 ≤ 1 - capThreshold a n w ^ 2 := by linarith
  unfold capMajorant
  exact div_nonneg (Real.rpow_nonneg hb _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1.le) (capNormalizer_nonneg _))

private theorem capRadius_sq (a : ℝ) (n : ℕ) (w : ℝ) :
    capRadius a n w ^ 2 = (Real.sqrt ((n : ℝ) - 1) + w) ^ 2 + capRho a n ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem tendsto_sqrt_ratio :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) - 1) / Real.sqrt (n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_nat
  simp only [sub_zero] at h
  have h' := Real.continuous_sqrt.continuousAt.tendsto.comp h
  rw [Real.sqrt_one] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hprod : (n : ℝ) * (1 - (n : ℝ)⁻¹) = (n : ℝ) - 1 := by
    field_simp
  rw [← hprod, Real.sqrt_mul hn0.le, mul_comm, mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hn0).ne']
  rfl

private theorem tendsto_radius_delta (a w : ℝ) :
    Tendsto (fun n : ℕ => (capRadius a n w ^ 2 - (n : ℝ)) / Real.sqrt (n : ℝ)) atTop
      (𝓝 (2 * w + a ^ 2)) := by
  have h := ((tendsto_sqrt_ratio.const_mul (2 * w)).add
    (tendsto_inv_sqrt_nat.const_mul (w ^ 2 - 1))).add
    (tendsto_const_nhds (x := a ^ 2))
  simp only [mul_one, mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) - 1 by linarith)
  have hr : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  rw [capRadius_sq, capRho_sq]
  change 2 * w * (Real.sqrt ((n : ℝ) - 1) / Real.sqrt (n : ℝ)) +
      (w ^ 2 - 1) * (Real.sqrt (n : ℝ))⁻¹ + a ^ 2 = _
  field_simp [hr]
  linear_combination -hs

private theorem tendsto_radius_normalized (a w : ℝ) :
    Tendsto (fun n : ℕ => capRadius a n w ^ 2 / (n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_radius_delta a w).mul tendsto_inv_sqrt_nat)
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hr : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
  change 1 + (capRadius a n w ^ 2 - (n : ℝ)) / Real.sqrt (n : ℝ) *
      (Real.sqrt (n : ℝ))⁻¹ = _
  generalize Real.sqrt (n : ℝ) = r at hr hs ⊢
  rw [← hs]
  field_simp
  ring

/-- The majorant has the normalized pointwise limit used in the Gaussian-perimeter argument. -/
theorem tendsto_capMajorant_div_capScale (a w : ℝ) (ha : 0 < a) :
    Tendsto (fun n => capMajorant a n w / capScale a n) atTop (𝓝 (Real.exp (a ^ 2 * w))) := by
  let d (n : ℕ) := (capRadius a n w ^ 2 - (n : ℝ)) / Real.sqrt (n : ℝ)
  let s (n : ℕ) := capRadius a n w ^ 2 / (n : ℝ)
  let u (n : ℕ) := capThreshold a n w ^ 2
  let m (n : ℕ) := (n : ℝ) / 2
  let rho (n : ℕ) := capRho a n
  let rad (n : ℕ) := capRadius a n w
  let k := Real.sqrt (2 * Real.pi)
  have hk : 0 < k := Real.sqrt_pos.2 (by positivity)
  have hs : Tendsto s atTop (𝓝 1) := tendsto_radius_normalized a w
  have hd : Tendsto d atTop (𝓝 (2 * w + a ^ 2)) := tendsto_radius_delta a w
  have hn : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hs0 : ∀ᶠ n in atTop, 0 < s n := hs.eventually_const_lt zero_lt_one
  have rad_ne (n : ℕ) (h : 0 < s n) : rad n ≠ 0 := by
    intro hz
    apply h.ne'
    change rad n ^ 2 / (n : ℝ) = 0
    simp [hz]
  have hu_eq : u =ᶠ[atTop] (fun n => a ^ 2 * (Real.sqrt (n : ℝ))⁻¹ / s n) := by
    filter_upwards [hn, hs0] with n hn' hsn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
    have hr : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
    have hrad := rad_ne n hsn
    change (capRho a n / rad n) ^ 2 = a ^ 2 * (Real.sqrt (n : ℝ))⁻¹ / (rad n ^ 2 / (n : ℝ))
    rw [div_pow, capRho_sq]
    generalize Real.sqrt (n : ℝ) = r at hr hsq ⊢
    rw [← hsq]
    field_simp
  have hu : Tendsto u atTop (𝓝 0) := by
    have h := (tendsto_inv_sqrt_nat.const_mul (a ^ 2)).div hs one_ne_zero
    simpa only [mul_zero, zero_div] using h.congr' hu_eq.symm
  have hm_u_sq : Tendsto (fun n => m n * u n ^ 2) atTop (𝓝 (a ^ 4 / 2)) := by
    have h := (tendsto_const_nhds (x := a ^ 4)).div ((hs.pow 2).const_mul 2) (by norm_num)
    simp only [one_pow, mul_one] at h
    refine h.congr' ?_
    filter_upwards [hu_eq, hs0, hn] with n heq hsn hn'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hr : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
    have hsq := Real.sq_sqrt hn0.le
    change a ^ 4 / (2 * s n ^ 2) = ((n : ℝ) / 2) * u n ^ 2
    rw [heq]
    generalize Real.sqrt (n : ℝ) = r at hr hsq ⊢
    rw [← hsq]
    field_simp [hsn.ne']
  have hlin : Tendsto (fun n => rho n ^ 2 / 2 - m n * u n) atTop
      (𝓝 (a ^ 2 * (2 * w + a ^ 2) / 2)) := by
    have h := (hd.const_mul (a ^ 2)).div (hs.const_mul 2) (by norm_num)
    simp only [mul_one] at h
    refine h.congr' ?_
    filter_upwards [hu_eq, hs0, hn] with n heq hsn hn'
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hr : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
    have hsq := Real.sq_sqrt hn0.le
    have hrad := rad_ne n hsn
    change a ^ 2 * ((rad n ^ 2 - (n : ℝ)) / Real.sqrt (n : ℝ)) /
      (2 * (rad n ^ 2 / (n : ℝ))) = capRho a n ^ 2 / 2 - ((n : ℝ) / 2) * u n
    rw [heq, capRho_sq]
    change _ = _ - ((n : ℝ) / 2) * (a ^ 2 * (Real.sqrt (n : ℝ))⁻¹ / (rad n ^ 2 / (n : ℝ)))
    generalize Real.sqrt (n : ℝ) = r at hr hsq ⊢
    rw [← hsq]
    field_simp
  have herr := tendsto_scaled_log_error 2 hu (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun _ => by dsimp [m]; positivity) hm_u_sq
  let E (n : ℕ) := m n * Real.log (1 - u n) + rho n ^ 2 / 2 - a ^ 4 / 4
  have hE : Tendsto E atTop (𝓝 (a ^ 2 * w)) := by
    have h := ((herr.add hlin).sub (hm_u_sq.div_const 2)).sub
      (tendsto_const_nhds (x := a ^ 4 / 4))
    rw [show a ^ 2 * w = 0 + a ^ 2 * (2 * w + a ^ 2) / 2 -
      (a ^ 4 / 2) / 2 - a ^ 4 / 4 by ring]
    convert h using 1
    ext n
    simp [E, Finset.sum_range_succ]
    ring
  have hN : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * capNormalizer n) atTop (𝓝 k) :=
    tendsto_scaledCapNormalizer
  have hN0 : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) * capNormalizer n :=
    hN.eventually_const_lt hk
  have hS : Tendsto (fun n => Real.sqrt (s n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hs)
  have hP := (hS.const_mul k).div hN hk.ne'
  rw [mul_one, div_self hk.ne'] at hP
  have hF := hP.mul (Real.continuous_exp.continuousAt.tendsto.comp hE)
  simp only [one_mul] at hF
  refine hF.congr' ?_
  filter_upwards [hn, hN0, hu.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with n hn' hNn hun
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hρ := capRho_pos ha (show 0 < n by omega)
  have hρ' : rho n ≠ 0 := hρ.ne'
  have hcn : 0 < capNormalizer n := pos_of_mul_pos_right hNn hr.le
  have hrad : 0 < rad n := by
    dsimp [rad, capRadius]
    apply Real.sqrt_pos.2
    positivity
  have hbase : 0 < 1 - u n := by linarith
  have hsqrt : Real.sqrt (s n) = rad n / Real.sqrt (n : ℝ) := by
    rw [show s n = rad n ^ 2 / (n : ℝ) by rfl, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hrad.le]
  have hexp : Real.exp (E n) = (1 - u n) ^ m n * Real.exp (rho n ^ 2 / 2) /
      Real.exp (a ^ 4 / 4) := by
    dsimp only [E]
    rw [Real.exp_sub, Real.exp_add, Real.rpow_def_of_pos hbase, mul_comm (m n)]
  change (k * Real.sqrt (s n) / (Real.sqrt (n : ℝ) * capNormalizer n)) *
      Real.exp (E n) = capMajorant a n w / capScale a n
  rw [hsqrt, hexp]
  change _ = ((1 - u n) ^ m n / ((n : ℝ) * (rho n / rad n) * capNormalizer n)) /
    ((Real.exp (- (rho n ^ 2) / 2) / (k * rho n)) * Real.exp (a ^ 4 / 4))
  rw [neg_div, Real.exp_neg]
  generalize hr_eq : Real.sqrt (n : ℝ) = r at hr ⊢
  have hsq : r ^ 2 = n := by subst r; exact Real.sq_sqrt hn0.le
  rw [← hsq]
  field_simp [hrad.ne', hρ', hk.ne', hcn.ne', hr.ne', Real.exp_ne_zero]

end Grokability

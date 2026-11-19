module

public import GaussianPerimeter.SphereSections
public import GaussianPerimeter.CapAsymptotics

public section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace Grokability

private theorem sqrt_pow_eq_capProfile (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (Real.sqrt (1 - x ^ 2)) ^ n = capProfile (n + 2) x := by
  have hx' : 0 ≤ 1 - x ^ 2 := by
    have : 0 ≤ (1 - x) * (1 + x) := mul_nonneg (by linarith [hx.2]) (by linarith [hx.1])
    nlinarith
  rw [capProfile, Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right,
    ← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hx']
  ring_nf

/-- A uniform sphere sample lies above a threshold in a unit direction with
probability at most the one-coordinate cap tail. -/
theorem uniformSphere_cap_le_capTail (n : ℕ) (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    uniformSphere (EuclideanSpace ℝ (Fin (n + 1)))
      {u | t ≤ ⟪v, (u : EuclideanSpace ℝ (Fin (n + 1)))⟫} ≤ ENNReal.ofReal (capTail n t) := by
  have : NeZero n := ⟨by omega⟩
  refine (uniformSphere_cap_le_sectionRatio n hv ht ht₁).trans_eq ?_
  have h₁ : (∫ x in t..1, (Real.sqrt (1 - x ^ 2)) ^ n) =
      ∫ x in t..1, capProfile (n + 2) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ht₁.le] at hx
    exact sqrt_pow_eq_capProfile n ⟨(by linarith : (-1 : ℝ) ≤ t).trans hx.1, hx.2⟩
  have h₂ : (∫ x in (-1 : ℝ)..1, (Real.sqrt (1 - x ^ 2)) ^ n) = capNormalizer (n + 2) := by
    unfold capNormalizer
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact sqrt_pow_eq_capProfile n hx
  rw [sqrt_pow_eq_capProfile n ⟨by linarith, ht₁.le⟩, h₁, h₂,
    capTail_eq_ballSections hn ht.le ht₁.le, ENNReal.ofReal_div_of_pos (capNormalizer_pos (by omega))]


/-- The probability of passing an inner-product constraint from the facet computation. -/
theorem one_sub_capTail_le_uniformSphere (n : ℕ) (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1) {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ρ < R) :
    1 - ENNReal.ofReal (capTail n (ρ / R)) ≤
      uniformSphere (EuclideanSpace ℝ (Fin (n + 1)))
        {u | ⟪R • v, (u : EuclideanSpace ℝ (Fin (n + 1)))⟫ < ρ} := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let S : Set (Metric.sphere (0 : E) 1) := {u | ρ / R ≤ ⟪v, (u : E)⟫}
  have hR0 := hρ.trans hR
  have hset : {u : Metric.sphere (0 : E) 1 | ⟪R • v, (u : E)⟫ < ρ} = Sᶜ := by
    ext u
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_le, real_inner_smul_left]
    rw [lt_div_iff₀ hR0, mul_comm]
  have hs : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  change _ ≤ uniformSphere E _
  rw [hset, measure_compl hs (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left
    (uniformSphere_cap_le_capTail n hn hv (div_pos hρ hR0) ((div_lt_one hR0).2 hR)) _

end Grokability

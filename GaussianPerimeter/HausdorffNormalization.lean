module

public import GaussianPerimeter.BrunnMinkowski
public import Mathlib.MeasureTheory.Measure.Hausdorff

public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace Grokability

/-- The Euclidean isodiametric bound for compact sets. Apply Brunn–Minkowski
to a set and its reflection, whose sum fits in the ball of radius its diameter. -/
theorem volume_le_diameter_ball {n : ℕ} {A : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hA : IsCompact A) :
    (2 : ℝ≥0∞) ^ (n + 1) * volume A ≤
      volume (closedBall 0 (diam A) : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  have hsum := hA.add hA.neg
  have hneg : volume (-A) = volume A := by
    have hsmul : (-1 : ℝ) • A = -A := by
      rw [← Set.image_smul, ← Set.image_neg_eq_neg]
      simp
    rw [← hsmul, Measure.addHaar_smul]
    simp
  have h := VolumeComparison.brunn_minkowski_euclideanSpace hne hA.measurableSet
    hne.neg hA.neg.measurableSet hsum.measurableSet
  rw [hneg, ← two_mul] at h
  have hd : 0 < (n : ℝ) + 1 := by positivity
  have h' := (ENNReal.le_rpow_inv_iff hd).mp h
  rw [ENNReal.mul_rpow_of_nonneg _ _ hd.le, ENNReal.rpow_inv_rpow hd.ne',
    ← Nat.cast_succ, ENNReal.rpow_natCast] at h'
  refine h'.trans (measure_mono ?_)
  rintro x ⟨y, hy, z, hz, rfl⟩
  rw [mem_closedBall, dist_zero_right]
  rw [mem_neg] at hz
  simpa only [dist_eq_norm, sub_neg_eq_add] using
    dist_le_diam_of_mem hA.isBounded hy hz

/-- The normalization used for Gaussian perimeter dominates Lebesgue measure
on the corresponding Euclidean space. -/
theorem volume_le_normalized_hausdorff (n : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      (volume (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) / (2 : ℝ≥0∞) ^ (n + 1)) •
        μH[((n + 1 : ℕ) : ℝ)] := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let C : ℝ≥0∞ := volume (ball (0 : E) 1) / (2 : ℝ≥0∞) ^ (n + 1)
  have hC0 : C ≠ 0 := (ENNReal.div_pos (measure_ball_pos volume 0 zero_lt_one).ne'
    (by simp)).ne'
  have hCtop : C ≠ ⊤ := ENNReal.div_ne_top measure_ball_ne_top (by positivity)
  have hbound {A : Set E} (hA : Bornology.IsBounded A) :
      volume A ≤ C * (ediam A) ^ (n + 1) := by
    have hcl : IsCompact (closure A) :=
      isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hA.closure⟩
    have h := volume_le_diameter_ball hcl
    rw [diam_closure, Measure.addHaar_closedBall volume 0 diam_nonneg,
      finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow diam_nonneg,
      Metric.diam, ENNReal.ofReal_toReal hA.ediam_ne_top] at h
    have h2 : (2 : ℝ≥0∞) ^ (n + 1) ≠ 0 := by positivity
    have h2' : (2 : ℝ≥0∞) ^ (n + 1) ≠ ⊤ := by simp
    have hclbound : volume (closure A) ≤
        ((ediam A) ^ (n + 1) * volume (ball (0 : E) 1)) / (2 : ℝ≥0∞) ^ (n + 1) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl h2) (Or.inl h2')).mpr
      rw [mul_comm (volume (closure A))]
      exact h
    exact (measure_mono subset_closure).trans (by
      simpa only [C, div_eq_mul_inv, mul_right_comm, mul_comm, mul_left_comm] using hclbound)
  have hraw : C⁻¹ • (volume : Measure E) ≤ μH[((n + 1 : ℕ) : ℝ)] := by
    apply Measure.le_hausdorffMeasure _ _ 1 zero_lt_one
    intro A hA
    have hb : Bornology.IsBounded A :=
      isBounded_iff_ediam_ne_top.mpr (ne_top_of_le_ne_top (by simp) hA)
    have hh := mul_le_mul_right (hbound hb) C⁻¹
    rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul] at hh
    simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast] using hh
  change (volume : Measure E) ≤ C • μH[((n + 1 : ℕ) : ℝ)]
  intro A
  change volume A ≤ C * μH[((n + 1 : ℕ) : ℝ)] A
  calc
    volume A = C * (C⁻¹ * volume A) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
    _ ≤ C * μH[((n + 1 : ℕ) : ℝ)] A := mul_le_mul_right (hraw A) C

end Grokability

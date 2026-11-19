module

public import GaussianPerimeter.Geometry
public import GaussianPerimeter.Sphere

public section

open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace InnerProductSpace

namespace Grokability

local notation "Euc" k => EuclideanSpace ℝ (Fin k)
local notation "UnitSphere" k => Metric.sphere (0 : Euc (k + 1)) 1

private theorem norm_eq_one_of_mem_unitSphere {k : ℕ} (u : UnitSphere k) : ‖u.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property

/-- The probability that a uniform normal has inner product less than `ρ`
with a vector whose squared norm is `ρ² + r²`. -/
@[expose]
noncomputable def facetAcceptanceProbability (k : ℕ) (ρ r : ℝ) : ℝ≥0∞ :=
  uniformSphere (Euc (k + 1))
    {v | ⟪Real.sqrt (ρ ^ 2 + r ^ 2) • (EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0),
      v.val⟫_ℝ < ρ}

theorem measurable_facetAcceptanceProbability (k : ℕ) (ρ : ℝ) :
    Measurable (facetAcceptanceProbability k ρ) := by
  let e : Euc (k + 1) := EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0
  let S := {p : ℝ × UnitSphere k | ⟪Real.sqrt (ρ ^ 2 + p.1 ^ 2) • e, p.2.val⟫_ℝ < ρ}
  have hS : MeasurableSet S := by
    apply measurableSet_lt _ measurable_const
    apply Continuous.measurable2 continuous_inner _ (measurable_subtype_coe.comp measurable_snd)
    have hm : Measurable (fun p : ℝ × UnitSphere k => Real.sqrt (ρ ^ 2 + p.1 ^ 2)) :=
      Real.continuous_sqrt.measurable.comp
        ((measurable_const (a := ρ ^ 2)).add (measurable_fst.pow_const 2))
    exact hm.smul (measurable_const (a := e))
  exact measurable_measure_prodMk_left (ν := uniformSphere (Euc (k + 1))) hS

theorem facetAcceptanceProbability_eq (k : ℕ) (ρ r : ℝ)
    (h : 0 < Real.sqrt (ρ ^ 2 + r ^ 2)) :
    facetAcceptanceProbability k ρ r = uniformSphere (Euc (k + 1))
      {v | ⟪(EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0), v.val⟫_ℝ <
        ρ / Real.sqrt (ρ ^ 2 + r ^ 2)} := by
  unfold facetAcceptanceProbability
  congr 1
  ext v
  simp only [mem_ofPred_eq, real_inner_smul_left]
  rw [lt_div_iff₀ h, mul_comm]

/-- Average the lower bound from the strict facets of an intersection of
half-spaces with independent, uniformly distributed unit normals. -/
theorem mul_lintegral_acceptance_le_Γ (k N : ℕ) (ρ : ℝ)
    (hvolume : (volume : Measure (Euc k)) ≤
      (volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k) • μH[(k : ℝ)]) :
    ((N + 1 : ℕ) : ℝ≥0∞) *
      (∫⁻ y : Euc k, facetAcceptanceProbability k ρ ‖y‖ ^ N *
        ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
          Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))) ≤ Γ (k + 1) := by
  classical
  let A := UnitSphere k
  let B := Euc k
  let μ := uniformSphere (Euc (k + 1))
  let μprod := Measure.pi (fun _ : Fin (N + 1) => μ)
  let weight (_ : A) (y : B) :=
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
      Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))
  let e (a : A) := facetEmbedding a.val (norm_eq_one_of_mem_unitSphere a) ρ
  let accept (a : A) (y : B) (v : A) := ⟪e a y, v.val⟫_ℝ < ρ
  have hw : Measurable (uncurry weight) := by unfold uncurry weight; fun_prop
  have he : Measurable (uncurry e) := by
    let normal (a : A) : {u : Euc (k + 1) // ‖u‖ = 1} :=
      ⟨a.val, norm_eq_one_of_mem_unitSphere a⟩
    have hm : Measurable normal := measurable_subtype_coe.subtype_mk
    exact (measurable_facetEmbedding ρ).comp ((hm.comp measurable_fst).prodMk measurable_snd)
  have ha : MeasurableSet {p : (A × B) × A | accept p.1.1 p.1.2 p.2} :=
    measurableSet_lt (Continuous.measurable2 continuous_inner (he.comp measurable_fst)
      (measurable_subtype_coe.comp measurable_snd)) measurable_const
  let F (i : Fin (N + 1)) (u : Fin (N + 1) → A) :=
    ∫⁻ y : B, {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator (fun u => weight (u i) y) u
  have hF (i : Fin (N + 1)) : Measurable (F i) := by
    let m (p : (Fin (N + 1) → A) × B) := (p.1 i, p.2)
    have hm : Measurable m := ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
    have hs : MeasurableSet {p : (Fin (N + 1) → A) × B |
        ∀ j ≠ i, accept (p.1 i) p.2 (p.1 j)} := by
      rw [show {p : (Fin (N + 1) → A) × B | ∀ j ≠ i, accept (p.1 i) p.2 (p.1 j)} =
          ⋂ j : {j // j ≠ i}, (fun p => (m p, p.1 j.1)) ⁻¹'
            {p : (A × B) × A | accept p.1.1 p.1.2 p.2} by ext; simp [m, Subtype.forall]]
      exact MeasurableSet.iInter fun j =>
        ha.preimage (hm.prodMk ((measurable_pi_apply j.1).comp measurable_fst))
    let g : ((Fin (N + 1) → A) × B) → ℝ≥0∞ :=
      {p | ∀ j ≠ i, accept (p.1 i) p.2 (p.1 j)}.indicator (uncurry weight ∘ m)
    have hg : Measurable g := (hw.comp hm).indicator hs
    have hFG : F i = fun u => ∫⁻ y : B, g (u, y) := by
      funext u
      apply lintegral_congr
      intro y
      by_cases hy : ∀ j ≠ i, accept (u i) y (u j)
      all_goals simp [g, m, indicator, hy]
    rw [hFG]
    exact hg.lintegral_prod_right'
  have hF_le (u : Fin (N + 1) → A) : ∑ i, F i u ≤ Γ (k + 1) := by
    let normals (i : Fin (N + 1)) := (u i).val
    let hnormals (i : Fin (N + 1)) := norm_eq_one_of_mem_unitSphere (u i)
    have hfacets := facet_lintegral_sum_le_gaussianPerimeter normals hnormals ρ hvolume
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans (hfacets.trans ?_)
    · let S := {y : B | ∀ j ≠ i, ⟪normals j, e (u i) y⟫_ℝ < ρ}
      calc
        F i u = ∫⁻ y, S.indicator (weight (u i)) y := by
          apply lintegral_congr
          intro y
          have hiff : u ∈ {u | ∀ j ≠ i, accept (u i) y (u j)} ↔ y ∈ S := by
            simp [accept, S, normals, real_inner_comm]
          by_cases hy : y ∈ S
          · rw [indicator_of_mem (hiff.mpr hy), indicator_of_mem hy]
          · rw [indicator_of_notMem (mt hiff.mp hy), indicator_of_notMem hy]
        _ ≤ ∫⁻ y in S, weight (u i) y := lintegral_indicator_le _ _
    · exact gaussianPerimeter_le_Γ (convex_halfspaceIntersection normals ρ)
  have hprob (a : A) (y : B) :
      μ {v | accept a y v} = facetAcceptanceProbability k ρ ‖y‖ := by
    unfold facetAcceptanceProbability
    apply uniformSphere_inner_eq_of_norm_eq _ ρ
    have hn := norm_sq_facetEmbedding a.val (norm_eq_one_of_mem_unitSphere a) ρ y
    rw [norm_smul, (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).norm_eq_one 0, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_sq (norm_nonneg (e a y))).symm.trans (congrArg Real.sqrt hn)
  let J : ℝ≥0∞ := ∫⁻ y : B, facetAcceptanceProbability k ρ ‖y‖ ^ N *
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
      Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))
  have hFi (i : Fin (N + 1)) : (∫⁻ u, F i u ∂μprod) = J := by
    change (∫⁻ u, ∫⁻ y : B, {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator
      (fun u => weight (u i) y) u ∂volume ∂μprod) = J
    rw [lintegral_independent_restrictions μ volume i weight accept hw ha]
    simp_rw [hprob]
    change (∫⁻ _ : A, J ∂μ) = J
    rw [lintegral_const, measure_univ, mul_one]
  change ((N + 1 : ℕ) : ℝ≥0∞) * J ≤ Γ (k + 1)
  calc
    _ = ∑ i : Fin (N + 1), ∫⁻ u, F i u ∂μprod := by
      simp [hFi, nsmul_eq_mul]
    _ = ∫⁻ u, ∑ i, F i u ∂μprod := (lintegral_finsetSum _ (fun i _ => hF i)).symm
    _ ≤ ∫⁻ _, Γ (k + 1) ∂μprod := lintegral_mono hF_le
    _ = Γ (k + 1) := by simp [μprod]

end Grokability

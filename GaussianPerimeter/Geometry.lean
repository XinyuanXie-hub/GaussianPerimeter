module

public import GaussianPerimeter.Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

public section

open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function

namespace GaussianPerimeter

local notation "Euc" k => EuclideanSpace ℝ (Fin k)

private noncomputable def facetBasis {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1) :
    OrthonormalBasis (Fin k) ℝ (ℝ ∙ u)ᗮ :=
  letI : Fact (Module.finrank ℝ (Euc (k + 1)) = k + 1) := ⟨by simp⟩
  OrthonormalBasis.fromOrthogonalSpanSingleton k (v := u) (by
    intro h
    simp [h] at hu)

private noncomputable def referenceNormal (k : ℕ) : Euc (k + 1) :=
  EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0

private theorem norm_referenceNormal (k : ℕ) : ‖referenceNormal k‖ = 1 :=
  (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).norm_eq_one 0

private noncomputable def referenceTangent {k : ℕ} (y : Euc k) :
    (ℝ ∙ referenceNormal k)ᗮ :=
  (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm y

private noncomputable def normalReflection {k : ℕ} (u : Euc (k + 1)) :
    (Euc (k + 1)) ≃ₗᵢ[ℝ] (Euc (k + 1)) :=
  (ℝ ∙ (referenceNormal k - u))ᗮ.reflection

private theorem normalReflection_apply_referenceNormal {k : ℕ} (u : Euc (k + 1))
    (hu : ‖u‖ = 1) : normalReflection u (referenceNormal k) = u :=
  Submodule.reflection_sub ((norm_referenceNormal k).trans hu.symm)

private noncomputable def facetTangent {k : ℕ} (u : Euc (k + 1)) (y : Euc k) :
    Euc (k + 1) :=
  normalReflection u (referenceTangent y)

/-- Coordinates on a hyperplane with unit normal `u` and offset `ρ`.
The fixed tangent coordinates are carried to the desired hyperplane by reflection. -/
noncomputable def facetEmbedding {k : ℕ} (u : Euc (k + 1)) (_hu : ‖u‖ = 1) (ρ : ℝ)
    (y : Euc k) : Euc (k + 1) :=
  ρ • u + facetTangent u y

private theorem inner_facetTangent {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (y : Euc k) : ⟪u, facetTangent u y⟫_ℝ = 0 := by
  calc
    ⟪u, facetTangent u y⟫_ℝ =
        ⟪normalReflection u (referenceNormal k), normalReflection u (referenceTangent y)⟫_ℝ := by
      rw [normalReflection_apply_referenceNormal u hu, facetTangent]
    _ = ⟪referenceNormal k, (referenceTangent y : Euc (k + 1))⟫_ℝ :=
      (normalReflection u).inner_map_map _ _
    _ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (referenceTangent y).2

/-- The hyperplane coordinates depend measurably on the normal and tangent coordinates. -/
theorem measurable_facetEmbedding {k : ℕ} (ρ : ℝ) :
    Measurable (fun p : {u : Euc (k + 1) // ‖u‖ = 1} × Euc k =>
      facetEmbedding p.1.1 p.1.2 ρ p.2) := by
  let N := {u : Euc (k + 1) // ‖u‖ = 1}
  let v (p : N × Euc k) := referenceNormal k - (p.1 : Euc (k + 1))
  let w (p : N × Euc k) : Euc (k + 1) := referenceTangent p.2
  have hm : Measurable (fun p : N × Euc k => (p.1 : Euc (k + 1))) :=
    measurable_subtype_coe.comp measurable_fst
  have hv : Measurable v := measurable_const.sub hm
  have hTangent : Continuous (fun y : Euc k => (referenceTangent y : Euc (k + 1))) :=
    continuous_subtype_val.comp
      (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm.isometry.continuous
  have hw : Measurable w := hTangent.measurable.comp measurable_snd
  have hinner : Measurable (fun p => ⟪v p, w p⟫_ℝ) :=
    Continuous.measurable2 continuous_inner hv hw
  have hcoef : Measurable (fun p => ⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) :=
    hinner.div (hv.norm.pow_const 2)
  have hp : Measurable (fun p => (⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) • v p) :=
    hcoef.smul hv
  have heq (p : N × Euc k) :
      facetEmbedding p.1.1 p.1.2 ρ p.2 =
        ρ • (p.1 : Euc (k + 1)) +
          (w p - ((⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) • v p +
            (⟪v p, w p⟫_ℝ / ‖v p‖ ^ 2) • v p)) := by
    simp only [facetEmbedding, facetTangent, normalReflection, Submodule.reflection_orthogonal_apply,
      Submodule.reflection_singleton_apply, neg_sub, v, w, RCLike.ofReal_real_eq_id, id_eq,
      two_nsmul]
  simp_rw [heq]
  exact ((measurable_const (a := ρ)).smul hm).add (hw.sub (hp.add hp))

theorem inner_facetEmbedding {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (ρ : ℝ) (y : Euc k) : ⟪u, facetEmbedding u hu ρ y⟫_ℝ = ρ := by
  simp [facetEmbedding, inner_add_right, inner_facetTangent u hu y, real_inner_smul_right,
    hu]

theorem isometry_facetEmbedding {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (ρ : ℝ) : Isometry (facetEmbedding u hu ρ) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [facetEmbedding, facetEmbedding, dist_add_left]
  rw [facetTangent, facetTangent, (normalReflection u).isometry.dist_eq]
  exact (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm.isometry.dist_eq _ _

theorem norm_sq_facetEmbedding {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (ρ : ℝ) (y : Euc k) : ‖facetEmbedding u hu ρ y‖ ^ 2 = ρ ^ 2 + ‖y‖ ^ 2 := by
  have horth : ⟪ρ • u, facetTangent u y⟫_ℝ = 0 := by
    simp [real_inner_smul_left, inner_facetTangent u hu y]
  have hnorm : ‖facetTangent u y‖ = ‖y‖ := by
    rw [facetTangent, (normalReflection u).norm_map]
    exact (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm.norm_map y
  calc
    ‖facetEmbedding u hu ρ y‖ ^ 2 = ‖ρ • u‖ ^ 2 + ‖facetTangent u y‖ ^ 2 := by
      simpa only [facetEmbedding, pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    _ = ρ ^ 2 + ‖y‖ ^ 2 := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs, hnorm]

variable {k : ℕ} {ι : Type*}

/-- Intersection of the closed half-spaces with normals `u i` at offset `ρ`. -/
def halfspaceIntersection (u : ι → Euc (k + 1)) (ρ : ℝ) : Set (Euc (k + 1)) :=
  ⋂ i, {x | ⟪u i, x⟫_ℝ ≤ ρ}

theorem convex_halfspaceIntersection (u : ι → Euc (k + 1)) (ρ : ℝ) :
    Convex ℝ (halfspaceIntersection u ρ) :=
  convex_iInter fun i =>
    (convex_Iic ρ).linear_preimage (innerSL ℝ (u i)).toLinearMap

private theorem isClosed_halfspaceIntersection (u : ι → Euc (k + 1)) (ρ : ℝ) :
    IsClosed (halfspaceIntersection u ρ) :=
  isClosed_iInter fun i => isClosed_le (innerSL ℝ (u i)).continuous continuous_const

/-- A strict facet consists of points on the supporting hyperplane of one
constraint where all other constraints are strict. -/
def strictFacet (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) : Set (Euc (k + 1)) :=
  {x | ⟪u i, x⟫_ℝ = ρ} ∩ ⋂ j : {j // j ≠ i}, {x | ⟪u j.1, x⟫_ℝ < ρ}

theorem mem_strictFacet (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) (x : Euc (k + 1)) :
    x ∈ strictFacet u ρ i ↔
      ⟪u i, x⟫_ℝ = ρ ∧ ∀ j ≠ i, ⟪u j, x⟫_ℝ < ρ := by
  simp [strictFacet, Subtype.forall]

theorem measurableSet_strictFacet [Countable ι] (u : ι → Euc (k + 1)) (ρ : ℝ) (i : ι) :
    MeasurableSet (strictFacet u ρ i) :=
  (isClosed_eq (innerSL ℝ (u i)).continuous continuous_const).measurableSet.inter <|
    MeasurableSet.iInter fun j =>
      (isOpen_lt (innerSL ℝ (u j.1)).continuous continuous_const).measurableSet

private theorem pairwiseDisjoint_strictFacet (u : ι → Euc (k + 1)) (ρ : ℝ) :
    Pairwise (Disjoint on strictFacet u ρ) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hx hy
  have hx := ((mem_strictFacet u ρ i x).mp hx).2 j hij.symm
  have hy := ((mem_strictFacet u ρ j x).mp hy).1
  exact hx.ne hy

private theorem strictFacet_subset_frontier (u : ι → Euc (k + 1))
    (hu : ∀ i, ‖u i‖ = 1) (ρ : ℝ) (i : ι) :
    strictFacet u ρ i ⊆ frontier (halfspaceIntersection u ρ) := by
  intro x hx
  rw [mem_strictFacet] at hx
  rw [(isClosed_halfspaceIntersection u ρ).frontier_eq]
  refine ⟨mem_iInter.mpr fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst j; exact hx.1.le
    · exact (hx.2 j h).le
  intro hinterior
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hinterior)
  have hclose : x + (ε / 2) • u i ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  have hconstraint := mem_iInter.mp (hball hclose) i
  change ⟪u i, x + (ε / 2) • u i⟫_ℝ ≤ ρ at hconstraint
  rw [inner_add_right, hx.1, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hu, one_pow, mul_one] at hconstraint
  exact (lt_add_of_pos_right ρ (half_pos hε)).not_ge hconstraint

/-- The sum of the Gaussian integrals over the strict facets is bounded by the
Gaussian perimeter, provided the chosen Hausdorff normalization dominates
Lebesgue measure on the model hyperplane. -/
theorem facet_lintegral_sum_le_gaussianPerimeter [Fintype ι] (u : ι → Euc (k + 1))
    (hu : ∀ i, ‖u i‖ = 1) (ρ : ℝ)
    (hvolume : (volume : Measure (Euc k)) ≤
      (volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k) • μH[(k : ℝ)]) :
    (∑ i, ∫⁻ y in {y | ∀ j ≠ i, ⟪u j, facetEmbedding (u i) (hu i) ρ y⟫_ℝ < ρ},
      ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
        Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2))) ≤
      gaussianPerimeter (halfspaceIntersection u ρ) := by
  classical
  let c := volume (Metric.ball (0 : Euc k) 1) / (2 : ℝ≥0∞) ^ k
  let f (x : Euc (k + 1)) :=
    ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2))
  let s i := strictFacet u ρ i
  let μ : Measure (Euc (k + 1)) := c • μH[(k : ℝ)]
  have hsum : (∑ i, ∫⁻ x in s i, f x ∂μ) ≤ gaussianPerimeter (halfspaceIntersection u ρ) := by
    have huEq :
        (∫⁻ x in ⋃ i, s i, f x ∂μ) = ∑ i, ∫⁻ x in s i, f x ∂μ :=
      (lintegral_iUnion (μ := μ) (measurableSet_strictFacet u ρ)
        (pairwiseDisjoint_strictFacet u ρ) f).trans (tsum_fintype _)
    rw [← huEq, gaussianPerimeter_succ]
    change _ ≤ c • ∫⁻ x in frontier (halfspaceIntersection u ρ), f x ∂μH[(k : ℝ)]
    rw [← setLIntegral_smul_measure]
    exact lintegral_mono_set (iUnion_subset (strictFacet_subset_frontier u hu ρ))

  refine (Finset.sum_le_sum fun i _ => ?_).trans hsum
  let e := facetEmbedding (u i) (hu i) ρ
  have he : Isometry e := isometry_facetEmbedding _ _ _
  have hemb : MeasurableEmbedding e := he.isClosedEmbedding.measurableEmbedding
  have hpre :
      e ⁻¹' s i = {y | ∀ j ≠ i, ⟪u j, e y⟫_ℝ < ρ} := by
    ext y
    change (e y ∈ strictFacet u ρ i) ↔ _
    rw [mem_strictFacet]
    simp [e, inner_facetEmbedding]
  have hcomp (y : Euc k) :
      f (e y) = ENNReal.ofReal ((2 * Real.pi) ^ (-(k + 1 : ℝ) / 2) *
        Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2)) := by
    simp [f, e, norm_sq_facetEmbedding]
  have hmap : Measure.map e (c • μH[(k : ℝ)]) = μ.restrict (range e) := by
    rw [Measure.map_smul _ hemb.measurable.aemeasurable,
      he.map_hausdorffMeasure (Or.inl (Nat.cast_nonneg _)), Measure.restrict_smul]
  have hp : MeasurePreserving e (c • μH[(k : ℝ)]) (μ.restrict (range e)) :=
    ⟨hemb.measurable, hmap⟩
  simp_rw [← hcomp]
  rw [← hpre]
  calc
    ∫⁻ y in e ⁻¹' s i, f (e y) ≤
        ∫⁻ y in e ⁻¹' s i, f (e y) ∂(c • μH[(k : ℝ)]) :=
      lintegral_mono' (Measure.restrict_mono Subset.rfl hvolume) (le_refl _)
    _ = ∫⁻ x in s i, f x ∂(μ.restrict (range e)) :=
      hp.setLIntegral_comp_preimage_emb hemb f _
    _ ≤ ∫⁻ x in s i, f x ∂μ :=
      lintegral_mono' (Measure.restrict_mono Subset.rfl Measure.restrict_le_self) (le_refl _)

end GaussianPerimeter

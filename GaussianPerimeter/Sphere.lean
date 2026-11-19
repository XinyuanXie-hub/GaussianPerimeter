module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi

public section

open MeasureTheory Set Function
open scoped ENNReal Pointwise RealInnerProductSpace

namespace Grokability

/-- Given one distinguished sample, each of the other independent samples
must belong to the same measurable set. -/
theorem lintegral_independent_restrictions {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B)
    [SFinite ν] {N : ℕ} (i : Fin (N + 1)) (weight : A → B → ℝ≥0∞)
    (accept : A → B → A → Prop)
    (hw : Measurable (uncurry weight))
    (ha : MeasurableSet {q : (A × B) × A | accept q.1.1 q.1.2 q.2}) :
    (∫⁻ u, ∫⁻ y, {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator
      (fun u => weight (u i) y) u ∂ν ∂Measure.pi (fun _ : Fin (N + 1) => μ)) =
    ∫⁻ a, ∫⁻ y, μ {v | accept a y v} ^ N * weight a y ∂ν ∂μ := by
  classical
  let μN : Measure (Fin N → A) := Measure.pi fun _ => μ
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => A) i).symm
  have hpres : MeasurePreserving e (μ.prod μN) (Measure.pi (fun _ => μ)) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) i).symm
  let ok (a : A) (y : B) : Set (Fin N → A) := univ.pi fun _ => {v | accept a y v}
  let f (a : A) (z : Fin N → A) (y : B) := (ok a y).indicator (fun _ => weight a y) z
  have hrepr (z : A × (Fin N → A)) (y : B) :
      {u | ∀ j ≠ i, accept (u i) y (u j)}.indicator
        (fun u => weight (u i) y) (e z) = f z.1 z.2 y := by
    let u : Fin (N + 1) → A := @Fin.insertNth N (fun _ => A) i z.1 z.2
    change {u' | ∀ j ≠ i, accept (u' i) y (u' j)}.indicator (fun u' => weight (u' i) y) u = _
    have heq : (∀ j ≠ i, accept z.1 y (@Fin.insertNth N (fun _ => A) i z.1 z.2 j)) ↔ z.2 ∈ ok z.1 y := by
      simp only [ok, mem_univ_pi, mem_ofPred_eq]
      constructor
      · intro h j
        simpa only [Fin.insertNth_apply_succAbove] using h (i.succAbove j) (i.succAbove_ne j)
      · intro h j hj
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        simpa only [Fin.insertNth_apply_succAbove] using h k
    have hui : u i = z.1 := Fin.insertNth_apply_same _ _ _
    simp only [indicator, mem_ofPred_eq, hui, f]
    simp only [show (∀ j ≠ i, accept z.1 y (u j)) ↔ z.2 ∈ ok z.1 y from heq]
  have h_joint : Measurable (fun z : (A × (Fin N → A)) × B => f z.1.1 z.1.2 z.2) := by
    apply Measurable.indicator
    · exact hw.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · suffices hs : {z : (A × (Fin N → A)) × B | z.1.2 ∈ ok z.1.1 z.2} =
          ⋂ j : Fin N, (fun z : (A × (Fin N → A)) × B => ((z.1.1, z.2), z.1.2 j)) ⁻¹'
            {q : (A × B) × A | accept q.1.1 q.1.2 q.2} by
        change MeasurableSet {z : (A × (Fin N → A)) × B | z.1.2 ∈ ok z.1.1 z.2}
        rw [hs]
        apply MeasurableSet.iInter
        intro j
        exact ha.preimage (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
          ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)))
      ext z
      simp [ok]
  have h_joint' (a : A) : Measurable (uncurry (f a)) := by
    exact h_joint.comp (((measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  calc
    _ = ∫⁻ z : A × (Fin N → A), ∫⁻ y, f z.1 z.2 y ∂ν ∂(μ.prod μN) := by
      rw [← hpres.lintegral_comp_emb e.measurableEmbedding]
      simp only [hrepr]
    _ = ∫⁻ a, ∫⁻ z, ∫⁻ y, f a z y ∂ν ∂μN ∂μ :=
      lintegral_prod _ (h_joint.lintegral_prod_right').aemeasurable
    _ = ∫⁻ a, ∫⁻ y, ∫⁻ z, f a z y ∂μN ∂ν ∂μ := by
      apply lintegral_congr
      intro a
      exact lintegral_lintegral_swap (h_joint' a).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro a
      apply lintegral_congr
      intro y
      have hpart : MeasurableSet {v | accept a y v} :=
        ha.preimage (show Measurable (fun v : A => ((a, y), v)) from
          measurable_const.prodMk measurable_id)
      change (∫⁻ z, (ok a y).indicator (fun _ => weight a y) z ∂μN) = _
      rw [lintegral_indicator_const (MeasurableSet.univ_pi fun _ => hpart), mul_comm]
      simp [μN, Measure.pi_pi]

local notation "UnitSphere" E => Metric.sphere (0 : E) 1

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The rotation-invariant cone measure, normalized to have mass one. -/
noncomputable def uniformSphere (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure (UnitSphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ univ)⁻¹ • σ

instance [Nontrivial E] : IsProbabilityMeasure (uniformSphere E) where
  measure_univ := by
    rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (fun h => (Measure.toSphere_ne_zero (volume : Measure E)) (Measure.measure_univ_eq_zero.mp h))
      (measure_ne_top _ _)

end Sphere

section Cone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The portion of the open unit ball subtended by the spherical cap. -/
@[expose] def capCone (v : E) (t : ℝ) : Set E :=
  {x | 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ t * ‖x‖ ≤ ⟪v, x⟫}

omit [FiniteDimensional ℝ E] in
theorem measurableSet_capCone (v : E) (t : ℝ) : MeasurableSet (capCone v t) := by
  have ha : MeasurableSet {x : E | 0 < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hb : MeasurableSet {x : E | ‖x‖ < 1} :=
    measurableSet_lt continuous_norm.measurable measurable_const
  have hc : MeasurableSet {x : E | t * ‖x‖ ≤ ⟪v, x⟫} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact ha.inter (hb.inter hc)

theorem uniformSphere_cap_eq_cone [Nontrivial E] (v : E) (t : ℝ) :
    uniformSphere E {u | t ≤ ⟪v, (u : E)⟫} =
      volume (capCone v t) / volume (Metric.ball (0 : E) 1) := by
  let μ : Measure E := volume
  let s : Set (UnitSphere E) := {u | t ≤ ⟪v, (u : E)⟫}
  have hs : MeasurableSet s := measurableSet_le measurable_const (by fun_prop)
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' s) = capCone v t := by
    ext u
    constructor
    · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, rfl⟩
      have hwn : ‖(w : E)‖ = 1 := by
        rw [← dist_zero_right]
        exact w.property
      simp only [capCone, mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hwn, mul_one,
        real_inner_smul_right]
      exact ⟨hr.1, hr.2, by simpa [mul_comm] using mul_le_mul_of_nonneg_left hw hr.1.le⟩
    · rintro ⟨hu, hu₁, hvu⟩
      let w : E := ‖u‖⁻¹ • u
      have hwn : ‖w‖ = 1 := by
        simp [w, norm_smul, hu.ne']
      have hw : w ∈ Metric.sphere (0 : E) 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hwn
      refine ⟨‖u‖, ⟨hu, hu₁⟩, w, ⟨⟨w, hw⟩, ?_, rfl⟩, ?_⟩
      · change t ≤ ⟪v, w⟫
        rw [show w = ‖u‖⁻¹ • u from rfl, real_inner_smul_right]
        exact (le_inv_mul_iff₀ hu).2 (by simpa [mul_comm] using hvu)
      · simp [w, smul_smul, hu.ne']
  change uniformSphere E s = _
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, hcone]
  have hf : (↑(Module.finrank ℝ E) : ℝ≥0∞) ≠ 0 := by
    have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
    exact_mod_cast hd.ne'
  have hft : (↑(Module.finrank ℝ E) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl hf) (Or.inl hft), div_eq_mul_inv]
  calc
    _ = ((↑(Module.finrank ℝ E) : ℝ≥0∞)⁻¹ * ↑(Module.finrank ℝ E)) *
        (μ (capCone v t) * (μ (Metric.ball 0 1))⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hf hft, one_mul]

end Cone


section Isometries

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F]

/-- Orthogonal changes of variables preserve normalized spherical cap probabilities. -/
theorem uniformSphere_cap_isometric (e : E ≃ₗᵢ[ℝ] F) (x : E) (c : ℝ) :
    uniformSphere E {u | c ≤ ⟪x, (u : E)⟫} =
      uniformSphere F {u | c ≤ ⟪e x, (u : F)⟫} := by
  rw [uniformSphere_cap_eq_cone, uniformSphere_cap_eq_cone,
    ← e.measurePreserving.measure_preimage (measurableSet_capCone (e x) c).nullMeasurableSet,
    ← e.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet]
  have hcone : e ⁻¹' capCone (e x) c = capCone x c := by
    ext z
    simp [capCone, LinearIsometryEquiv.inner_map_map]
  have hball : e ⁻¹' Metric.ball (0 : F) 1 = Metric.ball (0 : E) 1 := by
    ext z
    simp [Metric.mem_ball, dist_zero_right]
  rw [hcone, hball]

/-- Tail probabilities of an inner product with a uniformly random unit
vector depend on the deterministic vector only through its norm. -/
theorem uniformSphere_inner_eq_of_norm_eq {x y : E} (hxy : ‖x‖ = ‖y‖) (c : ℝ) :
    uniformSphere E {u | ⟪x, (u : E)⟫ < c} =
    uniformSphere E {u | ⟪y, (u : E)⟫ < c} := by
  let R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (x - y))ᗮ.reflection
  have hR : R x = y := Submodule.reflection_sub hxy
  let S (x : E) : Set (UnitSphere E) := {u | c ≤ ⟪x, (u : E)⟫}
  have hs (x : E) : MeasurableSet (S x) :=
    measurableSet_le measurable_const (by fun_prop)
  have hS (x : E) : {u : UnitSphere E | ⟪x, (u : E)⟫ < c} = (S x)ᶜ := by
    ext u
    simp [S]
  rw [hS x, hS y, measure_compl (hs x) (measure_ne_top _ _),
    measure_compl (hs y) (measure_ne_top _ _)]
  congr 1
  simpa [S, hR] using uniformSphere_cap_isometric R x c

end Isometries

end Grokability

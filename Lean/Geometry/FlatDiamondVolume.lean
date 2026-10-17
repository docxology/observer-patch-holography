module
public import Geometry.SourceCausalBoundary
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Geometric section volumes of flat causal diamonds

These are volumes of the actual sets defined by the Euclidean causal
inequalities. Polynomial integrals are connected to those sets through
measure-preserving Cartesian coordinates and Fubini.
-/

namespace OPH.FlatDiamondVolume

open MeasureTheory Set Filter Real
open OPH.GoldenSourceAssignment OPH.GoldenSourceCountLimit OPH.SourceCausalBoundary
open scoped Topology

noncomputable section

def coordinateBall (x : Space) (r : ℝ) : Set Space := {y | spatialNorm (y - x) ≤ r}

theorem coordinateBall_measurable (x : Space) (r : ℝ) :
    MeasurableSet (coordinateBall x r) :=
  (isClosed_le (continuous_spatialNorm.comp (continuous_id.sub continuous_const))
    continuous_const).measurableSet

theorem coordinateBall_volume (x : Space) (r : ℝ) :
    volume (coordinateBall x r) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  have heq : coordinateBall x r = WithLp.toLp 2 ⁻¹'
      Metric.closedBall (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) r := by
    ext y
    simp only [coordinateBall, mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    rfl
  rw [heq, (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet, EuclideanSpace.volume_closedBall_fin_three]

theorem coordinateBall_volume_real (x : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coordinateBall x r) = (4 * Real.pi / 3) * r ^ 3 := by
  rw [measureReal_def, coordinateBall_volume, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity)]
  ring

theorem coordinateBall_compact (x : Space) (r : ℝ) : IsCompact (coordinateBall x r) := by
  have heq : coordinateBall x r = WithLp.ofLp ''
      Metric.closedBall (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) r := by
    ext y
    constructor
    · intro hy
      refine ⟨WithLp.toLp 2 y, ?_, rfl⟩
      exact hy
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [heq]
  exact (isCompact_closedBall (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) r).image
    (PiLp.continuous_ofLp 2 _)

theorem diamond_closed (c : ℝ) (p q : Spacetime) : IsClosed (diamond c p q) :=
  (isClosed_le continuous_const (continuous_margin_right c p)).inter
    (isClosed_le continuous_const (continuous_margin_left c q))

theorem diamond_subset_box {c : ℝ} (hc : 0 < c) (p q : Spacetime) :
    diamond c p q ⊆ Icc p.1 q.1 ×ˢ coordinateBall p.2 (c * (q.1 - p.1)) := by
  intro z hz
  have h₁ : spatialNorm (z.2 - p.2) ≤ c * (z.1 - p.1) := sub_nonneg.mp hz.1
  have h₂ : spatialNorm (q.2 - z.2) ≤ c * (q.1 - z.1) := sub_nonneg.mp hz.2
  have hn₁ : 0 ≤ spatialNorm (z.2 - p.2) := norm_nonneg _
  have hn₂ : 0 ≤ spatialNorm (q.2 - z.2) := norm_nonneg _
  have ht₁ : p.1 ≤ z.1 := by nlinarith
  have ht₂ : z.1 ≤ q.1 := by nlinarith
  refine ⟨⟨ht₁, ht₂⟩, ?_⟩
  change spatialNorm (z.2 - p.2) ≤ c * (q.1 - p.1)
  nlinarith

theorem diamond_compact {c : ℝ} (hc : 0 < c) (p q : Spacetime) :
    IsCompact (diamond c p q) :=
  (isCompact_Icc.prod (coordinateBall_compact p.2 (c * (q.1 - p.1)))).of_isClosed_subset
    (diamond_closed c p q) (diamond_subset_box hc p q)

theorem spatialNorm_sub_comm (x y : Space) : spatialNorm (x - y) = spatialNorm (y - x) := by
  change ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) - WithLp.toLp 2 y‖ =
    ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3)) - WithLp.toLp 2 x‖
  exact norm_sub_rev _ _

theorem vertical_section {c : ℝ} (hc : 0 ≤ c) (T t : ℝ) (x : Space) :
    (fun y : Space => (t, y)) ⁻¹' diamond c (0, x) (T, x) =
      coordinateBall x (c * min t (T - t)) := by
  ext y
  simp only [mem_preimage, diamond, mem_inter_iff, future, past, mem_ofPred_eq,
    margin, sub_zero, coordinateBall, spatialNorm_sub_comm x y]
  rw [mul_min_of_nonneg _ _ hc, le_min_iff]
  exact and_congr sub_nonneg sub_nonneg

def sectionVolume (c T t : ℝ) : ℝ := (4 * Real.pi / 3) * (c * min t (T - t)) ^ 3

theorem sectionVolume_continuous (c T : ℝ) : Continuous (sectionVolume c T) := by
  unfold sectionVolume
  fun_prop

theorem sectionVolume_integral {T : ℝ} (hT : 0 ≤ T) (c : ℝ) :
    ∫ t in (0 : ℝ)..T, sectionVolume c T t = Real.pi * c ^ 3 * T ^ 4 / 24 := by
  have hc := sectionVolume_continuous c T
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (T / 2))
    (hc.intervalIntegrable (T / 2) T)]
  have he₁ : ∫ t in (0 : ℝ)..(T / 2), sectionVolume c T t =
      ∫ t in (0 : ℝ)..(T / 2), (4 * Real.pi / 3) * (c * t) ^ 3 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    simp only [sectionVolume, min_eq_left (by linarith [ht.2] : t ≤ T - t)]
  have he₂ : ∫ t in (T / 2)..T, sectionVolume c T t =
      ∫ t in (T / 2)..T, (4 * Real.pi / 3) * (c * (T - t)) ^ 3 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    simp only [sectionVolume, min_eq_right (by linarith [ht.1] : T - t ≤ t)]
  have hd₁ (t : ℝ) : HasDerivAt (fun t : ℝ => (Real.pi * c ^ 3 / 3) * t ^ 4)
      ((4 * Real.pi / 3) * (c * t) ^ 3) t := by
    convert (hasDerivAt_pow 4 t).const_mul (Real.pi * c ^ 3 / 3) using 1
    ring
  have hd₂ (t : ℝ) : HasDerivAt (fun t : ℝ => -(Real.pi * c ^ 3 / 3) * (T - t) ^ 4)
      ((4 * Real.pi / 3) * (c * (T - t)) ^ 3) t := by
    convert (((hasDerivAt_id' (x := t)).const_sub T).pow 4).const_mul
      (-(Real.pi * c ^ 3 / 3)) using 1
    ring
  rw [he₁, he₂,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd₁ t)
      ((by fun_prop : Continuous fun t : ℝ => (4 * Real.pi / 3) * (c * t) ^ 3).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd₂ t)
      ((by fun_prop : Continuous fun t : ℝ => (4 * Real.pi / 3) * (c * (T - t)) ^ 3).intervalIntegrable _ _)]
  ring

/-- A contained vertical diamond has its actual coordinate four-volume.
The containment hypothesis is geometric, not an assumed integral formula. -/
theorem vertical_diamond_volume {T L c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (x : Space) (hinside : coordinateBall x (c * T / 2) ⊆ cube L) :
    (spaceTimeVolume T L).real (diamond c (0, x) (T, x)) =
      Real.pi * c ^ 3 * T ^ 4 / 24 := by
  classical
  let : IsFiniteMeasure (spaceTimeVolume T L) := spaceTimeVolume_finite T L
  let : IsFiniteMeasure (volume.restrict (cube L)) := cube_measure_finite L
  let : IsFiniteMeasure (volume.restrict (Ico 0 T)) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ico])
  have hD := diamond_measurable c (0, x) (T, x)
  have hi : Integrable ((diamond c (0, x) (T, x)).indicator (1 : Spacetime → ℝ))
      (spaceTimeVolume T L) := (integrable_const _).indicator hD
  rw [← integral_indicator_one hD]
  unfold spaceTimeVolume at hi ⊢
  rw [integral_prod _ hi]
  have hs : ∀ t ∈ Ico 0 T,
      (∫ y, (diamond c (0, x) (T, x)).indicator 1 (t, y) ∂volume.restrict (cube L)) =
        sectionVolume c T t := by
    intro t ht
    have hr : 0 ≤ c * min t (T - t) := mul_nonneg hc (le_min ht.1 (by linarith [ht.2]))
    have hsub : coordinateBall x (c * min t (T - t)) ⊆ cube L := by
      apply Subset.trans _ hinside
      intro y hy
      have hmin : min t (T - t) ≤ T / 2 := by
        have h₁ := min_le_left t (T - t)
        have h₂ := min_le_right t (T - t)
        linarith
      change spatialNorm (y - x) ≤ c * T / 2
      have hy' : spatialNorm (y - x) ≤ c * min t (T - t) := hy
      exact hy'.trans (by nlinarith [mul_le_mul_of_nonneg_left hmin hc])
    have heq : (fun y => (diamond c (0, x) (T, x)).indicator (1 : Spacetime → ℝ) (t, y)) =
        (coordinateBall x (c * min t (T - t))).indicator (1 : Space → ℝ) := by
      ext y
      rw [← vertical_section hc T t x]
      by_cases hz : (t, y) ∈ diamond c (0, x) (T, x) <;> simp [hz]
    rw [heq, integral_indicator_one (coordinateBall_measurable _ _),
      measureReal_restrict_apply (coordinateBall_measurable _ _), inter_eq_left.mpr hsub,
      coordinateBall_volume_real _ hr]
    rfl
  rw [setIntegral_congr_fun measurableSet_Ico hs, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT, sectionVolume_integral hT c]

#print axioms coordinateBall_volume_real
#print axioms vertical_diamond_volume

def coordinateVolume : Measure Spacetime :=
  (volume : Measure ℝ).prod (volume : Measure Space)

instance : SFinite coordinateVolume := by unfold coordinateVolume; infer_instance

instance : IsFiniteMeasureOnCompacts coordinateVolume := by
  unfold coordinateVolume
  infer_instance

theorem coordinate_future_null {c : ℝ} (hc : c ≠ 0) (p : Spacetime) :
    coordinateVolume {q | margin c p q = 0} = 0 := by
  have hmeas : MeasurableSet {q | margin c p q = 0} :=
    (isClosed_eq (continuous_margin_right c p) continuous_const).measurableSet
  unfold coordinateVolume
  rw [Measure.prod_apply_symm hmeas]
  have heq (x : Space) : (fun t : ℝ => (t, x)) ⁻¹' {q | margin c p q = 0} =
      {p.1 + spatialNorm (x - p.2) / c} := by
    ext t
    simp only [mem_preimage, mem_ofPred_eq, margin, mem_singleton_iff]
    constructor
    · intro h
      have hh : t - p.1 = spatialNorm (x - p.2) / c :=
        (eq_div_iff hc).mpr (by nlinarith)
      linarith
    · intro h
      rw [h]
      nlinarith [div_mul_cancel₀ (spatialNorm (x - p.2)) hc]
  simp only [heq, measure_singleton, lintegral_zero]

theorem spatialNorm_sub_triangle (x y z : Space) :
    spatialNorm (z - x) ≤ spatialNorm (z - y) + spatialNorm (y - x) := by
  simpa only [dist_eq_norm, spatialNorm, WithLp.toLp_sub] using
    dist_triangle (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 y) (WithLp.toLp 2 x)

theorem causal_trans {c : ℝ} {p q r : Spacetime}
    (hpq : 0 ≤ margin c p q) (hqr : 0 ≤ margin c q r) : 0 ≤ margin c p r := by
  unfold margin at *
  have hh := spatialNorm_sub_triangle p.2 q.2 r.2
  nlinarith

theorem vertical_diamond_subset {T c : ℝ} (hc : 0 < c) (x : Space) :
    diamond c (0, x) (T, x) ⊆ Icc 0 T ×ˢ coordinateBall x (c * T / 2) := by
  intro z hz
  have h₁ : spatialNorm (z.2 - x) ≤ c * z.1 := by
    have hh : 0 ≤ c * (z.1 - 0) - spatialNorm (z.2 - x) := hz.1
    simpa only [sub_zero] using (sub_nonneg.mp hh)
  have h₂ : spatialNorm (z.2 - x) ≤ c * (T - z.1) := by
    have hh : 0 ≤ c * (T - z.1) - spatialNorm (x - z.2) := hz.2
    simpa only [spatialNorm_sub_comm x z.2] using (sub_nonneg.mp hh)
  have hn := norm_nonneg (WithLp.toLp 2 (z.2 - x) : EuclideanSpace ℝ (Fin 3))
  change 0 ≤ spatialNorm (z.2 - x) at hn
  have ht₁ : 0 ≤ z.1 := by nlinarith
  have ht₂ : z.1 ≤ T := by nlinarith
  refine ⟨⟨ht₁, ht₂⟩, ?_⟩
  change spatialNorm (z.2 - x) ≤ c * T / 2
  nlinarith

theorem vertical_diamond_finite {T c : ℝ} (hc : 0 < c) (x : Space) :
    coordinateVolume (diamond c (0, x) (T, x)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono (vertical_diamond_subset hc x))
  rw [coordinateVolume, Measure.prod_prod, Real.volume_Icc, coordinateBall_volume]
  finiteness

/-- Unrestricted coordinate volume of an actual vertical diamond. -/
theorem full_vertical_diamond_volume {T c : ℝ} (hT : 0 ≤ T) (hc : 0 < c) (x : Space) :
    coordinateVolume.real (diamond c (0, x) (T, x)) = Real.pi * c ^ 3 * T ^ 4 / 24 := by
  classical
  have hD := diamond_measurable c (0, x) (T, x)
  let : IsFiniteMeasure (coordinateVolume.restrict (diamond c (0, x) (T, x))) :=
    isFiniteMeasure_restrict.mpr (vertical_diamond_finite hc x)
  have hi : Integrable ((diamond c (0, x) (T, x)).indicator (1 : Spacetime → ℝ))
      coordinateVolume := by
    rw [integrable_indicator_iff hD]
    exact integrable_const _
  rw [← integral_indicator_one hD]
  unfold coordinateVolume at hi ⊢
  rw [integral_prod _ hi]
  have hsec (t : ℝ) :
      (∫ y, (diamond c (0, x) (T, x)).indicator 1 (t, y)) =
        (Icc 0 T).indicator (sectionVolume c T) t := by
    by_cases ht : t ∈ Icc 0 T
    · rw [indicator_of_mem ht]
      have hr : 0 ≤ c * min t (T - t) :=
        mul_nonneg hc.le (le_min ht.1 (sub_nonneg.mpr ht.2))
      have heq : (fun y => (diamond c (0, x) (T, x)).indicator (1 : Spacetime → ℝ) (t, y)) =
          (coordinateBall x (c * min t (T - t))).indicator (1 : Space → ℝ) := by
        ext y
        rw [← vertical_section hc.le T t x]
        by_cases hz : (t, y) ∈ diamond c (0, x) (T, x) <;> simp [hz]
      rw [heq, integral_indicator_one (coordinateBall_measurable _ _),
        coordinateBall_volume_real _ hr]
      rfl
    · rw [indicator_of_notMem ht]
      have hz (y : Space) : (t, y) ∉ diamond c (0, x) (T, x) :=
        fun hy => ht (vertical_diamond_subset hc x hy).1
      simp [hz]
  simp_rw [hsec]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT, sectionVolume_integral hT c]

#print axioms full_vertical_diamond_volume

end
end OPH.FlatDiamondVolume

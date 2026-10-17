module
public import Geometry.FlatLorentzVolume
public import Geometry.OrderingFractionFourDimensional
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

set_option autoImplicit false

namespace OPH.FlatDiamondPairIntegral

open MeasureTheory Set Real
open OPH.SourceCausalBoundary OPH.FlatDiamondVolume OPH.FlatLorentzVolume
open scoped Topology

noncomputable section

def closedPairs (c : ℝ) (p q : Spacetime) : Set (Spacetime × Spacetime) :=
  {z | z.1 ∈ diamond c p q ∧ z.2 ∈ diamond c p q ∧ 0 ≤ margin c z.1 z.2}

theorem closedPairs_measurable (c : ℝ) (p q : Spacetime) :
    MeasurableSet (closedPairs c p q) :=
  ((diamond_measurable c p q).preimage measurable_fst).inter
    (((diamond_measurable c p q).preimage measurable_snd).inter
      (isClosed_le continuous_const (continuous_margin c)).measurableSet)

theorem closedPairs_section {c : ℝ} {p q x : Spacetime} (hx : x ∈ diamond c p q) :
    Prod.mk x ⁻¹' closedPairs c p q = diamond c x q := by
  ext y
  constructor
  · intro hy
    exact ⟨hy.2.2, hy.2.1.2⟩
  · intro hy
    exact ⟨hx, ⟨causal_trans hx.1 hy.1, hy.2⟩, hy.1⟩

/-- Fubini connects the geometric pair set to future subdiamond volumes. -/
theorem closedPairs_integral {c : ℝ} (hc : 0 < c) (p q : Spacetime) :
    (coordinateVolume.prod coordinateVolume).real (closedPairs c p q) =
      ∫ x in diamond c p q, coordinateVolume.real (diamond c x q) ∂coordinateVolume := by
  classical
  have hD := diamond_measurable c p q
  have hC := closedPairs_measurable c p q
  have hdf : coordinateVolume (diamond c p q) ≠ ⊤ :=
    (diamond_compact hc p q).measure_ne_top
  have hcf : (coordinateVolume.prod coordinateVolume) (closedPairs c p q) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono (show closedPairs c p q ⊆
      diamond c p q ×ˢ diamond c p q from fun _ h => ⟨h.1, h.2.1⟩))
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hdf hdf
  let : IsFiniteMeasure ((coordinateVolume.prod coordinateVolume).restrict (closedPairs c p q)) :=
    isFiniteMeasure_restrict.mpr hcf
  have hi : Integrable ((closedPairs c p q).indicator (1 : Spacetime × Spacetime → ℝ))
      (coordinateVolume.prod coordinateVolume) := by
    rw [integrable_indicator_iff hC]
    exact integrable_const _
  rw [← integral_indicator_one hC, integral_prod _ hi]
  have hs (x : Spacetime) : (∫ y, (closedPairs c p q).indicator 1 (x, y) ∂coordinateVolume) =
      (diamond c p q).indicator (fun x => coordinateVolume.real (diamond c x q)) x := by
    by_cases hx : x ∈ diamond c p q
    · rw [indicator_of_mem hx]
      have heq : (fun y => (closedPairs c p q).indicator (1 : Spacetime × Spacetime → ℝ) (x, y)) =
          (diamond c x q).indicator (1 : Spacetime → ℝ) := by
        ext y
        rw [← closedPairs_section hx]
        by_cases hy : (x, y) ∈ closedPairs c p q <;> simp [hy]
      rw [heq, integral_indicator_one (diamond_measurable c x q)]
    · rw [indicator_of_notMem hx]
      have hy (y : Spacetime) : (x, y) ∉ closedPairs c p q := fun h => hx h.1
      simp [hy]
  simp_rw [hs]
  exact integral_indicator hD

theorem closedPairs_polynomial (p q : Spacetime) :
    (coordinateVolume.prod coordinateVolume).real (closedPairs 1 p q) =
      ∫ x in diamond 1 p q,
        Real.pi * ((q.1 - x.1) ^ 2 - spatialNorm (q.2 - x.2) ^ 2) ^ 2 / 24 ∂coordinateVolume := by
  rw [closedPairs_integral (by norm_num : (0 : ℝ) < 1)]
  apply setIntegral_congr_fun (diamond_measurable 1 p q)
  intro x hx
  apply causal_diamond_volume x q
  have hh : 0 ≤ 1 * (q.1 - x.1) - spatialNorm (q.2 - x.2) := hx.2
  simpa only [one_mul] using sub_nonneg.mp hh

/-- Radial integration for the actual three-dimensional coordinate ball. -/
theorem radial_ball_integral (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in coordinateBall 0 R, f (spatialNorm x)) =
      4 * Real.pi * ∫ r in (0 : ℝ)..R, r ^ 2 * f r := by
  classical
  let g : ℝ → ℝ := (Iic R).indicator f
  have heq : (fun x : Space => g (spatialNorm x)) =
      (coordinateBall 0 R).indicator (fun x => f (spatialNorm x)) := by
    ext x
    simp [g, coordinateBall, sub_zero, indicator_apply]
  rw [← integral_indicator (coordinateBall_measurable 0 R), ← heq]
  have hp := (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 Space).measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin 3) => g ‖x‖)
  change (∫ x : Space, g ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖) = _
  rw [hp, integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 3))) g]
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Metric.ball 0 1) =
      Real.pi * 4 / 3 := by
    simp [measureReal_def, EuclideanSpace.volume_ball_fin_three]
    positivity
  simp only [finrank_euclideanSpace, Fintype.card_fin, hball,
    Nat.reduceSub, nsmul_eq_mul, smul_eq_mul]
  have he (r : ℝ) : r ^ 2 * g r = (Iic R).indicator (fun r => r ^ 2 * f r) r := by
    by_cases hr : r ≤ R <;> simp [g, hr]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic R ∩ Ioi (0 : ℝ) = Ioc 0 R := by ext r; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]; tauto
  rw [hset, ← intervalIntegral.integral_of_le hR]
  ring

/-- Fubini over the actual vertical diamond, with its exact spherical sections. -/
theorem vertical_integral (F : Spacetime → ℝ) (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ z in diamond 1 (0, 0) (T, 0), F z ∂coordinateVolume) =
      ∫ t in (0 : ℝ)..T, ∫ y in coordinateBall 0 (min t (T - t)), F (t, y) := by
  classical
  have hD := diamond_measurable 1 (0, 0) (T, 0)
  have hi : Integrable ((diamond 1 (0, 0) (T, 0)).indicator F) coordinateVolume :=
    (integrable_indicator_iff hD).mpr
      (hF.continuousOn.integrableOn_compact (diamond_compact (by norm_num) _ _))
  rw [← integral_indicator hD]
  unfold coordinateVolume at hi ⊢
  rw [integral_prod _ hi]
  have hsec (t : ℝ) :
      (∫ y, (diamond 1 (0, 0) (T, 0)).indicator F (t, y)) =
        (Icc 0 T).indicator
          (fun t => ∫ y in coordinateBall 0 (min t (T - t)), F (t, y)) t := by
    by_cases ht : t ∈ Icc 0 T
    · rw [indicator_of_mem ht, ← integral_indicator (coordinateBall_measurable _ _)]
      apply integral_congr_ae
      filter_upwards [] with y
      have hset := vertical_section (by norm_num : (0 : ℝ) ≤ 1) T t (0 : Space)
      simp only [one_mul] at hset
      have hm : (t, y) ∈ diamond 1 (0, 0) (T, 0) ↔
          y ∈ coordinateBall 0 (min t (T - t)) := Set.ext_iff.mp hset y
      simp only [indicator_apply, hm]
    · rw [indicator_of_notMem ht]
      have hz (y : Space) : (t, y) ∉ diamond 1 (0, 0) (T, 0) :=
        fun hy => ht (vertical_diamond_subset (by norm_num : (0 : ℝ) < 1) 0 hy).1
      simp [hz]
  simp_rw [hsec]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT]

/-- The geometric pair measure equals the evaluated polynomial integral. -/
theorem vertical_closedPairs_volume {T : ℝ} (hT : 0 ≤ T) :
    (coordinateVolume.prod coordinateVolume).real (closedPairs 1 (0, 0) (T, 0)) =
      Real.pi ^ 2 * T ^ 8 / 11520 := by
  rw [closedPairs_polynomial]
  have hF : Continuous (fun z : Spacetime =>
      Real.pi * ((T - z.1) ^ 2 - spatialNorm (0 - z.2) ^ 2) ^ 2 / 24) := by
    have hn : Continuous (fun z : Spacetime => spatialNorm (0 - z.2)) :=
      continuous_spatialNorm.comp (continuous_const.sub continuous_snd)
    fun_prop
  rw [vertical_integral _ hF hT]
  have heq : (∫ t in (0 : ℝ)..T, ∫ y in coordinateBall 0 (min t (T - t)),
      Real.pi * ((T - t) ^ 2 - spatialNorm (0 - y) ^ 2) ^ 2 / 24) =
      (Real.pi ^ 2 / 6) * ∫ t in (0 : ℝ)..T,
        OPH.OrderingFractionFourDimensional.innerVolume T t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    have hr : 0 ≤ min t (T - t) := le_min ht.1 (sub_nonneg.mpr ht.2)
    simp_rw [spatialNorm_sub_comm (0 : Space), sub_zero]
    rw [radial_ball_integral (fun r => Real.pi * ((T - t) ^ 2 - r ^ 2) ^ 2 / 24) hr]
    have hf : (fun r : ℝ => r ^ 2 * (Real.pi * ((T - t) ^ 2 - r ^ 2) ^ 2 / 24)) =
        fun r => (Real.pi / 24) * (r ^ 2 * ((T - t) ^ 2 - r ^ 2) ^ 2) := by
      ext r
      ring
    rw [hf, intervalIntegral.integral_const_mul]
    unfold OPH.OrderingFractionFourDimensional.innerVolume
    ring
  rw [heq, OPH.OrderingFractionFourDimensional.orderedPair_double_integral T hT]
  ring

theorem vertical_closedPairs_eq_volume_sq {T : ℝ} (hT : 0 ≤ T) :
    (coordinateVolume.prod coordinateVolume).real (closedPairs 1 (0, 0) (T, 0)) =
      coordinateVolume.real (diamond 1 (0, 0) (T, 0)) ^ 2 / 20 := by
  rw [vertical_closedPairs_volume hT, full_vertical_diamond_volume hT (by norm_num)]
  ring

/-- A causal change of variables transports the actual pair set. -/
theorem closedPairs_preimage (c d : ℝ) (p q p' q' : Spacetime) (f : Spacetime → Spacetime)
    (hD : diamond c p q = f ⁻¹' diamond d p' q')
    (hc : ∀ x y, (0 ≤ margin c x y ↔ 0 ≤ margin d (f x) (f y))) :
    closedPairs c p q = Prod.map f f ⁻¹' closedPairs d p' q' := by
  ext z
  simp only [closedPairs, mem_ofPred_eq, hD, mem_preimage, Prod.map_fst, Prod.map_snd, hc]

theorem boost_causal_iff {T τ : ℝ} (x : Space) (hτ : 0 < τ)
    (hT : spatialNorm x < T) (hrel : T ^ 2 - dot x x = τ ^ 2) (p q : Spacetime) :
    0 ≤ margin 1 p q ↔ 0 ≤ margin 1 (boost T τ x p) (boost T τ x q) := by
  have hh := boost_future_iff x hτ hT hrel (q - p)
  rw [boost_sub] at hh
  simpa only [margin, one_mul, Prod.fst_sub, Prod.snd_sub, sub_nonneg] using hh.symm

theorem tilted_closedPairs_eq_volume_sq {T : ℝ} (x : Space) (hT : spatialNorm x < T) :
    (coordinateVolume.prod coordinateVolume).real (closedPairs 1 0 (T, x)) =
      coordinateVolume.real (diamond 1 0 (T, x)) ^ 2 / 20 := by
  have hTp : 0 < T := (spatialNorm_nonneg x).trans_lt hT
  have hq : 0 < T ^ 2 - spatialNorm x ^ 2 := by nlinarith [spatialNorm_nonneg x]
  let τ := Real.sqrt (T ^ 2 - spatialNorm x ^ 2)
  have hτ : 0 < τ := Real.sqrt_pos.mpr hq
  have hrel : T ^ 2 - dot x x = τ ^ 2 := by rw [dot_self]; exact (Real.sq_sqrt hq.le).symm
  have hmp := boost_measurePreserving x hτ.ne' (show T + τ ≠ 0 by linarith) hrel
  have hD := diamond_boost_preimage x hτ hT hrel
  have hC := closedPairs_preimage 1 1 0 (T, x) 0 (τ, 0) (boost T τ x) hD
    (boost_causal_iff x hτ hT hrel)
  rw [measureReal_def, hC, (hmp.prod hmp).measure_preimage
    (closedPairs_measurable 1 0 (τ, 0)).nullMeasurableSet]
  rw [measureReal_def, hD, hmp.measure_preimage (diamond_measurable 1 0 (τ, 0)).nullMeasurableSet]
  exact vertical_closedPairs_eq_volume_sq hτ.le

theorem causal_closedPairs_eq_volume_sq (p q : Spacetime)
    (hpq : spatialNorm (q.2 - p.2) < q.1 - p.1) :
    (coordinateVolume.prod coordinateVolume).real (closedPairs 1 p q) =
      coordinateVolume.real (diamond 1 p q) ^ 2 / 20 := by
  have hmp := coordinate_sub_preserving p
  have hD := diamond_translate_preimage 1 p q
  have hC := closedPairs_preimage 1 1 p q 0 (q - p) (fun z => z - p) hD
    (fun x y => by rw [margin_translate])
  rw [measureReal_def, hC, (hmp.prod hmp).measure_preimage
    (closedPairs_measurable 1 0 (q - p)).nullMeasurableSet]
  rw [measureReal_def, hD, hmp.measure_preimage (diamond_measurable 1 0 (q - p)).nullMeasurableSet]
  exact tilted_closedPairs_eq_volume_sq (q.2 - p.2) hpq

#print axioms causal_closedPairs_eq_volume_sq
#print axioms vertical_closedPairs_eq_volume_sq
#print axioms closedPairs_integral
#print axioms closedPairs_polynomial
#print axioms radial_ball_integral

end
end OPH.FlatDiamondPairIntegral

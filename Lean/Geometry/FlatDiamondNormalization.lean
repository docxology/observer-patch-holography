module
public import Geometry.FlatDiamondPairIntegral
public import Geometry.GoldenSourcePairLimit
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

set_option autoImplicit false

namespace OPH.FlatDiamondNormalization

open MeasureTheory Set Real Filter
open OPH.SourceCausalBoundary OPH.FlatDiamondVolume OPH.FlatLorentzVolume
open OPH.FlatDiamondPairIntegral
open scoped Topology

noncomputable section

def speed (c : ℝ) : Spacetime → Spacetime := Prod.map (c * ·) id

theorem speed_measurable (c : ℝ) : Measurable (speed c) :=
  (measurable_const_mul c).prodMap measurable_id

theorem speed_map {c : ℝ} (hc : 0 < c) :
    Measure.map (speed c) coordinateVolume = ENNReal.ofReal c⁻¹ • coordinateVolume := by
  unfold speed coordinateVolume
  rw [← Measure.map_prod_map _ _ (measurable_const_mul c) measurable_id,
    Real.map_volume_mul_left hc.ne', Measure.map_id, Measure.prod_smul_left,
    abs_of_pos (inv_pos.mpr hc)]

theorem speed_preimage_real {c : ℝ} (hc : 0 < c) {s : Set Spacetime} (hs : MeasurableSet s) :
    coordinateVolume.real (speed c ⁻¹' s) = c⁻¹ * coordinateVolume.real s := by
  rw [measureReal_def, ← Measure.map_apply (speed_measurable c) hs, speed_map hc,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le)]
  rfl

theorem speed_pair_preimage_real {c : ℝ} (hc : 0 < c) {s : Set (Spacetime × Spacetime)}
    (hs : MeasurableSet s) :
    (coordinateVolume.prod coordinateVolume).real (Prod.map (speed c) (speed c) ⁻¹' s) =
      c⁻¹ ^ 2 * (coordinateVolume.prod coordinateVolume).real s := by
  rw [measureReal_def, ← Measure.map_apply ((speed_measurable c).prodMap (speed_measurable c)) hs,
    ← Measure.map_prod_map _ _ (speed_measurable c) (speed_measurable c), speed_map hc,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le)]
  simp only [measureReal_def]
  ring

theorem margin_speed (c : ℝ) (p q : Spacetime) :
    margin 1 (speed c p) (speed c q) = margin c p q := by
  simp only [margin, speed, Prod.map_fst, Prod.map_snd, id_eq, one_mul]
  ring

theorem diamond_speed (c : ℝ) (p q : Spacetime) :
    diamond c p q = speed c ⁻¹' diamond 1 (speed c p) (speed c q) := by
  ext z
  simp only [diamond, future, past, mem_inter_iff, mem_ofPred_eq, mem_preimage, margin_speed]

/-- The geometric pair-volume identity holds at every supplied positive speed. -/
theorem closedPairs_eq_volume_sq {c : ℝ} (hc : 0 < c) (p q : Spacetime)
    (hpq : spatialNorm (q.2 - p.2) < c * (q.1 - p.1)) :
    (coordinateVolume.prod coordinateVolume).real (closedPairs c p q) =
      coordinateVolume.real (diamond c p q) ^ 2 / 20 := by
  have hC := closedPairs_preimage c 1 p q (speed c p) (speed c q) (speed c)
    (diamond_speed c p q) (fun x y => by rw [margin_speed])
  rw [hC, speed_pair_preimage_real hc (closedPairs_measurable _ _ _),
    causal_closedPairs_eq_volume_sq _ _ (by simpa only [speed, Prod.map_fst, Prod.map_snd,
      id_eq, ← mul_sub] using hpq), diamond_speed c p q,
    speed_preimage_real hc (diamond_measurable _ _ _)]
  ring

theorem timelike_diamond_volume {c : ℝ} (hc : 0 < c) (p q : Spacetime)
    (hpq : spatialNorm (q.2 - p.2) < c * (q.1 - p.1)) :
    coordinateVolume.real (diamond c p q) =
      Real.pi * ((c * (q.1 - p.1)) ^ 2 - spatialNorm (q.2 - p.2) ^ 2) ^ 2 / (24 * c) := by
  rw [diamond_speed c p q, speed_preimage_real hc (diamond_measurable _ _ _),
    causal_diamond_volume _ _ (by simpa only [speed, Prod.map_fst, Prod.map_snd,
      id_eq, ← mul_sub] using hpq.le)]
  simp only [speed, Prod.map_fst, Prod.map_snd, id_eq, ← mul_sub]
  ring

theorem timelike_diamond_volume_pos {c : ℝ} (hc : 0 < c) (p q : Spacetime)
    (hpq : spatialNorm (q.2 - p.2) < c * (q.1 - p.1)) :
    0 < coordinateVolume.real (diamond c p q) := by
  rw [timelike_diamond_volume hc p q hpq]
  have hsq : 0 < (c * (q.1 - p.1)) ^ 2 - spatialNorm (q.2 - p.2) ^ 2 := by
    nlinarith [spatialNorm_nonneg (q.2 - p.2)]
  positivity

open OPH.GoldenSourceAssignment OPH.GoldenSourceCountLimit
open OPH.GoldenSourceCausalLimit OPH.GoldenSourcePairLimit

theorem spaceTimeVolume_restrict (T L : ℝ) :
    spaceTimeVolume T L = coordinateVolume.restrict (Icc 0 T ×ˢ cube L) := by
  rw [spaceTimeVolume, restrict_Ico_eq_restrict_Icc, Measure.prod_restrict]
  rfl

theorem unclipped_volume {T L c : ℝ} (p q : Spacetime)
    (hbox : diamond c p q ⊆ Icc 0 T ×ˢ cube L) :
    (spaceTimeVolume T L).real (diamond c p q) = coordinateVolume.real (diamond c p q) := by
  rw [spaceTimeVolume_restrict, measureReal_restrict_apply (diamond_measurable _ _ _),
    inter_eq_left.mpr hbox]

theorem unclipped_closedPairs {T L c : ℝ} (p q : Spacetime)
    (hbox : diamond c p q ⊆ Icc 0 T ×ˢ cube L) :
    ((spaceTimeVolume T L).prod (spaceTimeVolume T L)).real (closedPairs c p q) =
      (coordinateVolume.prod coordinateVolume).real (closedPairs c p q) := by
  rw [spaceTimeVolume_restrict, Measure.prod_restrict,
    measureReal_restrict_apply (closedPairs_measurable _ _ _), inter_eq_left.mpr]
  exact fun _ hz => ⟨hbox hz.1, hbox hz.2.1⟩

theorem strictPair_volume_eq_closed (T L : ℝ) {c : ℝ} (hc : c ≠ 0) (p q : Spacetime) :
    ((spaceTimeVolume T L).prod (spaceTimeVolume T L)).real (pairRegion c p q) =
      ((spaceTimeVolume T L).prod (spaceTimeVolume T L)).real (closedPairs c p q) := by
  apply measureReal_congr
  have hn : ∀ᵐ z ∂((spaceTimeVolume T L).prod (spaceTimeVolume T L)),
      margin c z.1 z.2 ≠ 0 := by
    simpa only [ae_iff, not_not] using pair_null T L hc
  filter_upwards [hn] with z hz
  have hm : 0 < margin c z.1 z.2 ↔ 0 ≤ margin c z.1 z.2 :=
    ⟨le_of_lt, fun h => lt_of_le_of_ne h hz.symm⟩
  apply propext
  change (z ∈ pairRegion c p q ↔ z ∈ closedPairs c p q)
  simp only [pairRegion, closedPairs, mem_ofPred_eq, hm]

/-- The actual generated inclusive interval counts converge to the full
Alexandrov volume when the limiting diamond fits in the supplied window. -/
theorem generated_interval_count_tendsto_volume {T L c : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hc : 0 < c) (e f : (n : ℕ) → Label (n + 2) T L c) {p q : Spacetime}
    (he : Tendsto (fun n => position (e n)) atTop (𝓝 p))
    (hf : Tendsto (fun n => position (f n)) atTop (𝓝 q))
    (hpq : spatialNorm (q.2 - p.2) < c * (q.1 - p.1))
    (hbox : diamond c p q ⊆ Icc 0 T ×ˢ cube L) :
    Tendsto (fun n => eventWeight (n + 2) L c * (intervalCount (e n) (f n) : ℝ)) atTop
      (𝓝 (Real.pi * ((c * (q.1 - p.1)) ^ 2 - spatialNorm (q.2 - p.2) ^ 2) ^ 2 / (24 * c))) := by
  have hh := generated_interval_count_tendsto hT hL hc e f he hf
  rw [unclipped_volume p q hbox, timelike_diamond_volume hc p q hpq] at hh
  exact hh

/-- The four-dimensional ordering-fraction limit for the actual generated
strict-pair count, with N(N-1) normalization and the supplied positive speed. -/
theorem ordering_fraction_tendsto_one_tenth {T L c : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hc : 0 < c) (e f : (n : ℕ) → Label (n + 2) T L c) {p q : Spacetime}
    (he : Tendsto (fun n => position (e n)) atTop (𝓝 p))
    (hf : Tendsto (fun n => position (f n)) atTop (𝓝 q))
    (hpq : spatialNorm (q.2 - p.2) < c * (q.1 - p.1))
    (hbox : diamond c p q ⊆ Icc 0 T ×ˢ cube L) :
    Tendsto (fun n => 2 * (strictPairCount (e n) (f n) : ℝ) /
      ((intervalCount (e n) (f n) : ℝ) * ((intervalCount (e n) (f n) : ℝ) - 1)))
      atTop (𝓝 (1 / 10)) := by
  have hV : (spaceTimeVolume T L).real (diamond c p q) ≠ 0 := by
    rw [unclipped_volume p q hbox]
    exact (timelike_diamond_volume_pos hc p q hpq).ne'
  have hh := ordering_fraction_tendsto_geometric hT hL hc e f he hf hV
  rw [strictPair_volume_eq_closed T L hc.ne' p q, unclipped_closedPairs p q hbox,
    closedPairs_eq_volume_sq hc p q hpq, unclipped_volume p q hbox] at hh
  have hne := (timelike_diamond_volume_pos hc p q hpq).ne'
  have heq : 2 * (coordinateVolume.real (diamond c p q) ^ 2 / 20) /
      coordinateVolume.real (diamond c p q) ^ 2 = 1 / 10 := by field_simp; ring
  rwa [heq] at hh

#print axioms ordering_fraction_tendsto_one_tenth
#print axioms generated_interval_count_tendsto_volume
#print axioms closedPairs_eq_volume_sq
#print axioms timelike_diamond_volume

end
end OPH.FlatDiamondNormalization

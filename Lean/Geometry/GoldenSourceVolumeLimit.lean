module
public import Geometry.SourceNetVolumeError
public import Geometry.GoldenSourceCausalLimit

@[expose] public section

set_option autoImplicit false

namespace OPH.GoldenSourceVolumeLimit

open MeasureTheory Set Filter Real
open OPH.GoldenSourceAssignment OPH.GoldenSourceCountLimit OPH.GoldenSourceCausalLimit
open OPH.SourceCausalBoundary OPH.FlatDiamondVolume OPH.SourceNetVolumeError OPH.SourceCountTransport
open scoped Topology BigOperators Classical

noncomputable section

def alignedVolume (n : ℕ) (L c : ℝ) (K : ℕ) (b : Fin 3 → Fin (Nat.fib n)) : ℝ :=
  weightedVolume (cell n L) (site L) (radius n L) c K (site L b)

def alignedCount (n : ℕ) (L : ℝ) (K : ℕ) (b : Fin 3 → Fin (Nat.fib n)) : ℕ :=
  count (fun jb : Fin (K + 1) × (Fin 3 → Fin (Nat.fib n)) =>
    layerMember (site L) (radius n L) K jb.1.val (site L b) jb.2)

/-- Exact equality to the raw inclusive generated interval count. -/
theorem alignedVolume_eq_count {n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (c : ℝ) (K : ℕ) (b : Fin 3 → Fin (Nat.fib n)) :
    alignedVolume n L c K b =
      sourceDelta n L c * (L ^ 3 / (Nat.fib n : ℝ) ^ 3) * (alignedCount n L K b : ℝ) := by
  unfold alignedVolume weightedVolume layerMass
  simp_rw [cell_mass hn hL.le]
  rw [← Fin.sum_univ_eq_sum_range]
  have hh := constant_weight_count (L ^ 3 / (Nat.fib n : ℝ) ^ 3)
    (fun jb : Fin (K + 1) × (Fin 3 → Fin (Nat.fib n)) =>
      layerMember (site L) (radius n L) K jb.1.val (site L b) jb.2)
  rw [Fintype.sum_prod_type] at hh
  rw [hh]
  simp only [alignedCount, sourceDelta, radius, mul_assoc]

/-- The finite bound uses the actual golden sites and their proved cell masses
and assignment, without requiring representatives to lie in their cells. -/
theorem golden_weighted_error {n : ℕ} (hn : 0 < n) {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (hsmall : 2 * assignment n L < radius n L) (K : ℕ) (b : Fin 3 → Fin (Nat.fib n))
    (hbuffer : coordinateBall (WithLp.ofLp (site L b)) ((K : ℝ) * radius n L / 2 + assignment n L) ⊆ cube L) :
    let δ := sourceDelta n L c
    let T := (K : ℝ) * δ
    |alignedVolume n L c K b - Real.pi * c ^ 3 * T ^ 4 / 24| ≤
      4 * Real.pi * (T + δ) * (c * T / 2 + assignment n L) ^ 2 *
        (assignment n L + c * T * assignment n L / radius n L) +
      Real.pi * c ^ 3 * T ^ 3 * δ / 2 := by
  apply weighted_alexandrov_error (cell n L) (site L) (domain_convex L) (population_subset hL)
    (population_covers hn hL) (assignment_nonneg n hL.le) hsmall (assignment_nonneg n hL.le) hc
    (cell_measurable n L) (fun _ _ hij => (cell_disjoint hn hL hij).aedisjoint)
    (fun i => isFiniteMeasure_restrict.mp (cell_measure_finite n L i))
  · exact Eventually.of_forall fun y hy => mem_iUnion.mp ((cell_cover hn hL).symm ▸
      (show y ∈ cube L from fun i _ => hy i))
  · intro i
    exact Eventually.of_forall fun y hy => by
      simpa only [dist_eq_norm, assignment] using tensor_assignment hn hL.le i (WithLp.toLp 2 y)
        (fun k => ⟨(hy k (mem_univ k)).1, (hy k (mem_univ k)).2.le⟩)
  · exact mem_range_self b
  · intro y hy i
    exact hbuffer hy i (mem_univ i)

theorem assignment_tendsto (L : ℝ) :
    Tendsto (fun n => assignment (n + 2) L) atTop (𝓝 0) := by
  exact (tendsto_natCast_atTop_atTop.comp Nat.fib_add_two_strictMono.tendsto_atTop).const_div_atTop
    (2 * Real.sqrt 3 * L)

theorem eventually_inner_radius {L : ℝ} (hL : 0 < L) :
    ∀ᶠ n in atTop, 2 * assignment (n + 2) L < radius (n + 2) L := by
  have hh := (assignment_ratio_tendsto hL).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hh] with n hn
  have hp := radius_pos (by omega : 0 < n + 2) hL
  have h := (div_lt_iff₀ hp).mp hn
  linarith

/-- Aligned golden intervals converge in weighted volume. Layer counts may
vary with refinement; only their physical durations must converge. -/
theorem alignedVolume_tendsto {L c T : ℝ} (hL : 0 < L) (hc : 0 < c)
    (K : ℕ → ℕ) (b : (n : ℕ) → Fin 3 → Fin (Nat.fib (n + 2)))
    (hT : Tendsto (fun n => (K n : ℝ) * sourceDelta (n + 2) L c) atTop (𝓝 T))
    (hbuffer : ∀ᶠ n in atTop, coordinateBall (WithLp.ofLp (site L (b n)))
      ((K n : ℝ) * radius (n + 2) L / 2 + assignment (n + 2) L) ⊆ cube L) :
    Tendsto (fun n => alignedVolume (n + 2) L c (K n) (b n)) atTop
      (𝓝 (Real.pi * c ^ 3 * T ^ 4 / 24)) := by
  let δ := fun n => sourceDelta (n + 2) L c
  let A := fun n => assignment (n + 2) L
  let Tn := fun n => (K n : ℝ) * δ n
  let V := fun n => alignedVolume (n + 2) L c (K n) (b n)
  let ref := fun n => Real.pi * c ^ 3 * (Tn n) ^ 4 / 24
  let err := fun n => 4 * Real.pi * (Tn n + δ n) * (c * Tn n / 2 + A n) ^ 2 *
      (A n + c * Tn n * (A n / radius (n + 2) L)) + Real.pi * c ^ 3 * (Tn n) ^ 3 * δ n / 2
  have hδ := sourceDelta_tendsto L c
  have hA := assignment_tendsto L
  have hratio := assignment_ratio_tendsto hL
  have herr : Tendsto err atTop (𝓝 0) := by
    have h := (((hT.add hδ).const_mul (4 * Real.pi)).mul
      ((((hT.const_mul c).div_const 2).add hA).pow 2)).mul
        (hA.add ((hT.const_mul c).mul hratio))
    have ht := ((((hT.pow 3).const_mul (Real.pi * c ^ 3)).mul hδ).div_const 2)
    simpa only [err, Tn, δ, A, mul_zero, zero_div, add_zero, mul_assoc] using h.add ht
  have hdiff : Tendsto (fun n => V n - ref n) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg (V n - ref n))) _ herr
    filter_upwards [eventually_inner_radius hL, hbuffer] with n hn hb
    have hh := golden_weighted_error (by omega : 0 < n + 2) hL hc hn (K n) (b n) hb
    simpa only [V, ref, err, Tn, δ, A, mul_div_assoc] using hh
  have href : Tendsto ref atTop (𝓝 (Real.pi * c ^ 3 * T ^ 4 / 24)) :=
    ((hT.pow 4).const_mul (Real.pi * c ^ 3)).div_const 24
  simpa only [sub_add_cancel, zero_add] using hdiff.add href

theorem alignedCount_tendsto {L c T : ℝ} (hL : 0 < L) (hc : 0 < c)
    (K : ℕ → ℕ) (b : (n : ℕ) → Fin 3 → Fin (Nat.fib (n + 2)))
    (hT : Tendsto (fun n => (K n : ℝ) * sourceDelta (n + 2) L c) atTop (𝓝 T))
    (hbuffer : ∀ᶠ n in atTop, coordinateBall (WithLp.ofLp (site L (b n)))
      ((K n : ℝ) * radius (n + 2) L / 2 + assignment (n + 2) L) ⊆ cube L) :
    Tendsto (fun n => sourceDelta (n + 2) L c * (L ^ 3 / (Nat.fib (n + 2) : ℝ) ^ 3) *
      (alignedCount (n + 2) L (K n) (b n) : ℝ)) atTop (𝓝 (Real.pi * c ^ 3 * T ^ 4 / 24)) := by
  have hh := alignedVolume_tendsto hL hc K b hT hbuffer
  convert hh using 1
  ext n
  exact (alignedVolume_eq_count (by omega : 0 < n + 2) hL c (K n) (b n)).symm

#print axioms golden_weighted_error
#print axioms alignedVolume_eq_count
#print axioms alignedCount_tendsto

end
end OPH.GoldenSourceVolumeLimit

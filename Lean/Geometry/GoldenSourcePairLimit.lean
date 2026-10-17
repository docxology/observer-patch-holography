module
public import Geometry.GoldenSourceCausalLimit

@[expose] public section

set_option autoImplicit false

/-!
# Actual strict-pair counting limit of the supplied golden source family

Both interval membership and pair precedence use the generated read order.
Product cell masses are derived, inclusive endpoint errors are bounded, and
the pairwise null relation is proved null. The limiting quantity is the
geometric double-indicator measure in the declared window. Its numerical
evaluation is a separate geometric theorem, not an input hidden here.
-/

namespace OPH.GoldenSourcePairLimit

open MeasureTheory Set Filter
open OPH.GoldenSourceAssignment OPH.GoldenSourceCountLimit
open OPH.SourceNetCausalCone OPH.SourceCausalBoundary
open OPH.SourceCountTransport OPH.GoldenSourceCausalLimit
open scoped Topology BigOperators Classical

noncomputable section

/-- The actual strict part of the generated partial order, not a causal
comparison applied directly to sampled coordinates. -/
theorem strictlyGenerated_iff {n : ℕ} {T L c : ℝ} (hn : 0 < n) (hL : 0 < L)
    (i j : Label n T L c) : strictlyGenerated i j ↔ generated i j ∧ i ≠ j := by
  constructor
  · intro h
    exact ⟨h.2, fun hij => (Nat.ne_of_lt h.1) (congrArg (fun k => k.1.val) hij)⟩
  · rintro ⟨hg, hne⟩
    refine ⟨lt_of_le_of_ne hg.1 ?_, hg⟩
    intro ht
    apply hne
    apply Prod.ext (Fin.ext ht)
    apply site_injective hL
    have hsame : Precedes (radius n L) (i.1.val, (placed i).2)
        (i.1.val, (placed j).2) := by
      change Precedes (radius n L) (i.1.val, (placed i).2) (j.1.val, (placed j).2) at hg
      simpa only [ht] using hg
    exact congrArg Subtype.val ((same_layer_precedes_iff (radius_pos hn hL).le
      i.1.val (placed i).2 (placed j).2).mp hsame)

def pairMember {n : ℕ} {T L c : ℝ} (e f : Label n T L c)
    (ij : Label n T L c × Label n T L c) : Prop :=
  intervalMember e f ij.1 ∧ intervalMember e f ij.2 ∧ strictlyGenerated ij.1 ij.2

def strictPairCount {n : ℕ} {T L c : ℝ} (e f : Label n T L c) : ℕ :=
  count (pairMember e f)

/-- Geometric timelike pairs inside the same clipped limiting interval.
Null pairs and the coincidence diagonal have zero product measure. -/
def pairRegion (c : ℝ) (p q : Spacetime) : Set (Spacetime × Spacetime) :=
  {z | z.1 ∈ diamond c p q ∧ z.2 ∈ diamond c p q ∧ 0 < margin c z.1 z.2}

theorem pairRegion_measurable (c : ℝ) (p q : Spacetime) :
    MeasurableSet (pairRegion c p q) :=
  ((diamond_measurable c p q).preimage measurable_fst).inter
    (((diamond_measurable c p q).preimage measurable_snd).inter
      (isOpen_lt continuous_const (continuous_margin c)).measurableSet)

theorem strict_classification_ae {T L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    ∀ᵐ z ∂(spaceTimeVolume T L).prod (spaceTimeVolume T L), ∀ᶠ n in atTop,
      ∀ ij : Label (n + 2) T L c × Label (n + 2) T L c,
        z ∈ pairCell (n + 2) T L (sourceDelta (n + 2) L c) ij →
          (strictlyGenerated ij.1 ij.2 ↔ 0 < margin c z.1 z.2) := by
  let : IsFiniteMeasure (spaceTimeVolume T L) := spaceTimeVolume_finite T L
  have hcov (n : ℕ) : ∀ᵐ x ∂spaceTimeVolume T L, ∃ i,
      x ∈ eventCell (n + 2) T L (sourceDelta (n + 2) L c) i :=
    eventCell_ae_cover (by omega : 0 < n + 2) hL (sourceDelta_pos (by omega) hL hc)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr hcov),
    Measure.quasiMeasurePreserving_snd.ae (ae_all_iff.mpr hcov),
    compl_mem_ae_iff.mpr (pair_null T L hc.ne')] with z hx hy hn
  let b : (n : ℕ) → Label (n + 2) T L c := fun n => Classical.choose (hx n)
  let d : (n : ℕ) → Label (n + 2) T L c := fun n => Classical.choose (hy n)
  have hb (n : ℕ) : z.1 ∈ eventCell (n + 2) T L (sourceDelta (n + 2) L c) (b n) :=
    Classical.choose_spec (hx n)
  have hd (n : ℕ) : z.2 ∈ eventCell (n + 2) T L (sourceDelta (n + 2) L c) (d n) :=
    Classical.choose_spec (hy n)
  have hb0 := assigned_position_tendsto hL hc b hb
  have hd0 := assigned_position_tendsto hL hc d hd
  filter_upwards [generated_eventually_iff hL hc b d hb0 hd0 hn] with n hbd
  intro ij hij
  have hi : ij.1 = b n := by
    by_contra hne
    exact disjoint_left.mp (eventCell_disjoint (by omega : 0 < n + 2) hL
      (sourceDelta_pos (by omega) hL hc) hne) hij.1 (hb n)
  have hj : ij.2 = d n := by
    by_contra hne
    exact disjoint_left.mp (eventCell_disjoint (by omega : 0 < n + 2) hL
      (sourceDelta_pos (by omega) hL hc) hne) hij.2 (hd n)
  rw [hi, hj, hbd.2]
  have hn' : margin c z.1 z.2 ≠ 0 := hn
  exact ⟨fun h => lt_of_le_of_ne h hn'.symm, le_of_lt⟩

theorem pair_classification_ae {T L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (e f : (n : ℕ) → Label (n + 2) T L c) {p q : Spacetime}
    (he : Tendsto (fun n => position (e n)) atTop (𝓝 p))
    (hf : Tendsto (fun n => position (f n)) atTop (𝓝 q)) :
    ∀ᵐ z ∂(spaceTimeVolume T L).prod (spaceTimeVolume T L), ∀ᶠ n in atTop,
      ∀ ij, z ∈ pairCell (n + 2) T L (sourceDelta (n + 2) L c) ij →
        (pairMember (e n) (f n) ij ↔ z ∈ pairRegion c p q) := by
  let : IsFiniteMeasure (spaceTimeVolume T L) := spaceTimeVolume_finite T L
  have hi := interval_classification_ae hL hc e f he hf
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hi,
    Measure.quasiMeasurePreserving_snd.ae hi, strict_classification_ae (T := T) hL hc]
    with z hz₁ hz₂ hz₃
  filter_upwards [hz₁, hz₂, hz₃] with n hn₁ hn₂ hn₃
  intro ij hij
  exact (hn₁ ij.1 hij.1).and ((hn₂ ij.2 hij.2).and (hn₃ ij hij))

/-- Counts of actual strict generated pairs converge to the geometric product
volume. No ordering-fraction, weak-measure or pair-count limit is assumed. -/
theorem generated_strict_pair_count_tendsto {T L c : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hc : 0 < c) (e f : (n : ℕ) → Label (n + 2) T L c) {p q : Spacetime}
    (he : Tendsto (fun n => position (e n)) atTop (𝓝 p))
    (hf : Tendsto (fun n => position (f n)) atTop (𝓝 q)) :
    Tendsto (fun n =>
      (sourceDelta (n + 2) L c * (L ^ 3 / (Nat.fib (n + 2) : ℝ) ^ 3)) ^ 2 *
        (strictPairCount (e n) (f n) : ℝ)) atTop
      (𝓝 (((spaceTimeVolume T L).prod (spaceTimeVolume T L)).real (pairRegion c p q))) :=
  pair_selected_count_tendsto hT hL _ (fun n => sourceDelta_pos (by omega) hL hc)
    (sourceDelta_tendsto L c) (fun n => pairMember (e n) (f n)) _
    (pairRegion_measurable c p q) (pair_classification_ae hL hc e f he hf)

def eventWeight (n : ℕ) (L c : ℝ) : ℝ :=
  sourceDelta n L c * (L ^ 3 / (Nat.fib n : ℝ) ^ 3)

theorem eventWeight_pos {n : ℕ} (hn : 0 < n) {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    0 < eventWeight n L c := by
  unfold eventWeight
  apply mul_pos (sourceDelta_pos hn hL hc)
  exact div_pos (pow_pos hL 3) (pow_pos (by exact_mod_cast Nat.fib_pos.mpr hn) 3)

theorem eventWeight_tendsto (L c : ℝ) :
    Tendsto (fun n => eventWeight (n + 2) L c) atTop (𝓝 0) := by
  have hfib : Tendsto (fun n => (Nat.fib (n + 2) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.fib_add_two_strictMono.tendsto_atTop
  have hv := (hfib.const_div_atTop L).pow 3
  simpa only [eventWeight, div_pow, zero_pow (by norm_num : 3 ≠ 0), mul_zero] using
    (sourceDelta_tendsto L c).mul hv

theorem scaled_fraction (w N C : ℝ) (hw : w ≠ 0) :
    2 * (w ^ 2 * C) / ((w * N) * (w * N - w)) = 2 * C / (N * (N - 1)) := by
  calc
    _ = (w ^ 2 * (2 * C)) / (w ^ 2 * (N * (N - 1))) := by congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (pow_ne_zero 2 hw)

/-- The finite N(N-1) normalization converges without assuming N grows or
discarding diagonal terms. The difference from the square is the vanishing
event weight. Evaluation of this geometric quotient is separate. -/
theorem ordering_fraction_tendsto_geometric {T L c : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hc : 0 < c) (e f : (n : ℕ) → Label (n + 2) T L c) {p q : Spacetime}
    (he : Tendsto (fun n => position (e n)) atTop (𝓝 p))
    (hf : Tendsto (fun n => position (f n)) atTop (𝓝 q))
    (hV : (spaceTimeVolume T L).real (diamond c p q) ≠ 0) :
    Tendsto (fun n => 2 * (strictPairCount (e n) (f n) : ℝ) /
      ((intervalCount (e n) (f n) : ℝ) * ((intervalCount (e n) (f n) : ℝ) - 1)))
      atTop (𝓝 (2 * (((spaceTimeVolume T L).prod (spaceTimeVolume T L)).real
        (pairRegion c p q)) / ((spaceTimeVolume T L).real (diamond c p q)) ^ 2)) := by
  have hN := generated_interval_count_tendsto hT hL hc e f he hf
  have hC := generated_strict_pair_count_tendsto hT hL hc e f he hf
  have hw := eventWeight_tendsto L c
  have hden := hN.mul (hN.sub hw)
  have hlim := (hC.const_mul 2).div hden (by simpa only [sub_zero] using mul_ne_zero hV hV)
  have heq (n : ℕ) := scaled_fraction (eventWeight (n + 2) L c)
    (intervalCount (e n) (f n) : ℝ) (strictPairCount (e n) (f n) : ℝ)
    (eventWeight_pos (by omega) hL hc).ne'
  simp only [sub_zero, ← pow_two] at hlim
  convert hlim using 1
  ext n
  exact (heq n).symm

#print axioms strictlyGenerated_iff
#print axioms generated_strict_pair_count_tendsto
#print axioms ordering_fraction_tendsto_geometric

end
end OPH.GoldenSourcePairLimit

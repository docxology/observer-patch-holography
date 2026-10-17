module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Source-population cell transport and quadrature

The cell measures, representatives and displacement estimates are inputs.
The conclusions compare actual Bochner integrals with weighted samples;
neither an integral error nor a desired continuum limit is assumed.
These estimates apply to golden source-record cells and metric partitions
after their geometric and measure hypotheses have been established.
-/

namespace OPH.SourcePopulationQuadrature

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

variable {X E : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A locally supplied modulus integrates against the actual displacement. -/
theorem cell_local_first_moment (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (s : X) (K : ℝ) (hf : Integrable f μ)
    (hd : Integrable (fun x => dist s x) μ)
    (hcell : ∀ᵐ x ∂μ, ‖f s - f x‖ ≤ K * dist s x) :
    ‖μ.real univ • f s - ∫ x, f x ∂μ‖ ≤ K * ∫ x, dist s x ∂μ := by
  rw [← integral_const, ← integral_sub (integrable_const (f s)) hf]
  exact (norm_integral_le_of_norm_le (hd.const_mul K) hcell).trans_eq
    (integral_const_mul K _)

/-- A cell's error is controlled by its actual first displacement moment. -/
theorem cell_transport_error (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (s : X) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hf : Integrable f μ) (hd : Integrable (fun x => dist s x) μ) :
    ‖μ.real univ • f s - ∫ x, f x ∂μ‖ ≤
      (K : ℝ) * ∫ x, dist s x ∂μ := by
  rw [← integral_const, ← integral_sub (integrable_const (f s)) hf]
  calc
    ‖∫ x, f s - f x ∂μ‖ ≤ ∫ x, (K : ℝ) * dist s x ∂μ :=
      norm_integral_le_of_norm_le (hd.const_mul _) <|
        Filter.Eventually.of_forall fun x => by
          simpa only [dist_eq_norm] using hK.dist_le_mul s x
    _ = _ := integral_const_mul _ _

/-- The maximum displacement version needs no integrability assumption on
the distance function. Local Lipschitz bounds suffice on each cell. -/
theorem cell_uniform_error (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (s : X) (K H : ℝ) (hK : 0 ≤ K)
    (hf : Integrable f μ)
    (hfcell : ∀ᵐ x ∂μ, ‖f s - f x‖ ≤ K * dist s x)
    (hcell : ∀ᵐ x ∂μ, dist s x ≤ H) :
    ‖μ.real univ • f s - ∫ x, f x ∂μ‖ ≤
      μ.real univ * K * H := by
  rw [← integral_const, ← integral_sub (integrable_const (f s)) hf]
  have h : ∀ᵐ x ∂μ, ‖f s - f x‖ ≤ K * H := by
    filter_upwards [hfcell, hcell] with x hfx hx
    exact hfx.trans (mul_le_mul_of_nonneg_left hx hK)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    norm_integral_le_of_norm_le_const h

/-- Summing actual cell integrals produces the integral of the sum measure.
Cells may have different masses and local displacement/Lipschitz bounds. -/
theorem finite_cell_quadrature {ι : Type*} [Fintype ι]
    (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (f : X → E) (s : ι → X) (K H : ι → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hf : ∀ i, Integrable f (μ i))
    (hfcell : ∀ i, ∀ᵐ x ∂μ i, ‖f (s i) - f x‖ ≤ K i * dist (s i) x)
    (hcell : ∀ i, ∀ᵐ x ∂μ i, dist (s i) x ≤ H i) :
    ‖(∑ i, (μ i).real univ • f (s i)) - ∫ x, f x ∂(∑ i, μ i)‖ ≤
      ∑ i, (μ i).real univ * K i * H i := by
  rw [integral_finsetSum_measure (fun i _ => hf i), ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ =>
    cell_uniform_error (μ i) f (s i) (K i) (H i) (hK i) (hf i)
      (hfcell i) (hcell i)

/-- Integrated displacement can sharpen a coarse maximum-fill estimate. -/
theorem finite_cell_first_moment {ι : Type*} [Fintype ι]
    (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (f : X → E) (s : ι → X) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hf : ∀ i, Integrable f (μ i))
    (hd : ∀ i, Integrable (fun x => dist (s i) x) (μ i)) :
    ‖(∑ i, (μ i).real univ • f (s i)) - ∫ x, f x ∂(∑ i, μ i)‖ ≤
      (K : ℝ) * ∑ i, ∫ x, dist (s i) x ∂μ i := by
  rw [integral_finsetSum_measure (fun i _ => hf i), ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ =>
    cell_transport_error (μ i) f (s i) hK (hf i) (hd i)

/-- Cell-specific Lipschitz constants retain local first-moment information. -/
theorem finite_cell_local_first_moment {ι : Type*} [Fintype ι]
    (μ : ι → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (f : X → E) (s : ι → X) (K : ι → ℝ)
    (hf : ∀ i, Integrable f (μ i))
    (hd : ∀ i, Integrable (fun x => dist (s i) x) (μ i))
    (hcell : ∀ i, ∀ᵐ x ∂μ i, ‖f (s i) - f x‖ ≤ K i * dist (s i) x) :
    ‖(∑ i, (μ i).real univ • f (s i)) - ∫ x, f x ∂(∑ i, μ i)‖ ≤
      ∑ i, K i * ∫ x, dist (s i) x ∂μ i := by
  rw [integral_finsetSum_measure (fun i _ => hf i), ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ =>
    cell_local_first_moment (μ i) f (s i) (K i) (hf i) (hd i) (hcell i)

/-- Measurable partition hypotheses derive the common measure, rather than
assuming agreement of the quadrature and continuum integrals. A bounded
window can serve as `X`, with its restricted volume measure. -/
theorem partition_quadrature {ι : Type*} [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (C : ι → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : ⋃ i, C i = univ) (s : ι → X) (f : X → E)
    {K : ℝ≥0} (hK : LipschitzWith K f) (H : ι → ℝ)
    (hf : ∀ i, Integrable f (μ.restrict (C i)))
    (hcell : ∀ i, ∀ᵐ x ∂μ.restrict (C i), dist (s i) x ≤ H i) :
    ‖(∑ i, μ.real (C i) • f (s i)) - ∫ x, f x ∂μ‖ ≤
      ∑ i, μ.real (C i) * (K : ℝ) * H i := by
  have hsum : (∑ i, μ.restrict (C i)) = μ := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hdis hC,
      hcover, Measure.restrict_univ]
  have hlocal (i : ι) : ∀ᵐ x ∂μ.restrict (C i),
      ‖f (s i) - f x‖ ≤ (K : ℝ) * dist (s i) x :=
    Filter.Eventually.of_forall fun x => by
      simpa only [dist_eq_norm] using hK.dist_le_mul (s i) x
  simpa only [measureReal_restrict_apply_univ, hsum] using
    finite_cell_quadrature (fun i => μ.restrict (C i)) f s
      (fun _ => (K : ℝ)) H (fun _ => K.coe_nonneg) hf hlocal hcell

/-- A uniform assignment bound gives the usual volume times Lipschitz error. -/
theorem partition_uniform_quadrature {ι : Type*} [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (C : ι → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (hdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : ⋃ i, C i = univ) (s : ι → X) (f : X → E)
    {K : ℝ≥0} (hK : LipschitzWith K f) (H : ℝ)
    (hf : ∀ i, Integrable f (μ.restrict (C i)))
    (hcell : ∀ i, ∀ᵐ x ∂μ.restrict (C i), dist (s i) x ≤ H) :
    ‖(∑ i, μ.real (C i) • f (s i)) - ∫ x, f x ∂μ‖ ≤
      μ.real univ * (K : ℝ) * H := by
  have hmass : (∑ i, μ.real (C i)) = μ.real univ := by
    rw [← measureReal_iUnion_fintype hdis hC, hcover]
  simpa only [← Finset.sum_mul, hmass] using
    partition_quadrature μ C hC hdis hcover s f hK (fun _ => H) hf hcell

/-- Weak quadrature convergence is derived from shrinking cell displacement.
The population size and representatives may change at every index. -/
theorem partition_quadrature_tendsto {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (μ : Measure X) [IsFiniteMeasure μ]
    (C : (n : ℕ) → ι n → Set X) (s : (n : ℕ) → ι n → X)
    (hC : ∀ n i, MeasurableSet (C n i))
    (hdis : ∀ n, Pairwise (fun i j => Disjoint (C n i) (C n j)))
    (hcover : ∀ n, ⋃ i, C n i = univ) (H : ℕ → ℝ)
    (hH : Filter.Tendsto H Filter.atTop (nhds 0))
    (f : X → E) {K : ℝ≥0} (hK : LipschitzWith K f)
    (hf : ∀ n i, Integrable f (μ.restrict (C n i)))
    (hcell : ∀ n i, ∀ᵐ x ∂μ.restrict (C n i), dist (s n i) x ≤ H n) :
    Filter.Tendsto (fun n => ∑ i, μ.real (C n i) • f (s n i))
      Filter.atTop (nhds (∫ x, f x ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    partition_uniform_quadrature μ (C n) (hC n) (hdis n) (hcover n)
      (s n) f hK (H n) (hf n) (hcell n))
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul hH : Filter.Tendsto
      (fun n => (μ.real univ * (K : ℝ)) * H n) Filter.atTop
        (nhds ((μ.real univ * (K : ℝ)) * 0)))

omit [PseudoMetricSpace X] in
/-- Incorrect total weights are visible even to the constant detector. -/
theorem constant_detects_mass_error {ι : Type*} [Fintype ι]
    (μ : Measure X) (v : ι → ℝ) :
    |(∑ i, v i * (1 : ℝ)) - ∫ _ : X, (1 : ℝ) ∂μ| =
      |(∑ i, v i) - μ.real univ| := by
  simp [integral_const]

section Tent

omit [MeasurableSpace X]

/-- The radial compact-support kernel weight used by the scalar action. -/
noncomputable def tent (ε : ℝ) (x y : X) : ℝ :=
  max (1 - dist x y / ε) 0

theorem tent_nonnegative (ε : ℝ) (x y : X) : 0 ≤ tent ε x y :=
  le_max_right _ _

theorem tent_le_one {ε : ℝ} (hε : 0 < ε) (x y : X) : tent ε x y ≤ 1 := by
  apply max_le
  · linarith [div_nonneg (dist_nonneg (x := x) (y := y)) hε.le]
  · norm_num

theorem tent_eq_zero {ε : ℝ} (hε : 0 < ε) {x y : X}
    (h : ε ≤ dist x y) : tent ε x y = 0 := by
  apply max_eq_right
  have : 1 ≤ dist x y / ε := (le_div_iff₀ hε).mpr (by simpa using h)
  linarith

theorem tent_difference {ε : ℝ} (hε : 0 < ε) (x y z : X) :
    |tent ε x y - tent ε x z| ≤ dist y z / ε := by
  calc
    |tent ε x y - tent ε x z| ≤
        |(1 - dist x y / ε) - (1 - dist x z / ε)| :=
      abs_max_sub_max_le_abs _ _ _
    _ = |dist y x - dist z x| / ε := by
      rw [dist_comm x y, dist_comm x z]
      rw [show (1 - dist y x / ε) - (1 - dist z x / ε) =
          -(dist y x - dist z x) / ε by ring, abs_div, abs_neg,
        abs_of_pos hε]
    _ ≤ _ := div_le_div_of_nonneg_right (abs_dist_sub_le y z x) hε.le

/-- The field difference removes the apparent inverse-radius growth of the
tent integrand's Lipschitz constant. No global bound on `f` is required. -/
theorem tent_field_difference {ε : ℝ} (hε : 0 < ε) (x y z : X)
    (f : X → ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    |tent ε x y * (f x - f y) - tent ε x z * (f x - f z)| ≤
      (K : ℝ) * dist y z := by
  have ordered (y z : X) (hw : tent ε x y ≤ tent ε x z) :
      |tent ε x y * (f x - f y) - tent ε x z * (f x - f z)| ≤
        (K : ℝ) * dist y z := by
    by_cases hz : tent ε x z = 0
    · have hy : tent ε x y = 0 := le_antisymm (hw.trans_eq hz) (tent_nonnegative _ _ _)
      simp only [hy, hz, zero_mul, sub_self, abs_zero]
      positivity
    have hzpos : 0 < tent ε x z := lt_of_le_of_ne (tent_nonnegative _ _ _) (Ne.symm hz)
    have hzdist : dist x z ≤ ε := by
      by_contra h
      exact hz (tent_eq_zero hε (le_of_lt (lt_of_not_ge h)))
    have hfield : |f x - f z| ≤ (K : ℝ) * dist x z := hK.dist_le_mul x z
    have hbudget : tent ε x y + dist x z / ε ≤ 1 := by
      have hzform : tent ε x z = 1 - dist x z / ε := by
        apply max_eq_left
        have : dist x z / ε ≤ 1 := (div_le_one hε).mpr hzdist
        linarith
      rw [hzform] at hw
      linarith
    have hpair : |f z - f y| ≤ (K : ℝ) * dist y z := by
      simpa only [Real.dist_eq, dist_comm z y] using hK.dist_le_mul z y
    have hweight := tent_difference hε x y z
    calc
      _ = |tent ε x y * (f z - f y) +
          (tent ε x y - tent ε x z) * (f x - f z)| := by congr 1; ring
      _ ≤ |tent ε x y * (f z - f y)| +
          |(tent ε x y - tent ε x z) * (f x - f z)| := abs_add_le _ _
      _ = tent ε x y * |f z - f y| +
          |tent ε x y - tent ε x z| * |f x - f z| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (tent_nonnegative _ _ _)]
      _ ≤ tent ε x y * ((K : ℝ) * dist y z) +
          (dist y z / ε) * ((K : ℝ) * dist x z) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hpair (tent_nonnegative _ _ _))
          (mul_le_mul hweight hfield (abs_nonneg _) (by positivity))
      _ = ((K : ℝ) * dist y z) * (tent ε x y + dist x z / ε) := by ring
      _ ≤ ((K : ℝ) * dist y z) * 1 :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := mul_one _
  rcases le_total (tent ε x y) (tent ε x z) with h | h
  · exact ordered y z h
  · simpa only [abs_sub_comm, dist_comm z y] using ordered z y h

/-- The rooted tent integrand has the original field's Lipschitz constant. -/
theorem tent_field_lipschitz {ε : ℝ} (hε : 0 < ε) (x : X)
    (f : X → ℝ) {K : ℝ≥0} (hK : LipschitzWith K f) :
    LipschitzWith K (fun y => tent ε x y * (f x - f y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  exact tent_field_difference hε x y z f hK

end Tent

/-- The endpoint/assignment condition cannot be inferred from a sample weight. -/
theorem misplaced_sample_counterexample :
    ‖(Measure.dirac (1 : ℝ)).real univ • (0 : ℝ) -
        ∫ x : ℝ, x ∂Measure.dirac (1 : ℝ)‖ = 1 := by
  simp

#print axioms cell_local_first_moment
#print axioms finite_cell_local_first_moment
#print axioms partition_quadrature
#print axioms partition_quadrature_tendsto
#print axioms tent_field_difference
#print axioms tent_field_lipschitz
#print axioms misplaced_sample_counterexample

end OPH.SourcePopulationQuadrature

module
public import Geometry.SourceConstrainedSelection

@[expose] public section

/-!
# Finite A3 state-selection inequalities

Real reductions of the noncommutative compatible-family argument in
`code/source_publication_selection/STATE_SELECTION.md`. The matrix
mixture-gap estimate follows analytically from Umegaki data processing;
this module does not formalize that matrix theorem or introduce it as an
axiom. All functional inequalities below are explicit theorem hypotheses.
-/

set_option autoImplicit false

namespace OPH.SourceStateSelection
noncomputable section

/-- A positive logarithmic mixture coefficient prevents a boundary minimum. -/
theorem not_minimum_of_log_gap (value : ℝ → ℝ) (base cost coefficient : ℝ)
    (ha : 0 < coefficient)
    (hgap : ∀ t, 0 < t → t < 1 →
      value t ≤ base + t * cost + t * coefficient * Real.log t) :
    ∃ t, 0 < t ∧ t < 1 ∧ value t < base := by
  obtain ⟨t, ht, ht1, hlog⟩ :=
    SourceConstrainedSelection.exists_small_log (-cost / coefficient)
  have hslope := (lt_div_iff₀ ha).mp hlog
  have hstrict := mul_lt_mul_of_pos_left hslope ht
  exact ⟨t, ht, ht1, lt_of_le_of_lt (hgap t ht ht1) (by nlinarith)⟩

/-- Summing local convexity gaps retains a strictly scored boundary gap. -/
theorem weighted_gap {P : Type*} [Fintype P] [DecidableEq P]
    (weight before after mixed : P → ℝ) (i : P) (t gap : ℝ)
    (hw : ∀ j, 0 ≤ weight j)
    (hlocal : ∀ j, mixed j ≤ (1-t)*before j + t*after j -
      if j=i then gap else 0) :
    (∑ j, weight j * mixed j) ≤
      (1-t)*(∑ j, weight j*before j) + t*(∑ j, weight j*after j) -
        weight i * gap := by
  calc
    (∑ j, weight j * mixed j) ≤
        ∑ j, weight j * ((1-t)*before j + t*after j -
          if j=i then gap else 0) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlocal j) (hw j)
    _ = _ := by
      simp_rw [mul_sub, mul_add]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp_rw [← mul_assoc, mul_comm (weight _) (1-t), mul_comm (weight _) t,
        mul_assoc]
      simp [Finset.mul_sum]

/-- A quantitative boundary improvement, with its actual admissible mixture. -/
theorem explicit_improvement (value : ℝ → ℝ) (base cost coefficient : ℝ)
    (ha : 0 < coefficient) (hc : 0 ≤ cost)
    (hgap : ∀ t, 0 < t → t < 1 →
      value t ≤ base + t*cost + t*coefficient*Real.log t) :
    let t := Real.exp (-1-cost/coefficient)
    0 < t ∧ t < 1 ∧ value t ≤ base - coefficient*t := by
  dsimp
  have ht := Real.exp_pos (-1-cost/coefficient)
  have ht1 : Real.exp (-1-cost/coefficient) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have := div_nonneg hc ha.le
    linarith
  refine ⟨ht, ht1, ?_⟩
  calc
    value (Real.exp (-1-cost/coefficient)) ≤
        base + Real.exp (-1-cost/coefficient)*cost +
          Real.exp (-1-cost/coefficient)*coefficient*
            Real.log (Real.exp (-1-cost/coefficient)) := hgap _ ht ht1
    _ = base - coefficient*Real.exp (-1-cost/coefficient) := by
      rw [Real.log_exp]
      field_simp
      ring

/-- An error tolerance below a certified improvement excludes approximate optimality. -/
theorem not_approximate_minimum (candidate competitor epsilon improvement : ℝ)
    (hbetter : competitor ≤ candidate-improvement) (he : epsilon < improvement) :
    ¬ candidate ≤ competitor+epsilon := by linarith

/-- The binary divergence bound gives a strictly positive failure floor. -/
theorem probability_floor (p b entropy cost weight : ℝ)
    (hp : 0 < p) (hb : 0 < b) (hw : 0 < weight)
    (hbound : weight * (-entropy-b*Real.log p) ≤ cost) :
    Real.exp (-(cost/weight+entropy)/b) ≤ p := by
  have hdiv : -entropy-b*Real.log p ≤ cost/weight :=
    (le_div_iff₀ hw).mpr (by nlinarith [hbound])
  have hlog : -(cost/weight+entropy)/b ≤ Real.log p := by
    apply (div_le_iff₀ hb).mpr
    nlinarith
  calc
    Real.exp (-(cost/weight+entropy)/b) ≤ Real.exp (Real.log p) :=
      Real.exp_le_exp.mpr hlog
    _ = p := Real.exp_log hp

/-- Replacing the unknown optimum by a certified lower bound weakens the floor safely. -/
theorem probability_floor_of_cost_upper (p b entropy delta cost weight : ℝ)
    (hp : 0 < p) (hb : 0 < b) (hw : 0 < weight) (hd : delta ≤ cost)
    (hbound : weight * (-entropy-b*Real.log p) ≤ delta) :
    Real.exp (-(cost/weight+entropy)/b) ≤ p :=
  probability_floor p b entropy cost weight hp hb hw (hbound.trans hd)

/-- Support saturation, stated for any positive scored observable, gives an exact
feasibility criterion. Its premise concerns the whole feasible family. -/
theorem zero_iff_feasible_zero {S : Type*} (K : Set S) (selected : S)
    (readout : S → ℝ) (hselected : selected ∈ K)
    (hnonneg : ∀ s ∈ K, 0 ≤ readout s)
    (hsupport : ∀ s ∈ K, 0 < readout s → 0 < readout selected) :
    readout selected = 0 ↔ ∀ s ∈ K, readout s = 0 := by
  constructor
  · intro hz s hs
    by_contra hn
    have hpos := hsupport s hs (lt_of_le_of_ne (hnonneg s hs) (Ne.symm hn))
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  · intro h
    exact h selected hselected

/-- Positive domination transfers a zero expectation. Matrix support inclusion
supplies such domination at finite dimension; that matrix step is analytic. -/
theorem zero_of_positive_domination (selected feasible coefficient : ℝ)
    (hfeasible : 0 ≤ feasible) (hdom : feasible ≤ coefficient*selected)
    (hz : selected=0) : feasible=0 := by
  rw [hz, mul_zero] at hdom
  exact le_antisymm hdom hfeasible

/-- The two-time mismatch test distinguishes the identity and depolarizing
binary record laws despite their identical single-time marginals. -/
theorem binary_process_marginals :
    (1/2:ℚ)+0 = 1/4+1/4 ∧
    (0:ℚ)+1/2 = 1/4+1/4 ∧
    (0:ℚ)+0 ≠ 1/4+1/4 := by norm_num

end
end OPH.SourceStateSelection

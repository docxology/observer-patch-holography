module
public import ActionTimeGram

@[expose] public section

/-!
# Positive duration uniqueness for the variable-step action equation

This file proves the linear-algebraic implication used by
the source-scalar clock paper theorem. Two independent record vectors and the supplied
configuration Euler equation force both adjacent positive durations to be
`sqrt s`. The candidate durations are not assumed equal.

The analytic derivation of that Euler equation from trapezoidal quadrature,
the actual finite record certificate and the numerical
Gram values remain separate. The imported Gram bridge is composed below. No source-selection, physical unit, time orientation,
regional time-slice, or lapse-variation theorem is asserted here.
-/

namespace OPH.SourceActionTime

/-- Coefficients from the two independent directions force equal positive steps. -/
theorem positive_durations_from_coefficients
    {hprev hnext s : ℝ}
    (hp : 0 < hprev) (hn : 0 < hnext)
    (hfirst : 1 / hnext - 1 / hprev = 0)
    (hsecond : -s / hnext + (hnext + hprev) / 2 = 0) :
    hprev = Real.sqrt s ∧ hnext = Real.sqrt s := by
  have heq : hnext = hprev := by
    have hinv : hnext⁻¹ = hprev⁻¹ := by
      simpa only [one_div] using sub_eq_zero.mp hfirst
    exact inv_inj.mp hinv
  have hdiv : s / hnext = (hnext + hprev) / 2 := by
    rw [neg_div] at hsecond
    linarith
  have hprod : s = ((hnext + hprev) / 2) * hnext :=
    (div_eq_iff (ne_of_gt hn)).mp hdiv
  have hsq : hprev ^ 2 = s := by rw [heq] at hprod; nlinarith
  have hsqrt : Real.sqrt s = hprev := by
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_pos hp]
  exact ⟨hsqrt.symm, heq.trans hsqrt.symm⟩

/-- Actual record and configuration-stationarity equations, with independent
record increment and force, give the two scalar coefficient equations. -/
theorem record_stationarity_coefficients
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {previousIncrement force nextIncrement : V} {hprev hnext s : ℝ}
    (hind : LinearIndependent ℝ ![previousIncrement, force])
    (hrecord : nextIncrement = previousIncrement - s • force)
    (hEL : (1 / hnext) • nextIncrement - (1 / hprev) • previousIncrement +
      ((hnext + hprev) / 2) • force = 0) :
    1 / hnext - 1 / hprev = 0 ∧
      -s / hnext + (hnext + hprev) / 2 = 0 := by
  have hcomb :
      (1 / hnext - 1 / hprev) • previousIncrement +
        (-s / hnext + (hnext + hprev) / 2) • force = 0 := by
    calc
      _ = (1 / hnext) • nextIncrement - (1 / hprev) • previousIncrement +
          ((hnext + hprev) / 2) • force := by
            rw [hrecord]
            module
      _ = 0 := hEL
  exact (LinearIndependent.pair_iff.mp hind) _ _ hcomb

/-- Uniformity is a conclusion for any candidate positive adjacent durations
obeying this variable-step configuration equation on the given record triple. -/
theorem unique_positive_record_durations
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {previousIncrement force nextIncrement : V} {hprev hnext s : ℝ}
    (hind : LinearIndependent ℝ ![previousIncrement, force])
    (hrecord : nextIncrement = previousIncrement - s • force)
    (hp : 0 < hprev) (hn : 0 < hnext)
    (hEL : (1 / hnext) • nextIncrement - (1 / hprev) • previousIncrement +
      ((hnext + hprev) / 2) • force = 0) :
    hprev = Real.sqrt s ∧ hnext = Real.sqrt s := by
  obtain ⟨hfirst, hsecond⟩ := record_stationarity_coefficients hind hrecord hEL
  exact positive_durations_from_coefficients hp hn hfirst hsecond

#print axioms positive_durations_from_coefficients
#print axioms record_stationarity_coefficients
#print axioms unique_positive_record_durations

/-- Positive Gram data and the actual record/Euler equations identify both
positive layer durations. This composes the inner-product and module results. -/
theorem unique_positive_record_durations_of_positive_gram
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y z : V} {hprev hnext s : ℝ}
    (hGram : 0 < inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2)
    (hrecord : z = x - s • y)
    (hp : 0 < hprev) (hn : 0 < hnext)
    (hEL : (1 / hnext) • z - (1 / hprev) • x +
      ((hnext + hprev) / 2) • y = 0) :
    hprev = Real.sqrt s ∧ hnext = Real.sqrt s :=
  unique_positive_record_durations
    (linearIndependent_pair_of_positive_gram hGram) hrecord hp hn hEL

/-- The scalar contraction step used after applying the two left-inverse rows. -/
theorem residual_budget_bound {b b0 q : ℝ}
    (hq : q < 1) (h : b ≤ b0 + q * b) : b ≤ b0 / (1 - q) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - q)).2
  nlinarith

#print axioms unique_positive_record_durations_of_positive_gram
#print axioms residual_budget_bound

end OPH.SourceActionTime

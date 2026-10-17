module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators

namespace OPH.WhitneySpatialConsistency

/-!
# Finite cancellation underlying the dressed scalar consistency estimate

The weighted straight-path phase of a Whitney one-form vanishes exactly
by antisymmetry. The statements below formalize this cancellation, its
polarized version, and the exact centered error decomposition. The analytic
Taylor estimates, shape-regular refinement, Sobolev hypotheses, integration,
and action/first-variation bound are proved in the associated paper, not by
these finite algebraic identities.
-/

variable {ι : Type*} [Fintype ι]

/-- The double contraction of an antisymmetric edge array is zero. -/
theorem weighted_antisymmetric_cancellation (a : ι → ι → ℝ) (lambda : ι → ℝ)
    (ha : ∀ i j, a j i = -a i j) :
    (∑ i, ∑ j, lambda i * a i j * lambda j) = 0 := by
  have h : (∑ i, ∑ j, lambda i * a i j * lambda j) =
      -(∑ i, ∑ j, lambda i * a i j * lambda j) := by
    calc
      _ = ∑ j, ∑ i, lambda i * a i j * lambda j := Finset.sum_comm
      _ = ∑ i, ∑ j, -(lambda i * a i j * lambda j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [ha i j]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

/-- Actual barycentric weighting of the Whitney path phases. -/
theorem weighted_path_phase_zero (a : ι → ι → ℝ) (lambda : ι → ℝ)
    (ha : ∀ i j, a j i = -a i j) :
    (∑ i, lambda i * (∑ j, a i j * lambda j)) = 0 := by
  simpa only [Finset.mul_sum, mul_assoc] using
    weighted_antisymmetric_cancellation a lambda ha

/-- Polarization gives the spatial derivative cancellation without assuming
that a barycentric derivative is nonnegative or has unit sum. -/
theorem polarized_cancellation (a : ι → ι → ℝ) (lambda mu : ι → ℝ)
    (ha : ∀ i j, a j i = -a i j) :
    (∑ i, ∑ j, (lambda i * a i j * mu j + mu i * a i j * lambda j)) = 0 := by
  have h := weighted_antisymmetric_cancellation a (fun i => lambda i + mu i) ha
  have hl := weighted_antisymmetric_cancellation a lambda ha
  have hm := weighted_antisymmetric_cancellation a mu ha
  have hexpand :
      (∑ i, ∑ j, (lambda i + mu i) * a i j * (lambda j + mu j)) =
      (∑ i, ∑ j, lambda i * a i j * lambda j) +
      (∑ i, ∑ j, (lambda i * a i j * mu j + mu i * a i j * lambda j)) +
      (∑ i, ∑ j, mu i * a i j * mu j) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, hl, hm] at h
  simpa using h

/-- This identity isolates a quadratic phase remainder and a product of
phase error with nodal variation. It does not assume an exponential bound. -/
theorem centered_dressing_error (lambda phase unit nodal : ι → ℂ) (value charge : ℂ)
    (hc : ∑ i, lambda i * phase i = 0) :
    (∑ i, lambda i * (unit i - 1) * nodal i) =
      value * (∑ i, lambda i * (unit i - 1 - charge * phase i)) +
      (∑ i, lambda i * (unit i - 1) * (nodal i - value)) := by
  have hzero : charge * value * (∑ i, lambda i * phase i) = 0 := by rw [hc]; ring
  rw [Finset.mul_sum] at hzero
  calc
    _ = (∑ i, lambda i * (unit i - 1) * nodal i) -
        (∑ i, charge * value * (lambda i * phase i)) := by rw [hzero]; ring
    _ = _ := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A potential variation has the same centering cancellation. -/
theorem centered_potential_variation (lambda beta weighted : ι → ℂ) (value : ℂ)
    (hc : ∑ i, lambda i * beta i = 0) :
    (∑ i, lambda i * beta i * weighted i) =
      (∑ i, lambda i * beta i * (weighted i - value)) := by
  have hzero : (∑ i, lambda i * beta i) * value = 0 := by rw [hc]; ring
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, sub_zero]

end OPH.WhitneySpatialConsistency

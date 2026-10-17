module
public import Mathlib

@[expose] public section

/-!
# Nondegenerate Gram data identify two record directions

This supplies the inner-product bridge left separate in
`SourceActionTime.lean`: a strictly positive two-by-two Gram determinant
implies its `LinearIndependent ℝ ![previousIncrement, force]` hypothesis.
The proof first establishes the stronger nonzero-determinant statement by
eliminating the coefficients of an arbitrary vanishing linear combination.

The inner product is supplied. In the finite weighted application it must
represent the positive M inner product on the actual decoded records. This
file does not establish those record values, a numerical determinant bound,
configuration stationarity, or the physical choice of an action or clock.
Neither independence nor Gram inversion ensures that a third vector lies
in the span of the first two; the full-vector record equation stays separate.
-/

namespace OPH.SourceActionTime

/-- Invertible Gram data annihilate both coefficients of a vanishing pair. -/
theorem coefficients_zero_of_gram_ne_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y : V} {a b : ℝ}
    (hGram : inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2 ≠ 0)
    (hcomb : a • x + b • y = 0) : a = 0 ∧ b = 0 := by
  have hx : a * inner ℝ x x + b * inner ℝ x y = 0 := by
    have h := congrArg (fun v : V => inner ℝ x v) hcomb
    simpa only [inner_add_right, inner_smul_right, inner_zero_right] using h
  have hy : a * inner ℝ x y + b * inner ℝ y y = 0 := by
    have h := congrArg (fun v : V => inner ℝ y v) hcomb
    simpa only [inner_add_right, inner_smul_right, inner_zero_right,
      real_inner_comm x y] using h
  have ha : a * (inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2) = 0 := by
    calc
      _ = (a * inner ℝ x x + b * inner ℝ x y) * inner ℝ y y -
          (a * inner ℝ x y + b * inner ℝ y y) * inner ℝ x y := by ring
      _ = 0 := by rw [hx, hy]; ring
  have hb : b * (inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2) = 0 := by
    calc
      _ = (a * inner ℝ x y + b * inner ℝ y y) * inner ℝ x x -
          (a * inner ℝ x x + b * inner ℝ x y) * inner ℝ x y := by ring
      _ = 0 := by rw [hx, hy]; ring
  exact ⟨(mul_eq_zero.mp ha).resolve_right hGram,
    (mul_eq_zero.mp hb).resolve_right hGram⟩

/-- Nonzero Gram determinant implies independence of the exact record pair. -/
theorem linearIndependent_pair_of_gram_ne_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {x y : V}
    (hGram : inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2 ≠ 0) :
    LinearIndependent ℝ ![x, y] := by
  apply LinearIndependent.pair_iff.mpr
  intro a b hcomb
  exact coefficients_zero_of_gram_ne_zero hGram hcomb

/-- A positive Gram certificate discharges the duration theorem's pair premise. -/
theorem linearIndependent_pair_of_positive_gram
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {previousIncrement force : V}
    (hGram : 0 < inner ℝ previousIncrement previousIncrement * inner ℝ force force -
      (inner ℝ previousIncrement force) ^ 2) :
    LinearIndependent ℝ ![previousIncrement, force] :=
  linearIndependent_pair_of_gram_ne_zero (ne_of_gt hGram)

#print axioms coefficients_zero_of_gram_ne_zero
#print axioms linearIndependent_pair_of_gram_ne_zero
#print axioms linearIndependent_pair_of_positive_gram

end OPH.SourceActionTime

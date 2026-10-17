module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Positive energy and the weighted-degree bound for metric kernel actions

The weights and positive volume masses are supplied. These finite algebraic
lemmas support the analytic irregular-population scalar continuum theorem;
they do not derive a population, Voronoi measure, physical clock or PDE limit.
In particular symmetry is imposed on the conductances, not on the generally
nonsymmetric matrix obtained after dividing each row by its volume mass.
-/

namespace OPH.MetricKernelEnergy

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def dirichlet (a : ι → ι → ℝ) (u : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, a i j * (u i - u j)^2) / 2

theorem dirichlet_nonnegative (a : ι → ι → ℝ) (u : ι → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) : 0 ≤ dirichlet a u := by
  unfold dirichlet
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (ha i j) (sq_nonneg _)
  · norm_num

theorem dirichlet_constant (a : ι → ι → ℝ) (c : ℝ) :
    dirichlet a (fun _ => c) = 0 := by simp [dirichlet]

theorem symmetric_second_moment (a : ι → ι → ℝ) (u : ι → ℝ)
    (hs : ∀ i j, a i j = a j i) :
    (∑ i, ∑ j, a i j * (u j)^2) = ∑ i, ∑ j, a i j * (u i)^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs j i]

/-- The actual mass-weighted Rayleigh bound: a row-sum cap `d*v_i`
gives spectral cap `2*d`, not a cap in the unweighted counting norm. -/
theorem weighted_degree_bound (a : ι → ι → ℝ) (v u : ι → ℝ) (d : ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hs : ∀ i j, a i j = a j i)
    (hd : ∀ i, ∑ j, a i j ≤ d * v i) :
    dirichlet a u ≤ 2 * d * ∑ i, v i * (u i)^2 := by
  have hterm (i j : ι) : a i j * (u i - u j)^2 ≤
      2 * (a i j * (u i)^2 + a i j * (u j)^2) := by
    have h := mul_nonneg (ha i j) (sq_nonneg (u i + u j))
    nlinarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset ι)) => hterm i j
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hswap := symmetric_second_moment a u hs
  have hrow : (∑ i, ∑ j, a i j * (u i)^2) ≤
      d * ∑ i, v i * (u i)^2 := by
    calc
      (∑ i, ∑ j, a i j * (u i)^2) =
          ∑ i, (∑ j, a i j) * (u i)^2 := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ i, d * v i * (u i)^2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _)
      _ = d * ∑ i, v i * (u i)^2 := by simp_rw [mul_assoc, Finset.mul_sum]
  unfold dirichlet
  nlinarith

/-- Nonnegative action energy for supplied nonnegative volume masses. -/
theorem massive_energy_nonnegative (a : ι → ι → ℝ) (v u w : ι → ℝ)
    (c m : ℝ) (ha : ∀ i j, 0 ≤ a i j) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ (∑ i, v i * (w i)^2) + c^2 * dirichlet a u +
      m^2 * ∑ i, v i * (u i)^2 := by
  have hu : 0 ≤ ∑ i, v i * (u i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (sq_nonneg _)
  have hw : 0 ≤ ∑ i, v i * (w i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hv i) (sq_nonneg _)
  exact add_nonneg (add_nonneg hw (mul_nonneg (sq_nonneg _) (dirichlet_nonnegative a u ha)))
    (mul_nonneg (sq_nonneg _) hu)

#print axioms weighted_degree_bound
#print axioms massive_energy_nonnegative

end OPH.MetricKernelEnergy

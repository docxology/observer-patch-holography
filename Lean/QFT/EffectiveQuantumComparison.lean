module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Effective quantum comparison estimates and a leakage control

These dimension-independent Hilbert-space estimates prove that an explicitly
differentiable interaction-picture path with a bounded residual has a linear
time error, and transfer vector error to bounded effect probabilities with
constant one. A separate decomposition retains the full omitted vector tail.
The derivative identity is an input here: its verification from unbounded
self-adjoint generators and an energy spectral projection is the analytic
domain argument in `EFFECTIVE_QUANTUM_COMPARISON.tex`. The mixed-state
conditioning and trace-class steps of that paper are also analytic, not
formalized by this module.

An exact two-level Schroedinger trajectory demonstrates why a zero compressed
generator residual does not imply a correct effect probability. Its full
off-image coupling is nonzero. No continuum limit, state embedding for the
charged action, comparison accuracy, or physical clock is selected here.
-/

set_option autoImplicit false

namespace OPH.QFT.EffectiveQuantumComparison

noncomputable section

open scoped InnerProductSpace
open Set

section NormEstimate

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- A genuine derivative bound, rather than a postulated endpoint error,
controls the path throughout either orientation of a time interval. -/
theorem path_error_of_derivative_bound
    (w w' : ℝ → K) (t c : ℝ)
    (hderiv : ∀ s ∈ uIcc 0 t, HasDerivAt w (w' s) s)
    (hbound : ∀ s ∈ uIcc 0 t, ‖w' s‖ ≤ c) :
    ‖w t - w 0‖ ≤ |t| * c := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hderiv s hs).hasDerivWithinAt) hbound
    (convex_uIcc (0 : ℝ) t) (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 t)
    (right_mem_uIcc : t ∈ uIcc 0 t)
  simpa [Real.norm_eq_abs, mul_comm] using h

end NormEstimate

section HilbertEstimate

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Real quadratic readout of a bounded complex-linear operator. -/
def quadraticReadout (A : E →L[ℂ] E) (x : E) : ℝ :=
  (inner ℂ x (A x)).re

/-- The two cross terms are controlled in the full Hilbert norm. -/
theorem quadratic_readout_difference_bound
    (A : E →L[ℂ] E) (x y : E) :
    |quadraticReadout A x - quadraticReadout A y| ≤
      ‖A‖ * ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have heq : inner ℂ x (A x) - inner ℂ y (A y) =
      inner ℂ (x - y) (A x) + inner ℂ y (A (x - y)) := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  calc
    |quadraticReadout A x - quadraticReadout A y|
        = |(inner ℂ x (A x) - inner ℂ y (A y)).re| := by
            simp [quadraticReadout]
    _ ≤ ‖inner ℂ x (A x) - inner ℂ y (A y)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖inner ℂ (x - y) (A x)‖ + ‖inner ℂ y (A (x - y))‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ ≤ ‖x - y‖ * ‖A x‖ + ‖y‖ * ‖A (x - y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x - y‖ * (‖A‖ * ‖x‖) + ‖y‖ * (‖A‖ * ‖x - y‖) := by
      gcongr <;> exact A.le_opNorm _
    _ = ‖A‖ * ‖x - y‖ * (‖x‖ + ‖y‖) := by ring

/-- Centering an effect removes the otherwise unnecessary factor two.
Every self-adjoint effect `0 ≤ A ≤ I` has `‖2 A - I‖ ≤ 1`; that bounded
operator condition is the precise hypothesis used in this estimate. -/
theorem effect_probability_lipschitz
    (A : E →L[ℂ] E)
    (hA : ‖(2 : ℂ) • A - ContinuousLinearMap.id ℂ E‖ ≤ 1)
    (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |quadraticReadout A x - quadraticReadout A y| ≤ ‖x - y‖ := by
  let C : E →L[ℂ] E := (2 : ℂ) • A - ContinuousLinearMap.id ℂ E
  have hcenter (z : E) :
      quadraticReadout C z = 2 * quadraticReadout A z - ‖z‖ ^ 2 := by
    simp [quadraticReadout, C, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, Complex.mul_re, ← Complex.ofReal_pow]
  have h := quadratic_readout_difference_bound C x y
  have hc : ‖C‖ ≤ 1 := hA
  rw [hcenter x, hcenter y, hx, hy] at h
  have h2 : ‖C‖ * ‖x - y‖ * (1 + 1) ≤ 2 * ‖x - y‖ := by
    nlinarith [norm_nonneg (x - y)]
  have habs : |2 * quadraticReadout A x - 1 ^ 2 -
      (2 * quadraticReadout A y - 1 ^ 2)| =
      2 * |quadraticReadout A x - quadraticReadout A y| := by
    rw [show 2 * quadraticReadout A x - 1 ^ 2 -
        (2 * quadraticReadout A y - 1 ^ 2) =
        2 * (quadraticReadout A x - quadraticReadout A y) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs] at h
  linarith

/-- The interaction-picture derivative retains the complete residual vector.
Here `U` is the exact target unitary, `J` the isometric state map, and `v`
the reference path. No compressed generator appears in the hypotheses. -/
theorem interaction_picture_error
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (J : F →ₗᵢ[ℂ] E)
    (v : ℝ → F) (r : ℝ → E) (t hbar eps : ℝ)
    (hhbar : 0 < hbar) (hzero : U 0 = LinearIsometryEquiv.refl ℂ E)
    (hderiv : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun a => (U a).symm (J (v a)))
        ((Complex.I / (hbar : ℂ)) • (U s).symm (r s)) s)
    (hresidual : ∀ s ∈ uIcc 0 t, ‖r s‖ ≤ eps) :
    ‖J (v t) - U t (J (v 0))‖ ≤ |t| * eps / hbar := by
  have hbound : ∀ s ∈ uIcc 0 t,
      ‖(Complex.I / (hbar : ℂ)) • (U s).symm (r s)‖ ≤ eps / hbar := by
    intro s hs
    simp only [norm_smul, norm_div, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hhbar, LinearIsometryEquiv.norm_map]
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (hresidual s hs) (le_of_lt (one_div_pos.mpr hhbar))
  have h := path_error_of_derivative_bound
    (fun a => (U a).symm (J (v a)))
    (fun s => (Complex.I / (hbar : ℂ)) • (U s).symm (r s))
    t (eps / hbar) hderiv hbound
  have hnorm : ‖J (v t) - U t (J (v 0))‖ =
      ‖(U t).symm (J (v t)) - J (v 0)‖ := by
    rw [← (U t).symm.norm_map (J (v t) - U t (J (v 0))), map_sub]
    simp
  have href : (LinearIsometryEquiv.refl ℂ E).symm (J (v 0)) = J (v 0) := rfl
  simpa [hzero, hnorm, div_eq_mul_inv, mul_assoc, href] using h

/-- A bounded detector applied to the full residual comparison has the
same constant-one probability bound. The reference norm is preserved
explicitly; no probability conclusion is included among the hypotheses. -/
theorem effect_error_of_interaction_residual
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (J : F →ₗᵢ[ℂ] E)
    (v : ℝ → F) (r : ℝ → E) (t hbar eps : ℝ)
    (hhbar : 0 < hbar) (hzero : U 0 = LinearIsometryEquiv.refl ℂ E)
    (hderiv : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun a => (U a).symm (J (v a)))
        ((Complex.I / (hbar : ℂ)) • (U s).symm (r s)) s)
    (hresidual : ∀ s ∈ uIcc 0 t, ‖r s‖ ≤ eps)
    (A : E →L[ℂ] E)
    (hA : ‖(2 : ℂ) • A - ContinuousLinearMap.id ℂ E‖ ≤ 1)
    (hv0 : ‖v 0‖ = 1) (hvt : ‖v t‖ = 1) :
    |quadraticReadout A (J (v t)) - quadraticReadout A (U t (J (v 0)))|
      ≤ |t| * eps / hbar := by
  exact (effect_probability_lipschitz A hA _ _
    (by simpa using hvt) (by simpa using hv0)).trans
    (interaction_picture_error U J v r t hbar eps hhbar hzero hderiv hresidual)

/-- A low-energy approximation does not discard the omitted initial vector.
This lemma needs no invariance of the low-energy image in the target space. -/
theorem propagation_error_with_tail
    (U : E ≃ₗᵢ[ℂ] E) (V : F ≃ₗᵢ[ℂ] F) (J : F →ₗᵢ[ℂ] E)
    (x low : F) (b tail : ℝ)
    (hlow : ‖U (J low) - J (V low)‖ ≤ b)
    (htail : ‖x - low‖ ≤ tail) :
    ‖U (J x) - J (V x)‖ ≤ b + 2 * tail := by
  have heq : U (J x) - J (V x) =
      (U (J low) - J (V low)) +
        (U (J (x - low)) - J (V (x - low))) := by
    simp only [map_sub]
    abel
  calc
    ‖U (J x) - J (V x)‖ ≤ ‖U (J low) - J (V low)‖ +
        ‖U (J (x - low)) - J (V (x - low))‖ := by
      rw [heq]
      exact norm_add_le _ _
    _ ≤ b + (‖U (J (x - low))‖ + ‖J (V (x - low))‖) :=
      add_le_add hlow (norm_sub_le _ _)
    _ ≤ b + 2 * tail := by
      simp only [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
      linarith

end HilbertEstimate

section LeakageControl

/-- `sigma_x` acts on both coordinates; no compression is built into it. -/
def leakageHamiltonian (x : Fin 2 → ℂ) : Fin 2 → ℂ := ![x 1, x 0]

def leakageEmbedding (z : ℂ) : Fin 2 → ℂ := ![z, 0]

def leakageState (t : ℝ) : Fin 2 → ℂ :=
  ![(Real.cos t : ℂ), -Complex.I * (Real.sin t : ℂ)]

def leakageProbability (t : ℝ) : ℝ := Complex.normSq (leakageState t 0)

/-- The declared full two-level Hamiltonian is Hermitian in the ordinary
complex counting inner product. -/
theorem leakage_hamiltonian_hermitian (x y : Fin 2 → ℂ) :
    (∑ i : Fin 2, star (x i) * leakageHamiltonian y i) =
      ∑ i : Fin 2, star (leakageHamiltonian x i) * y i := by
  simp [leakageHamiltonian, Fin.sum_univ_two, add_comm]

/-- The effective one-dimensional Hamiltonian is zero after compression. -/
theorem compressed_residual_zero (z : ℂ) :
    leakageHamiltonian (leakageEmbedding z) 0 = 0 := by
  simp [leakageHamiltonian, leakageEmbedding]

/-- Its omitted target component has squared Hilbert norm one on the unit
initial vector. This is the residual that compression would hide. -/
theorem full_residual_norm_squared :
    (∑ i : Fin 2, Complex.normSq (leakageHamiltonian (leakageEmbedding 1) i)) = 1 := by
  norm_num [leakageHamiltonian, leakageEmbedding, Fin.sum_univ_two]

theorem leakage_initial_state : leakageState 0 = leakageEmbedding 1 := by
  simp [leakageState, leakageEmbedding]

/-- Explicit full Schroedinger equation at hbar=1. -/
theorem leakage_state_schroedinger (t : ℝ) :
    HasDerivAt leakageState ((-Complex.I) • leakageHamiltonian (leakageState t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [leakageState, leakageHamiltonian, neg_mul, mul_neg,
      ← mul_assoc, Complex.I_mul_I]
      using (Real.hasDerivAt_cos t).ofReal_comp
  · simpa [leakageState, leakageHamiltonian]
      using (Real.hasDerivAt_sin t).ofReal_comp.const_mul (-Complex.I)

theorem leakage_state_normalized (t : ℝ) :
    (∑ i : Fin 2, Complex.normSq (leakageState t i)) = 1 := by
  simpa only [leakageState, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_I, Complex.normSq_ofReal, one_mul, pow_two]
    using Real.cos_sq_add_sin_sq t

/-- Zero compressed residual and zero initial/detector mismatch coexist
with an actual probability discrepancy of one. -/
theorem zero_compressed_residual_does_not_control_probability :
    (∀ z : ℂ, leakageHamiltonian (leakageEmbedding z) 0 = 0) ∧
    leakageState 0 = leakageEmbedding 1 ∧
    |leakageProbability (Real.pi / 2) - 1| = 1 := by
  refine ⟨compressed_residual_zero, leakage_initial_state, ?_⟩
  norm_num [leakageProbability, leakageState, Real.cos_pi_div_two]

end LeakageControl

#print axioms path_error_of_derivative_bound
#print axioms quadratic_readout_difference_bound
#print axioms effect_probability_lipschitz
#print axioms interaction_picture_error
#print axioms effect_error_of_interaction_residual
#print axioms propagation_error_with_tail
#print axioms compressed_residual_zero
#print axioms full_residual_norm_squared
#print axioms leakage_initial_state
#print axioms leakage_state_schroedinger
#print axioms leakage_state_normalized
#print axioms leakage_hamiltonian_hermitian
#print axioms zero_compressed_residual_does_not_control_probability

end

end OPH.QFT.EffectiveQuantumComparison

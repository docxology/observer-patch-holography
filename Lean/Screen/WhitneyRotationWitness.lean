module
public import WhitneyFrameNaturality

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace OPH.WhitneyRotationWitness

open OPH.WhitneyQuantumBridge
open OPH.WhitneyFrameNaturality

noncomputable section

abbrev TwoModeSpace := Fin 2 → ℝ

def dotMass₂ : LinearMap.BilinForm ℝ TwoModeSpace :=
  LinearMap.mk₂ ℝ (fun x y => ∑ k, x k * y k)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [Fin.sum_univ_two]; ring)
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [Fin.sum_univ_two]; ring)

def standardVector : Fin 2 → TwoModeSpace
  | 0 => ![1, 0]
  | 1 => ![0, 1]

def rotatedVector : Fin 2 → TwoModeSpace
  | 0 => ![3 / 5, 4 / 5]
  | 1 => ![-4 / 5, 3 / 5]

theorem span_standardVector :
    Submodule.span ℝ (Set.range standardVector) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have h₀ : standardVector 0 ∈ Submodule.span ℝ (Set.range standardVector) :=
    Submodule.subset_span (Set.mem_range_self 0)
  have h₁ : standardVector 1 ∈ Submodule.span ℝ (Set.range standardVector) :=
    Submodule.subset_span (Set.mem_range_self 1)
  have hsum := Submodule.add_mem _
    (Submodule.smul_mem _ (x 0) h₀) (Submodule.smul_mem _ (x 1) h₁)
  convert hsum using 1
  funext k
  fin_cases k <;> simp [standardVector]

theorem span_rotatedVector :
    Submodule.span ℝ (Set.range rotatedVector) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have h₀ : rotatedVector 0 ∈ Submodule.span ℝ (Set.range rotatedVector) :=
    Submodule.subset_span (Set.mem_range_self 0)
  have h₁ : rotatedVector 1 ∈ Submodule.span ℝ (Set.range rotatedVector) :=
    Submodule.subset_span (Set.mem_range_self 1)
  let q₀ := (3 / 5 : ℝ) * x 0 + (4 / 5 : ℝ) * x 1
  let q₁ := (-4 / 5 : ℝ) * x 0 + (3 / 5 : ℝ) * x 1
  have hsum := Submodule.add_mem _
    (Submodule.smul_mem _ q₀ h₀) (Submodule.smul_mem _ q₁ h₁)
  convert hsum using 1
  funext k
  fin_cases k <;> simp [rotatedVector, q₀, q₁] <;> ring

def standardFrame : PositiveNormalFrame (ι := Fin 2) dotMass₂ dotMass₂
    (0 : TwoModeSpace →ₗ[ℝ] ℝ) where
  vector := standardVector
  omega := fun _ => 1
  positive := by intro; norm_num
  mass_orthonormal := by
    intro x y
    fin_cases x <;> fin_cases y <;> norm_num [dotMass₂, standardVector, Fin.sum_univ_two]
  eigenmode := by
    intro x y
    simp [dotMass₂]
  complete := by
    rw [LinearMap.ker_zero, span_standardVector]

def rotatedFrame : PositiveNormalFrame (ι := Fin 2) dotMass₂ dotMass₂
    (0 : TwoModeSpace →ₗ[ℝ] ℝ) where
  vector := rotatedVector
  omega := fun _ => 1
  positive := by intro; norm_num
  mass_orthonormal := by
    intro x y
    fin_cases x <;> fin_cases y <;>
      norm_num [dotMass₂, rotatedVector, Fin.sum_univ_two]
  eigenmode := by
    intro x y
    simp [dotMass₂]
  complete := by
    rw [LinearMap.ker_zero, span_rotatedVector]

theorem dotMass₂_symm : dotMass₂.IsSymm := by
  constructor
  intro x y
  simp [dotMass₂, mul_comm]

/-- A genuine non-permutation overlap entry. -/
theorem rotated_overlap_off_diagonal :
    frameOverlap standardFrame rotatedFrame 1 0 = -4 / 5 := by
  norm_num [frameOverlap, dotMass₂, standardFrame, rotatedFrame,
    standardVector, rotatedVector, Fin.sum_univ_two]

theorem rotated_classical_action_naturality (q velocity : Fin 2 → ℝ) :
    (∑ x, (velocity x ^ 2 - standardFrame.omega x ^ 2 * q x ^ 2) / 2) =
      ∑ y, ((frameTransition standardFrame rotatedFrame velocity y) ^ 2 -
        rotatedFrame.omega y ^ 2 * (frameTransition standardFrame rotatedFrame q y) ^ 2) / 2 := by
  rw [← same_action_normal_modes standardFrame q velocity,
    ← same_action_normal_modes rotatedFrame (frameTransition standardFrame rotatedFrame q)
      (frameTransition standardFrame rotatedFrame velocity)]
  rw [reconstruct_frameTransition standardFrame rotatedFrame dotMass₂_symm q,
    reconstruct_frameTransition standardFrame rotatedFrame dotMass₂_symm velocity]

theorem rotated_quantumHamiltonian_naturality
    (hbar : ℝ) (p : ParticlePolynomial (Fin 2)) :
    quantumHamiltonian hbar rotatedFrame.omega
        (polynomialTransport standardFrame rotatedFrame p) =
      polynomialTransport standardFrame rotatedFrame
        (quantumHamiltonian hbar standardFrame.omega p) :=
  quantumHamiltonian_polynomialTransport standardFrame rotatedFrame
    dotMass₂_symm dotMass₂_symm hbar p

#print axioms rotated_overlap_off_diagonal
#print axioms rotated_classical_action_naturality
#print axioms rotated_quantumHamiltonian_naturality

end
end OPH.WhitneyRotationWitness

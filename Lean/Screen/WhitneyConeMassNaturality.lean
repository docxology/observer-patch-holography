module
public import WhitneyConeMass
public import WhitneyFrameMorphism

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace OPH.WhitneyConeMassNaturality

open OPH.ConeCochainBridge
open OPH.WhitneyQuantumBridge
open OPH.WhitneyConeMass
open OPH.WhitneyFrameNaturality

noncomputable section

variable (mass₁ : LinearMap.BilinForm ℝ ConeOne)
  (mass₂ : LinearMap.BilinForm ℝ ConeTwo)
  (mass₁_symm : mass₁.IsSymm) (mass₂_symm : mass₂.IsSymm)
  (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x)
  (mass₂_pos : ∀ x : ConeTwo, x ≠ 0 → 0 < mass₂ x x)

local notation "Fₘ" => conePositiveNormalFrameWithMass mass₁ mass₂
  mass₁_symm mass₂_symm mass₁_pos mass₂_pos

theorem actual_cone_two_frame_reconstruction
    (G : PositiveNormalFrame (ι := Fin 30) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁)) (q : Fin 30 → ℝ) :
    reconstruct G.vector (frameTransition Fₘ G q) = reconstruct (Fₘ).vector q :=
  reconstruct_frameTransition Fₘ G mass₁_symm q

theorem actual_cone_classical_action_naturality
    (G : PositiveNormalFrame (ι := Fin 30) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁)) (q velocity : Fin 30 → ℝ) :
    (∑ x, (velocity x ^ 2 - (Fₘ).omega x ^ 2 * q x ^ 2) / 2) =
      ∑ y, ((frameTransition Fₘ G velocity y) ^ 2 -
        G.omega y ^ 2 * (frameTransition Fₘ G q y) ^ 2) / 2 := by
  rw [← same_action_normal_modes Fₘ q velocity,
    ← same_action_normal_modes G (frameTransition Fₘ G q)
      (frameTransition Fₘ G velocity)]
  rw [reconstruct_frameTransition Fₘ G mass₁_symm q,
    reconstruct_frameTransition Fₘ G mass₁_symm velocity]

theorem actual_cone_quantumHamiltonian_naturality
    (G : PositiveNormalFrame (ι := Fin 30) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁))
    (hbar : ℝ) (p : ParticlePolynomial (Fin 30)) :
    quantumHamiltonian hbar G.omega (polynomialTransport Fₘ G p) =
      polynomialTransport Fₘ G (quantumHamiltonian hbar (Fₘ).omega p) :=
  quantumHamiltonian_polynomialTransport Fₘ G mass₁_symm
    (coneStiffnessWithMass_symm mass₂ mass₂_symm) hbar p

/-- Every admissible frame for the source mass action has exactly thirty modes;
`Fin 30` is derived rather than chosen. -/
theorem actual_cone_frame_card_eq_thirty
    {i : Type*} [Fintype i] [DecidableEq i]
    (G : PositiveNormalFrame (ι := i) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁))
    (hMassPos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x) :
    Fintype.card i = 30 := by
  rw [frame_card_eq_sector_finrank G]
  exact coneConstraintWithMass_kernel_finrank mass₁ hMassPos

/-- An explicit different admissible source frame, obtained by reversing all
mode orientations. -/
def actual_cone_sign_frame :
    PositiveNormalFrame (ι := Fin 30) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁) :=
  signFlipFrame Fₘ

theorem actual_cone_sign_frame_ne :
    actual_cone_sign_frame mass₁ mass₂ mass₁_symm mass₂_symm
      mass₁_pos mass₂_pos ≠ Fₘ :=
  signFlipFrame_ne Fₘ

theorem actual_cone_sign_classical_naturality (q velocity : Fin 30 → ℝ) :
    (∑ x, (velocity x ^ 2 - (Fₘ).omega x ^ 2 * q x ^ 2) / 2) =
      ∑ y, ((frameTransition Fₘ (signFlipFrame Fₘ) velocity y) ^ 2 -
        (signFlipFrame Fₘ).omega y ^ 2 *
          (frameTransition Fₘ (signFlipFrame Fₘ) q y) ^ 2) / 2 :=
  actual_cone_classical_action_naturality mass₁ mass₂ mass₁_symm mass₂_symm
    mass₁_pos mass₂_pos (signFlipFrame Fₘ) q velocity

theorem actual_cone_sign_quantum_naturality
    (hbar : ℝ) (p : ParticlePolynomial (Fin 30)) :
    quantumHamiltonian hbar (signFlipFrame Fₘ).omega
        (polynomialTransport Fₘ (signFlipFrame Fₘ) p) =
      polynomialTransport Fₘ (signFlipFrame Fₘ)
        (quantumHamiltonian hbar (Fₘ).omega p) :=
  actual_cone_quantumHamiltonian_naturality mass₁ mass₂ mass₁_symm mass₂_symm
    mass₁_pos mass₂_pos (signFlipFrame Fₘ) hbar p

def actual_cone_reindex_frame
    (e : Fin 30 ≃ Fin 30) :
    PositiveNormalFrame (ι := Fin 30) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁) :=
  reindexFrame Fₘ e

theorem actual_cone_unequal_frequency_overlap_zero
    (G : PositiveNormalFrame (ι := Fin 30) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁))
    (y x : Fin 30) (hne : G.omega y ≠ (Fₘ).omega x) :
    frameOverlap Fₘ G y x = 0 :=
  frameOverlap_eq_zero_of_frequency_ne Fₘ G mass₁_symm
    (coneStiffnessWithMass_symm mass₂ mass₂_symm) y x hne

#print axioms actual_cone_two_frame_reconstruction
#print axioms actual_cone_classical_action_naturality
#print axioms actual_cone_quantumHamiltonian_naturality
#print axioms actual_cone_frame_card_eq_thirty
#print axioms actual_cone_sign_frame_ne
#print axioms actual_cone_sign_classical_naturality
#print axioms actual_cone_sign_quantum_naturality
#print axioms actual_cone_unequal_frequency_overlap_zero

end
end OPH.WhitneyConeMassNaturality

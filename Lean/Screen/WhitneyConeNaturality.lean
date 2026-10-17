module
public import WhitneyFrameMorphism

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace OPH.WhitneyConeNaturality

open OPH.WhitneyQuantumBridge
open OPH.WhitneyNormalModes
open OPH.WhitneyConeModes
open OPH.WhitneyFrameNaturality
open OPH.WhitneyFrameMorphism
open OPH.WhitneyFrameMorphism.FrameIsometry

noncomputable section

theorem coneMass_symm :
    LinearMap.BilinForm.IsSymm (innerₗ ConeOneL2) :=
  ⟨fun x y => by
    change inner ℝ x y = inner ℝ y x
    exact real_inner_comm y x⟩

/-- The generated 30-mode cone frame and every other admissible complete
frame reconstruct the same constrained field after the source-derived
coordinate transition. -/
theorem cone_two_frame_reconstruction
    (G : PositiveNormalFrame (ι := Fin 30) (innerₗ ConeOneL2)
      coneStiffness coneConstraint)
    (q : Fin 30 → ℝ) :
    reconstruct G.vector
        (frameTransition conePositiveNormalFrame G q) =
      reconstruct conePositiveNormalFrame.vector q :=
  reconstruct_frameTransition conePositiveNormalFrame G coneMass_symm q

/-- The existing classical action consumer is independent of sign, order,
and orthogonal rotations inside degenerate eigenspaces. -/
theorem cone_classical_action_naturality
    (G : PositiveNormalFrame (ι := Fin 30) (innerₗ ConeOneL2)
      coneStiffness coneConstraint)
    (q velocity : Fin 30 → ℝ) :
    (∑ x, (velocity x ^ 2 - conePositiveNormalFrame.omega x ^ 2 * q x ^ 2) / 2) =
      ∑ y, ((frameTransition conePositiveNormalFrame G velocity y) ^ 2 -
        G.omega y ^ 2 * (frameTransition conePositiveNormalFrame G q y) ^ 2) / 2 := by
  simpa [transition, mapFrame, FrameIsometry.refl] using
    classicalAction_naturality
      (refl (mass₁ := innerₗ ConeOneL2) (stiffness₁ := coneStiffness)
        (constraint₁ := coneConstraint))
      conePositiveNormalFrame G coneMass_symm q velocity

/-- The published polynomial Hamiltonian, including its zero-point term, is
the same operator after the induced general linear change of mode variables. -/
theorem cone_quantumHamiltonian_naturality
    (G : PositiveNormalFrame (ι := Fin 30) (innerₗ ConeOneL2)
      coneStiffness coneConstraint)
    (hbar : ℝ) (p : ParticlePolynomial (Fin 30)) :
    quantumHamiltonian hbar G.omega
        (polynomialTransport conePositiveNormalFrame G p) =
      polynomialTransport conePositiveNormalFrame G
        (quantumHamiltonian hbar conePositiveNormalFrame.omega p) :=
  quantumHamiltonian_polynomialTransport conePositiveNormalFrame G
    coneMass_symm coneStiffness_symm hbar p

theorem cone_transition_identity :
    frameTransition conePositiveNormalFrame conePositiveNormalFrame = LinearMap.id :=
  frameTransition_self conePositiveNormalFrame coneMass_symm

theorem cone_transition_composition
    (G H : PositiveNormalFrame (ι := Fin 30) (innerₗ ConeOneL2)
      coneStiffness coneConstraint) :
    (frameTransition G H).comp (frameTransition conePositiveNormalFrame G) =
      frameTransition conePositiveNormalFrame H :=
  frameTransition_comp conePositiveNormalFrame G H coneMass_symm

theorem cone_polynomial_identity :
    polynomialTransport conePositiveNormalFrame conePositiveNormalFrame =
      AlgHom.id ℂ (ParticlePolynomial (Fin 30)) :=
  polynomialTransport_self conePositiveNormalFrame

theorem cone_polynomial_composition
    (G H : PositiveNormalFrame (ι := Fin 30) (innerₗ ConeOneL2)
      coneStiffness coneConstraint) :
    (polynomialTransport G H).comp
        (polynomialTransport conePositiveNormalFrame G) =
      polynomialTransport conePositiveNormalFrame H :=
  polynomialTransport_comp conePositiveNormalFrame G H coneMass_symm

/-- Unequal-frequency modes cannot be mixed by an admissible basis change. -/
theorem cone_unequal_frequency_overlap_zero
    (G : PositiveNormalFrame (ι := Fin 30) (innerₗ ConeOneL2)
      coneStiffness coneConstraint)
    (y x : Fin 30) (hne : G.omega y ≠ conePositiveNormalFrame.omega x) :
    frameOverlap conePositiveNormalFrame G y x = 0 :=
  frameOverlap_eq_zero_of_frequency_ne conePositiveNormalFrame G
    coneMass_symm coneStiffness_symm y x hne

theorem cone_no_sign_fixed_frame :
    ¬ ∀ x, -conePositiveNormalFrame.vector x =
      conePositiveNormalFrame.vector x :=
  no_frame_fixed_by_neg conePositiveNormalFrame

#print axioms cone_two_frame_reconstruction
#print axioms cone_classical_action_naturality
#print axioms cone_quantumHamiltonian_naturality
#print axioms cone_transition_identity
#print axioms cone_transition_composition
#print axioms cone_polynomial_identity
#print axioms cone_polynomial_composition
#print axioms cone_unequal_frequency_overlap_zero
#print axioms cone_no_sign_fixed_frame

end

end OPH.WhitneyConeNaturality

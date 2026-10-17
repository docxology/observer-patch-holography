module
public import WhitneyConeMass

@[expose] public section

set_option autoImplicit false

namespace OPH.WhitneyMassPremiseInstance

open OPH.ConeCochainBridge
open OPH.WhitneyConeModes
open OPH.WhitneyConeMass

noncomputable section

/-- A concrete positive mass on raw cone one-cochains, induced by the frozen
mass-coordinate equivalence. This witnesses consistency of the general `M₁`
premise without claiming equality to the manuscript's numerical matrix. -/
def countingMass₁ : LinearMap.BilinForm ℝ ConeOne :=
  LinearMap.mk₂ ℝ
    (fun x y => inner ℝ (coneOneCoordinates.symm x) (coneOneCoordinates.symm y))
    (by intros; simp [map_add, inner_add_left])
    (by intros; simp [map_smul, real_inner_smul_left])
    (by intros; simp [map_add, inner_add_right])
    (by intros; simp [map_smul, real_inner_smul_right])

def countingMass₂ : LinearMap.BilinForm ℝ ConeTwo :=
  LinearMap.mk₂ ℝ
    (fun x y => inner ℝ (coneTwoCoordinates.symm x) (coneTwoCoordinates.symm y))
    (by intros; simp [map_add, inner_add_left])
    (by intros; simp [map_smul, real_inner_smul_left])
    (by intros; simp [map_add, inner_add_right])
    (by intros; simp [map_smul, real_inner_smul_right])

theorem countingMass₁_symm : countingMass₁.IsSymm := by
  constructor
  intro x y
  change inner ℝ (coneOneCoordinates.symm x) (coneOneCoordinates.symm y) =
    inner ℝ (coneOneCoordinates.symm y) (coneOneCoordinates.symm x)
  exact real_inner_comm _ _

theorem countingMass₂_symm : countingMass₂.IsSymm := by
  constructor
  intro x y
  change inner ℝ (coneTwoCoordinates.symm x) (coneTwoCoordinates.symm y) =
    inner ℝ (coneTwoCoordinates.symm y) (coneTwoCoordinates.symm x)
  exact real_inner_comm _ _

theorem countingMass₁_pos (x : ConeOne) (hne : x ≠ 0) :
    0 < countingMass₁ x x := by
  change 0 < inner ℝ (coneOneCoordinates.symm x) (coneOneCoordinates.symm x)
  apply real_inner_self_pos.mpr
  intro hzero
  apply hne
  have := congrArg coneOneCoordinates hzero
  simpa using this

theorem countingMass₂_pos (x : ConeTwo) (hne : x ≠ 0) :
    0 < countingMass₂ x x := by
  change 0 < inner ℝ (coneTwoCoordinates.symm x) (coneTwoCoordinates.symm x)
  apply real_inner_self_pos.mpr
  intro hzero
  apply hne
  have := congrArg coneTwoCoordinates hzero
  simpa using this

/-- Concrete activation of the raw-cone arbitrary-mass constructor. -/
def countingMassConeFrame :=
  conePositiveNormalFrameWithMass countingMass₁ countingMass₂
    countingMass₁_symm countingMass₂_symm countingMass₁_pos countingMass₂_pos

theorem countingMassConeFrame_has_thirty_modes :
    Fintype.card (Fin 30) = 30 := rfl

#print axioms countingMass₁_pos
#print axioms countingMass₂_pos
#print axioms countingMassConeFrame

end
end OPH.WhitneyMassPremiseInstance

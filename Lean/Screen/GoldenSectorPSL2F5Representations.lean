module
public import Mathlib.RepresentationTheory.Basic
public import GoldenSectorIrreducibility
public import PSL2F5SixAxesBridge

@[expose] public section

open scoped Matrix

namespace OPH.GoldenSectorPSL2F5Representations

open OPH.A5PortAction
open OPH.CarrierModeEquivariance
open OPH.GoldenSectorCharacters
open OPH.GoldenSectorIrreducibility
open OPH.A5PortGroupBridge
open OPH.PSL2F5SixAxesBridge

/-!
# Typed projective-group representations on the two golden pieces

The sixty committed twelve-port rotations form `PortGroup`, and the existing
face-field action has a genuine left-action convention
`leftFace p = pullFace (invPerm p)`.  This file packages that action as a
linear representation, restricts it to either rank-three golden projector
image `W C`, and transports it along the certified group isomorphism
`PSL2F5 ≃* PortGroup`.

Pullback along the canonical center quotient `SL2F5 → PSL2F5` gives an
`SL2F5` representation on each golden piece.  Every element of the center,
in particular `-1`, acts trivially because the representation factors through
the quotient.

BOUNDARY.  This file does not prove `PSL(2,5) ≅ A5`, identify `SL(2,5)` with
the binary icosahedral group, construct a faithful two-dimensional spinor
representation, invoke McKay, derive or select `φ`, state a mass law, or
identify the finite action with physical rotations.
-/

/-! ## 1. Recover the committed list row carried by a `PortGroup` element -/

/-- Row `i` of the committed `A5PortAction.perms` list. -/
def portRowAt (i : Fin 60) : List Nat :=
  OPH.A5PortAction.perms.get
    ⟨i.val, by rw [OPH.A5PortAction.perms_length]; exact i.isLt⟩

set_option maxHeartbeats 4000000 in
/-- Every indexed row is one of the committed port-action rows. -/
theorem portRowAt_mem : ∀ i : Fin 60, portRowAt i ∈ perms := by
  decide

/-- Row zero is the identity row. -/
theorem portRowAt_zero : portRowAt 0 = List.range 12 := by
  decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
/-- The row law agrees with the multiplication table certified on
`PortGroup`; this is an exact finite-table check, not an order argument. -/
theorem portRowAt_mul : ∀ i j : Fin 60,
    portRowAt (portMulIndex i j) = comp (portRowAt i) (portRowAt j) := by
  decide

/-- The committed row represented by a typed `PortGroup` element. -/
noncomputable def portRow (g : PortGroup) : List Nat :=
  portRowAt (portIndex g)

/-- A typed port-group element always selects a committed row. -/
theorem portRow_mem (g : PortGroup) : portRow g ∈ perms :=
  portRowAt_mem (portIndex g)

/-- The identity port-group element selects the identity row. -/
theorem portRow_one : portRow (1 : PortGroup) = List.range 12 := by
  rw [portRow, portIndex_one, portRowAt_zero]

/-- Row selection respects multiplication in `PortGroup`. -/
theorem portRow_mul (g h : PortGroup) :
    portRow (g * h) = comp (portRow g) (portRow h) := by
  rw [portRow, portIndex_mul, portRowAt_mul]
  rfl

/-! ## 2. The genuine left representation on face fields -/

/-- The existing left face action as a real linear endomorphism.  It is the
matrix action of the inverse committed row, hence is definitionally tied to
the exact face-action tables used by the golden-sector certificates. -/
noncomputable def leftFaceLinear (p : List Nat) :
    (Fin 20 → ℝ) →ₗ[ℝ] (Fin 20 → ℝ) :=
  Matrix.toLin' (gR (invPerm p))

@[simp]
theorem leftFaceLinear_apply (p : List Nat) (F : Fin 20 → ℝ) :
    leftFaceLinear p F = leftFace p F := by
  simp only [leftFaceLinear, Matrix.toLin'_apply, gR, leftFace]
  exact faceActZ_mulVec (invPerm p) F

/-- The actual typed port group acts linearly on the twenty-dimensional face
field by the existing left-action convention. -/
noncomputable def facePortRepresentation :
    Representation ℝ PortGroup (Fin 20 → ℝ) where
  toFun g := leftFaceLinear (portRow g)
  map_one' := by
    apply LinearMap.ext
    intro F
    change leftFaceLinear (portRow (1 : PortGroup)) F = F
    rw [leftFaceLinear_apply, portRow_one, leftFace_id]
  map_mul' g h := by
    apply LinearMap.ext
    intro F
    change leftFaceLinear (portRow (g * h)) F =
      leftFaceLinear (portRow g) (leftFaceLinear (portRow h) F)
    simp only [leftFaceLinear_apply]
    rw [portRow_mul]
    exact leftFace_comp (portRow g) (portRow_mem g)
      (portRow h) (portRow_mem h) F

/-! ## 3. Restriction to either golden projector image -/

/-- Every committed left face action preserves either golden projector image.
This is the existing `W_invariant` theorem applied to the listed inverse row. -/
theorem W_leftFace_invariant (C : GoldenCert) (p : List Nat) (hp : p ∈ perms)
    {w : Fin 20 → ℝ} (hw : w ∈ W C) : leftFace p w ∈ W C := by
  have h := W_invariant C (invPerm p) (inv_spec p hp).1 hw
  simpa only [gR, faceActZ_mulVec, leftFace] using h

/-- The committed port group as a genuine representation on a golden
rank-three piece. -/
noncomputable def goldenPortRepresentation (C : GoldenCert) :
    Representation ℝ PortGroup (W C) :=
  Representation.subrepresentation facePortRepresentation (W C) fun g w hw => by
    change leftFaceLinear (portRow g) w ∈ W C
    rw [leftFaceLinear_apply]
    exact W_leftFace_invariant C (portRow g) (portRow_mem g) hw

/-- The `λ₊` golden piece as a typed `PortGroup` representation. -/
noncomputable def goldenPlusPortRepresentation :
    Representation ℝ PortGroup (W plusCert) :=
  goldenPortRepresentation plusCert

/-- The `λ₋` golden piece as a typed `PortGroup` representation. -/
noncomputable def goldenMinusPortRepresentation :
    Representation ℝ PortGroup (W minusCert) :=
  goldenPortRepresentation minusCert

/-! ## 4. Transport to the abstract projective group -/

/-- Transport a golden-piece representation through the certified
`PSL2F5 ≃* PortGroup` bridge. -/
noncomputable def goldenPSLRepresentation (C : GoldenCert) :
    Representation ℝ PSL2F5 (W C) :=
  (goldenPortRepresentation C).comp pslEquivPortGroup.toMonoidHom

/-- The `λ₊` golden piece as a typed `PSL2F5` representation. -/
noncomputable def goldenPlusPSLRepresentation :
    Representation ℝ PSL2F5 (W plusCert) :=
  goldenPSLRepresentation plusCert

/-- The `λ₋` golden piece as a typed `PSL2F5` representation. -/
noncomputable def goldenMinusPSLRepresentation :
    Representation ℝ PSL2F5 (W minusCert) :=
  goldenPSLRepresentation minusCert

/-! ## 5. Pullback to `SL2F5` and the central kernel -/

/-- Pull a golden projective representation back through the canonical
center quotient `SL2F5 → PSL2F5`. -/
noncomputable def goldenSLRepresentation (C : GoldenCert) :
    Representation ℝ SL2F5 (W C) :=
  (goldenPSLRepresentation C).comp slToPsl

/-- Every central element of `SL2F5` acts trivially on either golden piece. -/
theorem goldenSL_center_trivial (C : GoldenCert) (A : SL2F5)
    (hA : A ∈ Subgroup.center SL2F5) : goldenSLRepresentation C A = 1 := by
  have hq : slToPsl A = 1 := by
    change A ∈ slToPsl.ker
    rw [slToPsl_ker_center]
    exact hA
  change goldenPSLRepresentation C (slToPsl A) = 1
  rw [hq, map_one]

/-- The central element `-1` acts trivially on either golden piece. -/
theorem goldenSL_neg_one_trivial (C : GoldenCert) :
    goldenSLRepresentation C (-1) = 1 := by
  apply goldenSL_center_trivial
  exact (center_mem_iff_plus_minus_one (-1)).2 (Or.inr rfl)

/-- In particular the `λ₊` golden triplet is center-trivial on `SL2F5`. -/
theorem goldenPlusSL_neg_one_trivial :
    goldenSLRepresentation plusCert (-1) = 1 :=
  goldenSL_neg_one_trivial plusCert

/-- In particular the `λ₋` golden triplet is center-trivial on `SL2F5`. -/
theorem goldenMinusSL_neg_one_trivial :
    goldenSLRepresentation minusCert (-1) = 1 :=
  goldenSL_neg_one_trivial minusCert

end OPH.GoldenSectorPSL2F5Representations

/- Axiom audit: no `sorry`, `admit`, new axioms, or `native_decide`. -/

#print axioms OPH.GoldenSectorPSL2F5Representations.portRowAt_mul
#print axioms OPH.GoldenSectorPSL2F5Representations.facePortRepresentation
#print axioms OPH.GoldenSectorPSL2F5Representations.goldenPortRepresentation
#print axioms OPH.GoldenSectorPSL2F5Representations.goldenPlusPSLRepresentation
#print axioms OPH.GoldenSectorPSL2F5Representations.goldenMinusPSLRepresentation
#print axioms OPH.GoldenSectorPSL2F5Representations.goldenSL_center_trivial
#print axioms OPH.GoldenSectorPSL2F5Representations.goldenPlusSL_neg_one_trivial
#print axioms OPH.GoldenSectorPSL2F5Representations.goldenMinusSL_neg_one_trivial

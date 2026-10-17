module
public import PSL2F5SixAxesBridge

@[expose] public section

/-!
# The canonical `SL(2, F5)` cover of the committed port group

The existing bridge identifies Mathlib's `PSL(2,F5)` quotient with the typed
subgroup of the sixty committed twelve-port rotations. This module composes
that isomorphism with the canonical quotient `SL(2,F5) → PSL(2,F5)` and records
the resulting group-level cover of the actual port action.

The map is surjective, its kernel is exactly the scalar center `{+I,-I}`, and
therefore the central element `-I` lies over the identity port rotation. The
commuting square is definitionally the one certified by the projective
and port-group bridges.

This is deliberately only the canonical finite-group cover interface. In
particular, this file does not identify `SL(2,5)` with the executable
`PORT-SPIN-LIFT` from the super-Tannakian matter certificate, does not identify
that group with the binary icosahedral group, does not construct a faithful
two-dimensional complex spinor representation, does not invoke McKay/E8,
does not select `φ`, and makes no physical-rotation or mass claim.
-/

namespace OPH.SL2F5PortCover

open OPH.PSL2F5SixAxesBridge
open OPH.A5PortGroupBridge

abbrev F5 := OPH.PSL2F5SixAxesBridge.F5
abbrev SL2F5 := OPH.PSL2F5SixAxesBridge.SL2F5
abbrev PSL2F5 := OPH.PSL2F5SixAxesBridge.PSL2F5
abbrev PortGroup := OPH.A5PortGroupBridge.PortGroup

/-- The certified projective group isomorphism, exposed as a
homomorphism into the committed twelve-port rotation group. -/
noncomputable def pslToPort : PSL2F5 →* PortGroup :=
  pslEquivPortGroup.toMonoidHom

/-- The canonical determinant-one cover of the committed port group. -/
noncomputable def slToPort : SL2F5 →* PortGroup :=
  pslToPort.comp slToPsl

@[simp]
theorem slToPort_apply (A : SL2F5) :
    slToPort A = pslToPort (slToPsl A) :=
  rfl

/-- The projective-to-port map is faithful. -/
theorem pslToPort_injective : Function.Injective pslToPort := by
  simpa [pslToPort] using pslEquivPortGroup.injective

/-- Every committed port rotation is reached by the projective group. -/
theorem pslToPort_surjective : Function.Surjective pslToPort := by
  simpa [pslToPort] using pslEquivPortGroup.surjective

/-- Every committed port rotation has a determinant-one lift. -/
theorem slToPort_surjective : Function.Surjective slToPort := by
  intro g
  obtain ⟨q, hq⟩ := pslToPort_surjective g
  obtain ⟨A, hA⟩ := slToPsl_surjective q
  refine ⟨A, ?_⟩
  simpa [slToPort, hA] using hq

/-- The kernel of the port cover is exactly the canonical scalar center. -/
theorem slToPort_ker : slToPort.ker = Subgroup.center SL2F5 := by
  ext A
  constructor
  · intro hA
    have hport : pslToPort (slToPsl A) = 1 := by
      simpa [slToPort] using hA
    have hq : slToPsl A = 1 := by
      apply pslToPort_injective
      simpa using hport
    have hmem : A ∈ slToPsl.ker := hq
    rw [slToPsl_ker_center] at hmem
    exact hmem
  · intro hA
    have hmem : A ∈ slToPsl.ker := by
      rw [slToPsl_ker_center]
      exact hA
    have hq : slToPsl A = 1 := hmem
    change pslToPort (slToPsl A) = 1
    rw [hq, map_one]

/-- The nontrivial scalar center element lies over the identity port
rotation. -/
@[simp]
theorem slToPort_neg_one : slToPort (-1) = 1 := by
  have h : (-1 : SL2F5) ∈ slToPort.ker := by
    rw [slToPort_ker]
    exact (center_mem_iff_plus_minus_one (-1)).2 (Or.inr rfl)
  exact h

/-- The cover square with `SL2F5 → PSL2F5` and `PSL2F5 ≃ PortGroup`
commutes on every element. -/
theorem cover_square (A : SL2F5) :
    slToPort A = pslEquivPortGroup (slToPsl A) :=
  rfl

end OPH.SL2F5PortCover

/- Axiom audit: no `sorry`, `admit`, new axioms, or `native_decide`. -/

#print axioms OPH.SL2F5PortCover.pslToPort_injective
#print axioms OPH.SL2F5PortCover.pslToPort_surjective
#print axioms OPH.SL2F5PortCover.slToPort_surjective
#print axioms OPH.SL2F5PortCover.slToPort_ker
#print axioms OPH.SL2F5PortCover.slToPort_neg_one
#print axioms OPH.SL2F5PortCover.cover_square

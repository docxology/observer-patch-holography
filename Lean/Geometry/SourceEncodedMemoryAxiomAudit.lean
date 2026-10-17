module
public import Mathlib.Util.AssertNoSorry
public import PortGramA5Isometry
public import Geometry.SourceEncodedMemory

@[expose] public section

/-! Every theorem is audited transitively, including proof dependencies. -/
open Lean Elab Command in
elab "audit_encoded_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter (fun ax => !permitted.contains ax)
  unless unexpected.isEmpty do
    throwError "Encoded memory axiom audit rejected {unexpected.toList}"
  logInfo m!"'{name}' depends on axioms: {axioms.toList}"

/-- error: Encoded memory axiom audit rejected [sorryAx] -/
#guard_msgs in
 audit_encoded_axioms sorryAx

-- The control inherits the native axiom of the reviewed rotation proof.
private alias nativeDecisionControl := OPH.PortGramA5Isometry.rotationQ_orthogonal

/-- error: Encoded memory axiom audit rejected [_private.PortGramA5Isometry.0.OPH.PortGramA5Isometry.rotationQ_orthogonal._native.native_decide.ax_1_1] -/
#guard_msgs in
 audit_encoded_axioms nativeDecisionControl

audit_encoded_axioms OPH.SourceEncodedMemory.run_append
audit_encoded_axioms OPH.SourceEncodedMemory.run_nonnegative
audit_encoded_axioms OPH.SourceEncodedMemory.copy_native
audit_encoded_axioms OPH.SourceEncodedMemory.clear_native
audit_encoded_axioms OPH.SourceEncodedMemory.encode_nonnegative
audit_encoded_axioms OPH.SourceEncodedMemory.encode_gap
audit_encoded_axioms OPH.SourceEncodedMemory.blank_copy_source
audit_encoded_axioms OPH.SourceEncodedMemory.blank_copy_target
audit_encoded_axioms OPH.SourceEncodedMemory.blank_copy_sign
audit_encoded_axioms OPH.SourceEncodedMemory.hop_signal
audit_encoded_axioms OPH.SourceEncodedMemory.read_signal
audit_encoded_axioms OPH.SourceEncodedMemory.reads_signal
audit_encoded_axioms OPH.SourceEncodedMemory.reads_length
audit_encoded_axioms OPH.SourceEncodedMemory.route_signal
audit_encoded_axioms OPH.SourceEncodedMemory.route_length
audit_encoded_axioms OPH.SourceEncodedMemory.attenuation_positive
audit_encoded_axioms OPH.SourceEncodedMemory.attenuation_preserves_sign
audit_encoded_axioms OPH.SourceEncodedMemory.near_trans
audit_encoded_axioms OPH.SourceEncodedMemory.pairAverage_near
audit_encoded_axioms OPH.SourceEncodedMemory.noisy_run_bound
audit_encoded_axioms OPH.SourceEncodedMemory.robust_positive_read
audit_encoded_axioms OPH.SourceEncodedMemory.robust_negative_read
audit_encoded_axioms OPH.SourceEncodedMemory.robust_route_positive
audit_encoded_axioms OPH.SourceEncodedMemory.ambiguous_at_margin
audit_encoded_axioms OPH.SourceEncodedMemory.analog_readout_error

module
public import Mathlib.Util.AssertNoSorry
public import PortGramA5Isometry
public import Geometry.SourceRoutingStorage
public import Geometry.SourceRoutingBudget
public import Geometry.SourceRoutingHierarchy

@[expose] public section

/-! Transitive axiom audit for every theorem in the M1 routing refinement.
Only the standard Lean axioms are allowed. Kernel `decide` is permitted;
compiler-trusted reductions and admitted propositions are rejected. -/

open Lean Elab Command in
elab "audit_routing_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter (fun ax => !permitted.contains ax)
  unless unexpected.isEmpty do
    throwError "Routing refinement axiom audit rejected {unexpected.toList}"
  logInfo m!"'{name}' depends on axioms: {axioms.toList}"

/-- error: Routing refinement axiom audit rejected [sorryAx] -/
#guard_msgs in
audit_routing_axioms sorryAx

-- The control inherits the native axiom of the reviewed rotation proof.
private alias nativeDecisionControl := OPH.PortGramA5Isometry.rotationQ_orthogonal

/-- error: Routing refinement axiom audit rejected [_private.PortGramA5Isometry.0.OPH.PortGramA5Isometry.rotationQ_orthogonal._native.native_decide.ax_1_1] -/
#guard_msgs in
audit_routing_axioms nativeDecisionControl

audit_routing_axioms OPH.SourceRoutingStorage.live_slot_injective
audit_routing_axioms OPH.SourceRoutingStorage.slot_owner
audit_routing_axioms OPH.SourceRoutingStorage.write_realizes
audit_routing_axioms OPH.SourceRoutingStorage.retire_realizes
audit_routing_axioms OPH.SourceRoutingStorage.carrier_slot_count
audit_routing_axioms OPH.SourceRoutingStorage.occupied_slot_bound
audit_routing_axioms OPH.SourceRoutingStorage.retired_payload_alias

audit_routing_axioms OPH.SourceRoutingBudget.readCount_lower
audit_routing_axioms OPH.SourceRoutingBudget.readCount_upper
audit_routing_axioms OPH.SourceRoutingBudget.hopCount_upper
audit_routing_axioms OPH.SourceRoutingBudget.eventCount_upper
audit_routing_axioms OPH.SourceRoutingBudget.three_times_logical_le_events
audit_routing_axioms OPH.SourceRoutingBudget.raw_mass_error_lower
audit_routing_axioms OPH.SourceRoutingBudget.serial_tick_bound

audit_routing_axioms OPH.SourceRoutingHierarchy.Walk.append
audit_routing_axioms OPH.SourceRoutingHierarchy.Within.trans
audit_routing_axioms OPH.SourceRoutingHierarchy.Within.mono
audit_routing_axioms OPH.SourceRoutingHierarchy.lift_walk
audit_routing_axioms OPH.SourceRoutingHierarchy.diameter_lift
audit_routing_axioms OPH.SourceRoutingHierarchy.envelope_closed
audit_routing_axioms OPH.SourceRoutingHierarchy.tower_diameter
audit_routing_axioms OPH.SourceRoutingHierarchy.children_share_vertex
audit_routing_axioms OPH.SourceRoutingHierarchy.old_vertex_retained
audit_routing_axioms OPH.SourceRoutingHierarchy.stencil_refinement
audit_routing_axioms OPH.SourceRoutingHierarchy.base_paths
audit_routing_axioms OPH.SourceRoutingHierarchy.base_diameter

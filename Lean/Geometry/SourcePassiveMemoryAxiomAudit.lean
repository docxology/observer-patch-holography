module
public import Mathlib.Util.AssertNoSorry
public import PortGramA5Isometry
public import Geometry.SourcePassiveMemoryBudget

@[expose] public section

/-! Transitive audit of every theorem in the passive-memory derivation. -/
open Lean Elab Command in
elab "audit_passive_axioms " n:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := axioms.filter (fun ax => !permitted.contains ax)
  unless unexpected.isEmpty do
    throwError "Passive memory axiom audit rejected {unexpected.toList}"
  logInfo m!"'{name}' depends on axioms: {axioms.toList}"

/-- error: Passive memory axiom audit rejected [sorryAx] -/
#guard_msgs in
audit_passive_axioms sorryAx

-- The control inherits the native axiom of the reviewed rotation proof.
private alias nativeDecisionControl := OPH.PortGramA5Isometry.rotationQ_orthogonal

/-- error: Passive memory axiom audit rejected [_private.PortGramA5Isometry.0.OPH.PortGramA5Isometry.rotationQ_orthogonal._native.native_decide.ax_1_1] -/
#guard_msgs in
audit_passive_axioms nativeDecisionControl

audit_passive_axioms OPH.SourceNonlinearRecord.nonnegative_single
audit_passive_axioms OPH.SourceNonlinearRecord.nonnegative_add
audit_passive_axioms OPH.SourceNonlinearRecord.nonnegative_sum
audit_passive_axioms OPH.SourceNonlinearRecord.pairAverage_single_same
audit_passive_axioms OPH.SourceNonlinearRecord.protected_move_addend
audit_passive_axioms OPH.SourceNonlinearRecord.protected_move_along_path
audit_passive_axioms OPH.SourceNonlinearRecord.concentrate_finite_sum
audit_passive_axioms OPH.SourceNonlinearRecord.protected_record_factors_total
audit_passive_axioms OPH.SourceNonlinearRecord.sum_pairAverage
audit_passive_axioms OPH.SourceNonlinearRecord.total_readout_protected
audit_passive_axioms OPH.SourceNonlinearRecord.same_total_same_protected_record
audit_passive_axioms OPH.SourcePassiveReset.run_append
audit_passive_axioms OPH.SourcePassiveReset.pairAverage_nonnegative
audit_passive_axioms OPH.SourcePassiveReset.run_nonnegative
audit_passive_axioms OPH.SourcePassiveReset.incident_lower_bound
audit_passive_axioms OPH.SourcePassiveReset.retained_self_lower_bound
audit_passive_axioms OPH.SourcePassiveReset.positive_register_cannot_reset
audit_passive_axioms OPH.SourcePassiveReset.reset_tolerance_requires
audit_passive_axioms OPH.SourcePassiveReset.coldState_zero
audit_passive_axioms OPH.SourcePassiveReset.coldState_step
audit_passive_axioms OPH.SourcePassiveReset.coldWord_exact
audit_passive_axioms OPH.SourcePassiveReset.coldWord_residual
audit_passive_axioms OPH.SourcePassiveReset.coldWord_length
audit_passive_axioms OPH.SourcePassiveReset.coldWord_support
audit_passive_axioms OPH.SourcePassiveReset.coldWord_next_zero
audit_passive_axioms OPH.SourcePassiveMemoryBudget.quadratic_nonnegative
audit_passive_axioms OPH.SourcePassiveMemoryBudget.pairAverage_quadratic_defect
audit_passive_axioms OPH.SourcePassiveMemoryBudget.loss_nonnegative
audit_passive_axioms OPH.SourcePassiveMemoryBudget.quadratic_ledger
audit_passive_axioms OPH.SourcePassiveMemoryBudget.quadratic_nonincreasing
audit_passive_axioms OPH.SourcePassiveMemoryBudget.quadratic_eq_iff_quiescent
audit_passive_axioms OPH.SourcePassiveMemoryBudget.closed_cycle_quiescent
audit_passive_axioms OPH.SourcePassiveMemoryBudget.quiescent_run
audit_passive_axioms OPH.SourcePassiveMemoryBudget.pairAverage_shift
audit_passive_axioms OPH.SourcePassiveMemoryBudget.run_shift
audit_passive_axioms OPH.SourcePassiveMemoryBudget.quadratic_beforeCopy
audit_passive_axioms OPH.SourcePassiveMemoryBudget.quadratic_afterCopy
audit_passive_axioms OPH.SourcePassiveMemoryBudget.copy_total_unchanged
audit_passive_axioms OPH.SourcePassiveMemoryBudget.copy_ancillary_budget
audit_passive_axioms OPH.SourcePassiveMemoryBudget.no_catalytic_balanced_copy

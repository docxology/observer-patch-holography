module
public import EventAlgebra.Robertson
public import EventAlgebra.Superselection
public import ExteriorComponentBridge
public import QuantumMatterIntegration
public import B10EdgeCenterAction

@[expose] public section

/-!
# B10 finite quantum limitation package

This root collects the supplied-state Robertson theorem, the exact
partition-operational quotient, the five-mode exterior component bridge, and
the typed component/sector/Z6 integration.  The partition-center action
module adds a commutative readout relative to the supplied partition and a
supplied-weight sixth-root character action on the component-labelled mapped
projector ranges, including the attached exterior-degree parity support and
exact kernel.  The individual modules state the required inputs and physical
boundaries.  Importing them together adds no edge identification,
source-selection, physical fermion-parity identification, or laboratory
premise.
-/

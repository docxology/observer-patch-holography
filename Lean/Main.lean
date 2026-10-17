module
public import ObserverPatchHolography
public import ObserverPatchHolography.BridgeEquivalence
public import ObserverPatchHolography.CapacityFixedPoint
public import ObserverPatchHolography.CapacityClosurePrinciple
public import ObserverPatchHolography.SeedPi
public import EventAlgebra

@[expose] public section

def main : IO Unit := do
  IO.println "ObserverPatchHolography Lean library loaded."
  IO.println "EventAlgebra library loaded (finite event algebras, sorry-free)."
  IO.println "See docs/PROOF_INDEX.md for current formalisation status."

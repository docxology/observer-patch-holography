# Fermionic hypercharge current on prepared golden sites

This package executes a declared finite CAR hopping factor on the 64-site,
144-link golden carrier. The registered five multiplets supply 15 internal
states with two Spin components. Each internal state occupies its own normalized
spatial/Spin orbital, so the coefficient arrays represent a 15-particle Slater
state. They do not replace fermion fields by commuting classical variables.

Run from the repository root:

```sh
python3 code/sm_fermion_current/build_current.py --write
python3 code/sm_fermion_current/verify_current.py
python3 -m pytest -q code/sm_fermion_current/test_current.py
```

Each local implicit-midpoint factor uses exact Gaussian rationals. Its
hypercharge current is the link-angle derivative of the same bilinear
Hamiltonian expectation. That midpoint current changes a classical electric
momentum, preserving discrete charge continuity and expectation Gauss. The
midpoint orbital covariance is a positive contraction; it does not represent
a normalized fifteen-particle Slater state at an intermediate physical time. The
charge unit is integer `6Y`; it is distinct from the scalar pilot's reduced
charge convention. The hopping coefficient and duration are supplied, and
the scalar pilot's mass and conductance weights are not reused.

The baseline, phase intervention and gauge-copy histories retain actual
register reads, writers, versions and writes. Public checkpoint currents use
the checkpoint state. The `factor_current` registers instead contain each
edge factor's midpoint current. Bounded self-reading software patches are
represented by local state, link ports, retained readback, records and electric
feedback; the receipt is their public execution evidence.

The electric field is classical. Initial local charge expectation vanishes,
while its quantum variance is `945/512` in squared integer-charge units.
The state therefore does not satisfy the operator Gauss constraint with the
declared electric values. Non-Abelian evolution, Yukawa interactions,
gauge-electric/plaquette factors, continuum chirality and regulator anomaly
cancellation are outside this factor. The anomaly sums classify the retained
representation census. Exact discrete conservation supplies neither a
continuous-time error bound nor source selection, physical units or a
laboratory measurement.

## Quantized electric link

A separate localized preparation occupies one left-end spin orbital in each
of the 15 internal channels on the first golden-family edge. The electric
link has the infinite integer basis, and a rightward charge transfer shifts
its electric value by the negative transferred charge. Every branch of the
resulting entangled fermion/link state satisfies the operator hypercharge
Gauss constraint. Nonabelian quantum Gauss constraints are not imposed.
This construction has different initial data from the uniform semiclassical
history above.

```sh
python3 code/sm_fermion_current/build_quantum_link.py --write
python3 code/sm_fermion_current/verify_quantum_link.py
python3 -m pytest -q code/sm_fermion_current/test_quantum_link.py
```

The compact receipt retains all 15 exact Cayley factors, the full flux
distribution after every factor, and a digest of all 32,768 final branches.
The electric basis has no cyclic wrap or artificial cutoff. Its populated
support is the 37 integers from -18 to 18. The current integrated over the
discrete factors is the negative electric change; the final instantaneous
current is a separate observable. Only one link and its invariant spin modes
evolve. The commuting channel Hamiltonians also have an exact continuous
solution with cosine/sine channel amplitudes. At model time `pi/6`, mean
electric flux is `-3`, current is `3*sqrt(3)`, and electric variance is `45/2`.
This continuous solution and the rational Cayley word are distinct histories.
The action, quantum preparation, electric quantization and schedule
are supplied; this finite construction supplies no continuum error estimate,
non-Abelian or Yukawa evolution, physical clock or laboratory current.

## Lean 4.35 source-custody migration

The registered parent Lean source identities now select the strictly compiled
4.35 source snapshot. The original 4.29 sources and receipt remain immutable in
Git history at `bfa6c44d5347f113a5418d2a25d836f1057993a2`.
`lean435_migration.json` records the exact old/new source and parent-receipt
identities. Regeneration must preserve the entire original mathematical payload
when the source-pin map is excluded, and independent exact replay and mutation
controls must still pass. No arbitrary source identity is accepted, no historical
prediction registration is rewritten, and no scientific scope is promoted.

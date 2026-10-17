module
public import QFT.LocallyCovariantLimit
public import ObserverPatchHolography.Provenance.RefinementNaturality

@[expose] public section

/-!
# Restriction naturality on authenticated finite event logs

Restriction and algebra refinement commute when regional restriction agrees
with the existing natural repair map.  That agreement is an explicit extra
hypothesis; repair naturality alone does not identify the two operations.

An algebra decoration of a semantic log checks region inclusion on actual
authenticated direct-parent edges.  Transitive closure then supplies a
contravariant restriction system, including identity and composition.  A
certified log map and a compatible region decoration join this restriction
system to the algebra-refinement naturality square.

The inhabitant uses the committed support-graded diagonal net and the
authenticated Boolean diamond to three-event chain coarsening.  Its root
algebra is scalar and its other algebras are full diagonal; restriction
changes a diagonal projector.  The algebra regulator is constant, although
the event coarsening merges two distinct responses.  Algebra decorations
and the edge certificate are supplied finite data, not selected physical
regions.  No normed limit restriction, nonconstant physical refinement,
CP extension, spacetime interpretation, or physical time-slice follows.
-/

namespace OPH.QFT

open OPH.Tower OPH.Provenance

universe u v w z

variable {ι : Type u} [Preorder ι] {T : ConsensusTower ι}

/-- The missing square, stated in the common refined regional algebra. -/
def RestrictionNaturality (N : FiniteCausalObserverNet T) : Prop :=
  ∀ {r s : ι} (hrs : r ≤ s) {U V : N.Region r}
    (hVU : N.regionLE r V U) (X : N.localAlgebra r U),
    N.localRefine hrs V (N.restrict r hVU X) =
      N.restrict s (N.region_refine_mono hrs hVU) (N.localRefine hrs U X)

/-- Restriction agrees with regional repair on the larger regional algebra.
This is not a field of `FiniteCausalObserverNet`. -/
def RestrictionRepairCompatible (N : FiniteCausalObserverNet T) : Prop :=
  ∀ (r : ι) {U V : N.Region r} (hVU : N.regionLE r V U)
    (X : N.localAlgebra r U),
    (N.restrict r hVU X : ConsensusTower.PrivateAlgebra T r) =
      N.repair r V X

/-- Natural repair supplies the restriction square under the named agreement. -/
theorem restriction_naturality_of_repair (N : FiniteCausalObserverNet T)
    (h : RestrictionRepairCompatible N) : RestrictionNaturality N := by
  intro r s hrs U V hVU X
  apply Subtype.ext
  change T.algebraRefine hrs (N.restrict r hVU X : _) =
    (N.restrict s (N.region_refine_mono hrs hVU) (N.localRefine hrs U X) : _)
  rw [h r hVU X, h s (N.region_refine_mono hrs hVU) (N.localRefine hrs U X)]
  exact N.repair_natural hrs V X

variable {Register : Type v} {Value : Type w} {EventId : Type z}
variable [DecidableEq Register]

/-- Declared algebras on events; monotonicity is checked on authenticated
read-after-write edges, not inferred from a serial event index. -/
structure SourceRegionDecoration (N : FiniteCausalObserverNet T) (r : ι)
    (L : SemanticEventLog Register Value EventId) where
  region : EventId → N.Region r
  edge_mono : ∀ {e f}, L.ParentEdge e f → N.regionLE r (region e) (region f)

namespace SourceRegionDecoration

variable {N : FiniteCausalObserverNet T} {r : ι}
variable {L : SemanticEventLog Register Value EventId}

/-- Generated informational precedence implies inclusion of decorated regions. -/
theorem generated_mono (A : SourceRegionDecoration N r L) {e f : EventId}
    (h : L.GeneratedBeforeEq e f) : N.regionLE r (A.region e) (A.region f) := by
  rcases h with rfl | h
  · exact N.regionLE_refl r _
  · induction h with
    | single h => exact A.edge_mono h
    | tail _ h ih => exact N.regionLE_trans r ih (A.edge_mono h)

/-- A later event's observable restricts to an informational ancestor. -/
noncomputable def restrict (A : SourceRegionDecoration N r L) {e f : EventId}
    (h : L.GeneratedBeforeEq e f) :
    N.localAlgebra r (A.region f) →⋆ₐ[ℂ] N.localAlgebra r (A.region e) :=
  N.restrict r (A.generated_mono h)

/-- Identity for the contravariant event restriction. -/
theorem restrict_id (A : SourceRegionDecoration N r L) (e : EventId)
    (X : N.localAlgebra r (A.region e)) :
    A.restrict (Or.inl rfl : L.GeneratedBeforeEq e e) X = X :=
  N.restrict_refl r _ X

/-- Composition follows generated precedence and reverses the observable maps. -/
theorem restrict_comp (A : SourceRegionDecoration N r L) {e f g : EventId}
    (hef : L.GeneratedBeforeEq e f) (hfg : L.GeneratedBeforeEq f g)
    (X : N.localAlgebra r (A.region g)) :
    A.restrict hef (A.restrict hfg X) =
      A.restrict (L.generatedBeforeEq_trans hef hfg) X :=
  N.restrict_trans r (A.generated_mono hfg) (A.generated_mono hef) X

end SourceRegionDecoration

/-- The same square on generated event ancestry.  The target region
decoration must agree with the declared algebra refinement; the semantic
log map separately certifies that these target events are ordered. -/
theorem source_restriction_square
    (N : FiniteCausalObserverNet T) (hc : RestrictionRepairCompatible N)
    {r s : ι} (hrs : r ≤ s)
    {Rf Rc Vf Vc Ef Ec : Type} [DecidableEq Rf] [DecidableEq Rc]
    {Lf : SemanticEventLog Rf Vf Ef} {Lc : SemanticEventLog Rc Vc Ec}
    (F : SourceRegionDecoration N r Lf) (C : SourceRegionDecoration N s Lc)
    (R : LogRefinement Lf Lc)
    (hregion : ∀ e, C.region (R.map e) = N.regionRefine hrs (F.region e))
    {e f : Ef} (hef : Lf.GeneratedBeforeEq e f)
    (X : N.localAlgebra r (F.region f)) :
    let Xc : N.localAlgebra s (C.region (R.map f)) :=
      ⟨T.algebraRefine hrs X, by
        rw [hregion f]
        exact N.localAlgebra_natural hrs (F.region f) X X.property⟩
    Lc.GeneratedBeforeEq (R.map e) (R.map f) ∧
      (N.localRefine hrs (F.region e) (F.restrict hef X) :
        ConsensusTower.PrivateAlgebra T s) =
      (C.restrict (R.generatedBeforeEq_maps_under_edge_certificate hef) Xc :
        ConsensusTower.PrivateAlgebra T s) := by
  dsimp only
  refine ⟨R.generatedBeforeEq_maps_under_edge_certificate hef, ?_⟩
  change T.algebraRefine hrs (N.restrict r (F.generated_mono hef) X : _) =
    (N.restrict s (C.generated_mono
      (R.generatedBeforeEq_maps_under_edge_certificate hef)) _ : _)
  rw [hc r, hc s, hregion e]
  exact N.repair_natural hrs (F.region e) X

/-! ## A nontrivial restriction on a genuine authenticated coarsening -/

theorem support_restriction_repair_compatible :
    RestrictionRepairCompatible supportGradedNet := by
  intro r U V hVU X
  rfl

theorem support_restriction_natural : RestrictionNaturality supportGradedNet :=
  restriction_naturality_of_repair _ support_restriction_repair_compatible

/-- Root scalar algebra; every response and answer has the full diagonal one. -/
def diamondRegion (e : Fin 4) : Finset (Fin 2) :=
  if e = 0 then ∅ else Finset.univ

def chainRegion (e : Fin 3) : Finset (Fin 2) :=
  if e = 0 then ∅ else Finset.univ

def diamondDecoration : SourceRegionDecoration supportGradedNet () BooleanDiamond.log where
  region := diamondRegion
  edge_mono := by
    have h : ∀ e f : Fin 4, BooleanDiamond.log.ParentEdge e f →
        diamondRegion e ⊆ diamondRegion f := by decide
    exact fun {e f} hedge => h e f hedge

def chainDecoration : SourceRegionDecoration supportGradedNet ()
    DiamondChainRefinement.chainLog3 where
  region := chainRegion
  edge_mono := by
    have h : ∀ e f : Fin 3, DiamondChainRefinement.chainLog3.ParentEdge e f →
        chainRegion e ⊆ chainRegion f := by decide
    exact fun {e f} hedge => h e f hedge

theorem coarsening_regions_agree (e : Fin 4) :
    chainDecoration.region (DiamondChainRefinement.refinement.map e) =
      supportGradedNet.regionRefine (show () ≤ () from le_rfl)
        (diamondDecoration.region e) := by
  change chainRegion (DiamondChainRefinement.diamondToChain e) = diamondRegion e
  fin_cases e <;> rfl

/-- The identity algebra bonding map, with its target region checked against
the actual event coarsening. -/
noncomputable def coarsenObservable (e : Fin 4)
    (X : supportGradedNet.localAlgebra () (diamondDecoration.region e)) :
    supportGradedNet.localAlgebra ()
      (chainDecoration.region (DiamondChainRefinement.refinement.map e)) :=
  ⟨X, by rw [coarsening_regions_agree]; exact X.property⟩

/-- The inhabited square: restriction after authenticated coarsening equals
coarsening after restriction, at the level of the same private matrices. -/
theorem coarsening_restriction_square {e f : Fin 4}
    (hef : BooleanDiamond.log.GeneratedBeforeEq e f)
    (X : supportGradedNet.localAlgebra () (diamondDecoration.region f)) :
    (diamondDecoration.restrict hef X).val =
      (chainDecoration.restrict
        (DiamondChainRefinement.refinement.generatedBeforeEq_maps_under_edge_certificate hef)
        (coarsenObservable f X)).val := by
  exact (source_restriction_square supportGradedNet
    support_restriction_repair_compatible (show () ≤ () from le_rfl)
    diamondDecoration chainDecoration DiamondChainRefinement.refinement
    coarsening_regions_agree hef X).2

/-- The source map really merges distinct authenticated responses. -/
theorem coarsening_not_injective :
    ¬ Function.Injective DiamondChainRefinement.refinement.map := by
  intro h
  have he : (1 : Fin 4) = 2 := h (show
    DiamondChainRefinement.refinement.map 1 =
      DiamondChainRefinement.refinement.map 2 from rfl)
  exact (by decide : (1 : Fin 4) ≠ 2) he

/-- Restriction is not an identity map disguised by event labels. -/
theorem root_restriction_changes_projector :
    supportCompress (diamondRegion 0) e0 ≠ e0 := by
  intro h
  have hm := supportCompress_mem (diamondRegion 0) e0
  rw [h] at hm
  exact e0_not_mem_empty hm

/-! The independent reversed-map control is the imported theorem
`DiamondChainRefinement.reversed_map_not_natural`: algebra decorations do
not license reversing an authenticated edge. -/

#print axioms restriction_naturality_of_repair
#print axioms SourceRegionDecoration.generated_mono
#print axioms SourceRegionDecoration.restrict_id
#print axioms SourceRegionDecoration.restrict_comp
#print axioms source_restriction_square
#print axioms support_restriction_natural
#print axioms coarsening_restriction_square
#print axioms coarsening_not_injective
#print axioms root_restriction_changes_projector

end OPH.QFT

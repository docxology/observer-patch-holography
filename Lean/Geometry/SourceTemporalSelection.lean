module
public import Geometry.SourceTemporalObservation
public import Geometry.SourceConstrainedSelection
public import Geometry.SourceTemporalMenu
public import Geometry.SourceTemporalConnected

@[expose] public section

/-!
# Exact temporal grammar for a constrained classical information projection

In the scored full-history branch, certainty of linear publication is
equivalent to observability on every history admitted by any feasible law.
The grammar is obtained from response kernels. An attained information
projection cannot delete an admitted ambiguity. The finite linear grammar
does not establish completeness for the full A1--A3 architecture.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalSelection
noncomputable section
open OPH.SourceTemporalObservation OPH.SourceConstrainedSelection

variable {V I W : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [Fintype W]

def Certain (L : W → I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) (p : W → ℝ) : Prop :=
  ∀ w, 0 < p w → Observable (L w) f

omit [Fintype I] in
/-- Exact necessity and sufficiency, strengthening a crossing-only test.
All weights, references and feasible constraints are explicit inputs. -/
theorem selected_certain_iff [_instFintypeI : Fintype I] (K : Set (W → ℝ)) (hK : Convex ℝ K)
    (hn : ∀ p ∈ K, ∀ w, 0 ≤ p w) (weight reference selected : W → ℝ)
    (hw : ∀ w, 0 < weight w) (hr : ∀ w, 0 < reference w) (hp : selected ∈ K)
    (hm : ∀ q ∈ K, weightedKL weight reference selected ≤ weightedKL weight reference q)
    (L : W → I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) :
    Certain L f selected ↔ ∀ q ∈ K, Certain L f q := by
  constructor
  · intro h q hq w hqw
    exact h w (weightedKL_minimizer_support K hK hn weight reference selected hw hr hp hm
      q hq w hqw)
  · intro h
    exact h selected hp

/-- Intersection of the response spans is the complete space of linear
meanings readable with certainty on the admitted history support. -/
theorem selected_certain_iff_spans (K : Set (W → ℝ)) (hK : Convex ℝ K)
    (hn : ∀ p ∈ K, ∀ w, 0 ≤ p w) (weight reference selected : W → ℝ)
    (hw : ∀ w, 0 < weight w) (hr : ∀ w, 0 < reference w) (hp : selected ∈ K)
    (hm : ∀ q ∈ K, weightedKL weight reference selected ≤ weightedKL weight reference q)
    (L : W → I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) :
    Certain L f selected ↔
      ∀ q ∈ K, ∀ w, 0 < q w → f ∈ Submodule.span ℝ (Set.range (L w)) := by
  rw [selected_certain_iff K hK hn weight reference selected hw hr hp hm L f]
  simp only [Certain, observable_iff_span]

/-- One omitted temporal constraint has a dual ambiguity witness. A changed
reference with the same faithful support cannot repair this omission. -/
theorem feasible_ambiguity_survives (K : Set (W → ℝ)) (hK : Convex ℝ K)
    (hn : ∀ p ∈ K, ∀ w, 0 ≤ p w) (weight reference selected : W → ℝ)
    (hw : ∀ w, 0 < weight w) (hr : ∀ w, 0 < reference w) (hp : selected ∈ K)
    (hm : ∀ q ∈ K, weightedKL weight reference selected ≤ weightedKL weight reference q)
    (L : W → I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ)
    (q : W → ℝ) (hq : q ∈ K) (w : W) (hqw : 0 < q w)
    (hz : ¬ Observable (L w) f) :
    0 < selected w ∧ ∃ z, (∀ i, L w i z = 0) ∧ f z ≠ 0 :=
  ⟨weightedKL_minimizer_support K hK hn weight reference selected hw hr hp hm q hq w hqw,
    invisible_witness (L w) f hz⟩

/-- For a specified affine meaning and direct record interface, the selected
law produces its required reads exactly when every feasible law enforces
their inclusion. This derives the temporal menu constraint from meanings,
without inserting an expected value or a preferred serial schedule. -/
theorem selected_direct_reads_iff {N : Type*} [Fintype N] [DecidableEq N]
    (K : Set (W → ℝ)) (hK : Convex ℝ K)
    (hn : ∀ p ∈ K, ∀ w, 0 ≤ p w) (weight reference selected : W → ℝ)
    (hw : ∀ w, 0 < weight w) (hr : ∀ w, 0 < reference w) (hp : selected ∈ K)
    (hm : ∀ q ∈ K, weightedKL weight reference selected ≤ weightedKL weight reference q)
    (reads : W → Finset N) (coefficients : N → ℝ) :
    (∀ w, 0 < selected w → Observable (SourceTemporalMenu.direct (reads w))
      (SourceTemporalMenu.meaning coefficients)) ↔
    ∀ q ∈ K, ∀ w, 0 < q w → ∀ j, coefficients j ≠ 0 → j ∈ reads w := by
  constructor
  · intro h q hq w hqw
    apply (SourceTemporalMenu.direct_observable_iff (reads w) coefficients).mp
    exact h w (weightedKL_minimizer_support K hK hn weight reference selected hw hr hp hm
      q hq w hqw)
  · intro h w hpw
    exact (SourceTemporalMenu.direct_observable_iff (reads w) coefficients).mpr (h selected hp w hpw)

/-- Connected source topology constructs the same completion protocol for
every prefix state. Under the stated KL problem, it recovers a meaning with
certainty exactly when no feasible history has erased it. The
constraint is a source joint-span test, not a successful-word oracle. -/
theorem selected_native_completion_iff {P : Type*} [Fintype P] [DecidableEq P]
    (G : SimpleGraph P) (connected : G.Connected) (root : P)
    (K : Set (W → ℝ)) (hK : Convex ℝ K)
    (hn : ∀ p ∈ K, ∀ w, 0 ≤ p w) (weight reference selected : W → ℝ)
    (hw : ∀ w, 0 < weight w) (hr : ∀ w, 0 < reference w) (hp : selected ∈ K)
    (hm : ∀ q ∈ K, weightedKL weight reference selected ≤ weightedKL weight reference q)
    (L : W → I → V →ₗ[ℝ] ℝ) (state : W → V →ₗ[ℝ] (P → ℝ)) (f : V →ₗ[ℝ] ℝ) :
    ∃ plan : SourceTemporalTomography.Plan root {root},
      SourceTemporalConnected.Supported G (SourceTemporalTomography.lower plan) ∧
      ((∀ w, 0 < selected w → ∀ x y, (∀ i, L w i x = L w i y) →
          SourceTemporalTomography.completionSamples plan (state w x) =
          SourceTemporalTomography.completionSamples plan (state w y) → f x = f y) ↔
       ∀ q ∈ K, ∀ w, 0 < q w →
         f ∈ Submodule.span ℝ (Set.range (SourceTemporalTomography.joint (L w) (state w)))) := by
  obtain ⟨plan,hs,_⟩ := SourceTemporalConnected.connected_native_completion G connected root
  refine ⟨plan,hs,?_⟩
  have hlocal : ∀ w, (∀ x y, (∀ i, L w i x = L w i y) →
      SourceTemporalTomography.completionSamples plan (state w x) =
      SourceTemporalTomography.completionSamples plan (state w y) → f x = f y) ↔
      Observable (SourceTemporalTomography.joint (L w) (state w)) f := by
    intro w
    rw [SourceTemporalTomography.completion_iff_joint_span,observable_iff_span]
  simp only [hlocal]
  exact selected_certain_iff_spans K hK hn weight reference selected hw hr hp hm
    (fun w => SourceTemporalTomography.joint (L w) (state w)) f

end
end OPH.SourceTemporalSelection

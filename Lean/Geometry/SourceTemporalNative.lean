module
public import Geometry.SourceTemporalObservation

@[expose] public section

/-!
# Temporal observation forms of the scalar seam dynamics

Every response form is composed from the actual pair-mean word, a declared
linear preparation and local coordinate readouts. No target value or desired
decoder enters this construction. A prefix retains its sampled observations.
Physical sampling, precision and the history law are separate inputs.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalNative
noncomputable section
open OPH.SourceTemporalObservation OPH.SourceReadAcceptance OPH.SourceEncodedMemory
open ObserverPatchHolography.ScalarSeamRepair

variable {V P R : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq P]
  [Fintype R]

def wordMap : List (P × P) → (P → ℝ) →ₗ[ℝ] (P → ℝ)
  | [] => LinearMap.id
  | e::es => (wordMap es).comp (pairAverage e.1 e.2)

theorem wordMap_run (es : List (P × P)) (x : P → ℝ) : wordMap es x = run es x := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih => exact ih _

theorem wordMap_baseline (es : List (P × P)) (b : ℝ) :
    wordMap es (fun _ => b) = (fun _ => b) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hm : pairAverage e.1 e.2 (fun _ => b) = (fun _ => b) := by
      ext p
      simp [pairAverage]
    simpa only [wordMap,LinearMap.comp_apply,hm] using ih

theorem wordMap_shift (es : List (P × P)) (b : ℝ) (x : P → ℝ) :
    wordMap es (fun p => b+x p) = fun p => b+wordMap es x p := by
  have h := (wordMap es).map_add (fun _ => b) x
  rw [wordMap_baseline] at h
  exact h

/-- `horizon` counts sample slots, starting with the initial state at slot
zero. Observations through H executed means therefore use H+1 slots. -/
def responses (prep : V →ₗ[ℝ] (P → ℝ)) (es : List (P × P))
    (read : R → P) (horizon : ℕ) : (Fin horizon × R) → V →ₗ[ℝ] ℝ :=
  fun slot => (LinearMap.proj (read slot.2)).comp
    ((wordMap (es.take slot.1.val)).comp prep)

omit [Fintype R] in
theorem responses_run [_instFintypeR : Fintype R] (prep : V →ₗ[ℝ] (P → ℝ)) (es : List (P × P))
    (read : R → P) (horizon : ℕ) (slot : Fin horizon × R) (x : V) :
    responses prep es read horizon slot x = run (es.take slot.1.val) (prep x) (read slot.2) := by
  simp [responses, wordMap_run]

/-- Kernel reduction and linear span are an exact criterion for every real
linear record, including records outside any enumerated candidate menu. -/
theorem native_acceptance_iff (prep : V →ₗ[ℝ] (P → ℝ)) (es : List (P × P))
    (read : R → P) (horizon : ℕ) (f : V →ₗ[ℝ] ℝ) (x : V) :
    canonical (Possible (responses prep es read horizon) f)
      (fun slot => run (es.take slot.1.val) (prep x) (read slot.2)) = some (f x) ↔
        f ∈ Submodule.span ℝ (Set.range (responses prep es read horizon)) := by
  simpa only [← responses_run] using
    canonical_publication_iff (responses prep es read horizon) f x

theorem prefix_observability (prep : V →ₗ[ℝ] (P → ℝ)) (es : List (P × P))
    (read : R → P) (h k : ℕ) (hle : h ≤ k) (f : V →ₗ[ℝ] ℝ)
    (ho : Observable (responses prep es read h) f) :
    Observable (responses prep es read k) f := by
  exact observable_extension _ _ (fun slot : Fin h × R => (Fin.castLE hle slot.1,slot.2))
    (fun _ => rfl) f ho

/-- The earliest observable prefix is selected from source response forms,
independently of the realized payload. No future sample enters its decoder. -/
def firstRead (prep : V →ₗ[ℝ] (P → ℝ)) (es : List (P × P))
    (read : R → P) (f : V →ₗ[ℝ] ℝ) (h : ∃ k, Observable (responses prep es read k) f) : ℕ := by
  classical
  exact Nat.find h

omit [Fintype R] in
theorem firstRead_correct [_instFintypeR : Fintype R] (prep : V →ₗ[ℝ] (P → ℝ)) (es : List (P × P))
    (read : R → P) (f : V →ₗ[ℝ] ℝ) (h : ∃ k, Observable (responses prep es read k) f) :
    Observable (responses prep es read (firstRead prep es read f h)) f := by
  classical
  exact Nat.find_spec h

theorem before_firstRead_abstains (prep : V →ₗ[ℝ] (P → ℝ)) (es : List (P × P))
    (read : R → P) (f : V →ₗ[ℝ] ℝ) (h : ∃ k, Observable (responses prep es read k) f)
    (k : ℕ) (hk : k < firstRead prep es read f h) (x : V)
    (publish : (Fin k × R → ℝ) → Option ℝ)
    (hs : Sound (Possible (responses prep es read k) f) publish) :
    publish (fun slot => responses prep es read k slot x) = none := by
  classical
  exact nonobservable_abstains _ _ publish hs (Nat.find_min h hk) x

end
end OPH.SourceTemporalNative

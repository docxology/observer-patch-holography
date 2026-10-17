module
public import ObserverPatchHolography.RepairWordSchedule
public import Geometry.SourceEncodedMemory

@[expose] public section

/-!
# Finite-word selection and remote-read obstruction

The finite KL schedule theorem supplies full support only under its explicit
complete-alphabet, full-simplex and counting-reference premises. This module
connects that selected distribution to the actual scalar transition action.
It does not instantiate all A1--A3 clauses or exclude accepted stopping-time
protocols, constrained schedules, side channels or probabilistic delivery.
-/

set_option autoImplicit false

namespace OPH.SourceReadSelection
noncomputable section
open ObserverPatchHolography.RepairWordSchedule
open ObserverPatchHolography.ScalarSeamRepair OPH.SourceEncodedMemory
open ProbabilityTheory
open scoped ENNReal

variable {Move : Type*}

/-- A full-support word law almost surely enforces a predicate exactly when
every word satisfies it. In a finite discrete space, no positive atom can be
discarded as a null history. -/
theorem full_support_criterion {W : Type*} (p : PMF W)
    (hp : ∀ w, 0 < p w) (P : W → Prop) :
    (∀ w, p w ≠ 0 → P w) ↔ ∀ w, P w := by
  constructor
  · intro h w
    exact h w (ne_of_gt (hp w))
  · intro h w _
    exact h w

theorem selected_support_criterion [Fintype Move] [Nonempty Move] (k : ℕ)
    (selection : FullWordKLProjection Move k) (P : Word Move k → Prop) :
    (∀ w, selection.selected w ≠ 0 → P w) ↔ ∀ w, P w :=
  full_support_criterion selection.selected
    (selected_full_support Move k selection) P

/-- Lift words over a subalphabet into the original alphabet. -/
def liftWord (s : Finset Move) {k : ℕ}
    (w : Fin k → {m // m ∈ s}) : Word Move k := fun i => (w i).val

theorem liftWord_injective (s : Finset Move) (k : ℕ) :
    Function.Injective (@liftWord Move s k) := by
  intro w v h
  funext i
  apply Subtype.ext
  exact congrFun h i

theorem liftWord_range (s : Finset Move) (k : ℕ) (w : Word Move k) :
    (∃ v : Fin k → {m // m ∈ s}, liftWord s v = w) ↔ ∀ i, w i ∈ s := by
  constructor
  · rintro ⟨v, rfl⟩ i
    exact (v i).property
  · intro h
    exact ⟨fun i => ⟨w i, h i⟩, rfl⟩

/-- Exact mass of all distinct words whose letters lie in `s`. The preceding
injection and range theorem certify that the sum neither duplicates nor
omits histories. This includes k=0 and the empty subalphabet. -/
theorem selected_subalphabet_mass [Fintype Move] [Nonempty Move]
    (s : Finset Move) (k : ℕ)
    (selection : FullWordKLProjection Move k) :
    (∑ w : Fin k → {m // m ∈ s}, selection.selected (liftWord s w)) =
      (s.card : ℝ≥0∞)^k / (Fintype.card Move : ℝ≥0∞)^k := by
  simp_rw [selected_eq_uniformWord, uniformWord_apply]
  simp [div_eq_mul_inv]

/-- If every history in an event fails on at least one of two interventions,
the event mass is bounded by the sum of their error probabilities. Dividing
by two gives the error lower bound for an independent balanced input bit. -/
theorem two_input_error_bound {W : Type*} [Fintype W]
    (p : W → ℝ≥0∞) (bad ok₀ ok₁ : W → Prop)
    [DecidablePred bad] [DecidablePred ok₀] [DecidablePred ok₁]
    (h : ∀ w, bad w → ¬ (ok₀ w ∧ ok₁ w)) :
    (∑ w, if bad w then p w else 0) ≤
      (∑ w, if ok₀ w then 0 else p w) +
      (∑ w, if ok₁ w then 0 else p w) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  by_cases hb : bad w
  · have hn := h w hb
    by_cases h₀ : ok₀ w <;> by_cases h₁ : ok₁ w
    · exact (hn ⟨h₀, h₁⟩).elim
    all_goals simp [hb, h₀, h₁]
  · simp [hb]

variable {ι : Type*} [DecidableEq ι]

/-- A move does not cross the cut separating a source region from its exterior. -/
def NoCross (source : ι → Prop) (e : ι × ι) : Prop :=
  source e.1 ↔ source e.2

theorem mean_outside_eq (source : ι → Prop) (e : ι × ι)
    (he : NoCross source e) (x y : ι → ℝ)
    (hxy : ∀ i, ¬ source i → x i = y i) :
    ∀ i, ¬ source i → pairAverage e.1 e.2 x i = pairAverage e.1 e.2 y i := by
  intro i hi
  by_cases h : i = e.1 ∨ i = e.2
  · have hu : ¬ source e.1 := by
      rcases h with rfl | rfl
      · exact hi
      · exact fun hs => hi (he.mp hs)
    have hv : ¬ source e.2 := fun hs => hu (he.mpr hs)
    simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left h]
    rw [hxy e.1 hu, hxy e.2 hv]
  · simpa [pairAverage, h] using hxy i hi

/-- All exterior values remain intervention-indistinguishable for every word
that avoids the cut, even when interior and exterior repairs both occur. -/
theorem run_outside_eq (source : ι → Prop) (es : List (ι × ι))
    (hes : ∀ e ∈ es, NoCross source e) (x y : ι → ℝ)
    (hxy : ∀ i, ¬ source i → x i = y i) :
    ∀ i, ¬ source i → run es x i = run es y i := by
  induction es generalizing x y with
  | nil => exact hxy
  | cons e es ih =>
    exact ih (fun f hf => hes f (List.mem_cons_of_mem e hf)) _ _
      (mean_outside_eq source e (hes e (by simp)) x y hxy)

/-- Any fixed local read interface, including several rails, sees identical
data across the two source interventions when the word avoids the cut. -/
theorem local_read_eq {R : Type*} (source : ι → Prop)
    (readPort : R → ι) (hr : ∀ r, ¬ source (readPort r))
    (es : List (ι × ι)) (hes : ∀ e ∈ es, NoCross source e)
    (x y : ι → ℝ) (hxy : ∀ i, ¬ source i → x i = y i) :
    (fun r => run es x (readPort r)) = (fun r => run es y (readPort r)) := by
  funext r
  exact run_outside_eq source es hes x y hxy (readPort r) (hr r)

/-- Readouts of every prefix, including the initial state. For n beyond the
deadline, `take n` repeats the final state; it supplies no future samples. -/
def transcript {R : Type*} (es : List (ι × ι)) (x : ι → ℝ)
    (readPort : R → ι) : ℕ → R → ℝ :=
  fun n r => run (es.take n) x (readPort r)

theorem local_transcript_eq {R : Type*} (source : ι → Prop)
    (readPort : R → ι) (hr : ∀ r, ¬ source (readPort r))
    (es : List (ι × ι)) (hes : ∀ e ∈ es, NoCross source e)
    (x y : ι → ℝ) (hxy : ∀ i, ¬ source i → x i = y i) :
    transcript es x readPort = transcript es y readPort := by
  funext n r
  apply run_outside_eq source (es.take n) _ x y hxy (readPort r) (hr r)
  intro e he
  exact hes e (List.mem_of_mem_take he)

/-- Even a decoder told the entire word cannot reconstruct two distinct
payloads from identical local data. Word and metadata are held fixed under
the source intervention; payload-dependent scheduling is an additional
communication channel, not covered by this statement. -/
theorem cut_word_not_both_correct {R Value : Type*}
    (source : ι → Prop) (readPort : R → ι)
    (hr : ∀ r, ¬ source (readPort r))
    (es : List (ι × ι)) (hes : ∀ e ∈ es, NoCross source e)
    (x y : ι → ℝ) (hxy : ∀ i, ¬ source i → x i = y i)
    (decode : (R → ℝ) → Value) (a b : Value) (hab : a ≠ b) :
    ¬ (decode (fun r => run es x (readPort r)) = a ∧
       decode (fun r => run es y (readPort r)) = b) := by
  rw [local_read_eq source readPort hr es hes x y hxy]
  rintro ⟨ha, hb⟩
  exact hab (ha.symm.trans hb)

/-- Keeping every exterior sample cannot recover information that never
crossed the cut. Private randomness may be fixed and coupled identically
across interventions; it cannot remove this indistinguishability. -/
theorem cut_transcript_not_both_correct {R Value : Type*}
    (source : ι → Prop) (readPort : R → ι)
    (hr : ∀ r, ¬ source (readPort r))
    (es : List (ι × ι)) (hes : ∀ e ∈ es, NoCross source e)
    (x y : ι → ℝ) (hxy : ∀ i, ¬ source i → x i = y i)
    (decode : (ℕ → R → ℝ) → Value) (a b : Value) (hab : a ≠ b) :
    ¬ (decode (transcript es x readPort) = a ∧
       decode (transcript es y readPort) = b) := by
  rw [local_transcript_eq source readPort hr es hes x y hxy]
  rintro ⟨ha, hb⟩
  exact hab (ha.symm.trans hb)

/-- Any history accepted as correct for both interventions must have crossed
the source cut. This necessary condition does not itself certify transport. -/
theorem correct_pair_requires_crossing {R Value : Type*}
    (source : ι → Prop) (readPort : R → ι)
    (hr : ∀ r, ¬ source (readPort r)) (es : List (ι × ι))
    (x y : ι → ℝ) (hxy : ∀ i, ¬ source i → x i = y i)
    (decode : (ℕ → R → ℝ) → Value) (a b : Value) (hab : a ≠ b)
    (correct : decode (transcript es x readPort) = a ∧
               decode (transcript es y readPort) = b) :
    ∃ e ∈ es, ¬ NoCross source e := by
  by_contra h
  push Not at h
  exact cut_transcript_not_both_correct source readPort hr es h x y hxy decode a b hab correct

/-- At every finite horizon, one enabled noncrossing move supplies a
positive-probability obstructing word for the conditional A3-selected law.
This is a finite-deadline guarantee obstruction, not impossibility of eventual
delivery or a countermodel of the complete current axioms. -/
theorem selected_remote_read_obstruction [Fintype Move] [Nonempty Move]
    {R Value : Type*}
    (k : ℕ) (selection : FullWordKLProjection Move k)
    (edge : Move → ι × ι) (idle : Move)
    (source : ι → Prop) (hidle : NoCross source (edge idle))
    (readPort : R → ι) (hr : ∀ r, ¬ source (readPort r))
    (x y : ι → ℝ) (hxy : ∀ i, ¬ source i → x i = y i)
    (decode : Word Move k → (ℕ → R → ℝ) → Value)
    (a b : Value) (hab : a ≠ b) :
    ∃ w : Word Move k, 0 < selection.selected w ∧
      ¬ (decode w (transcript (List.ofFn (edge ∘ w)) x readPort) = a ∧
         decode w (transcript (List.ofFn (edge ∘ w)) y readPort) = b) := by
  let w : Word Move k := fun _ => idle
  refine ⟨w, selected_full_support Move k selection w, ?_⟩
  apply cut_transcript_not_both_correct source readPort hr _ _ x y hxy (decode w) a b hab
  intro e he
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
  exact hidle

end
end OPH.SourceReadSelection

module
public import Geometry.SourceNativeShuttle

@[expose] public section

/-!
# Composition of native words with explicit comparison errors

Comparison states may discard a cleaned bus only with a proved residual
bound. Concatenation adds those bounds. The physical execution contains no
projection or error-clock reset, and signed disturbances are charged after
every scalar mean, including all cleanup operations and idle-register drift.
-/

set_option autoImplicit false

namespace OPH.SourceNativeProgramError
noncomputable section
open OPH.SourceEncodedMemory
open ObserverPatchHolography.ScalarSeamRepair

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem run_near (word : List (ι × ι)) (x y : ι → ℝ) (E : ℝ)
    (h : Near E x y) : Near E (run word x) (run word y) := by
  induction word generalizing x y with
  | nil => exact h
  | cons edge word ih => exact ih _ _ (pairAverage_near edge.1 edge.2 x y E h)

def mapped (f : ι → κ) (word : List (ι × ι)) : List (κ × κ) :=
  word.map (fun e => (f e.1, f e.2))

theorem pair_pullback (f : ι → κ) (hf : Function.Injective f)
    (u v : ι) (x : κ → ℝ) :
    (pairAverage (f u) (f v) x) ∘ f = pairAverage u v (x ∘ f) := by
  ext i
  simp [pairAverage, Function.comp_def, hf.eq_iff]

theorem run_pullback (f : ι → κ) (hf : Function.Injective f)
    (word : List (ι × ι)) (x : κ → ℝ) :
    (run (mapped f word) x) ∘ f = run word (x ∘ f) := by
  induction word generalizing x with
  | nil => rfl
  | cons edge word ih =>
    simpa only [mapped, List.map_cons, run, pair_pullback f hf] using
      ih (pairAverage (f edge.1) (f edge.2) x)

theorem run_outside (word : List (ι × ι)) (x : ι → ℝ) (i : ι)
    (h : ∀ edge ∈ word, i ≠ edge.1 ∧ i ≠ edge.2) : run word x i = x i := by
  induction word generalizing x with
  | nil => rfl
  | cons edge word ih =>
    rw [run, ih _ (fun e he => h e (by simp [he]))]
    have hi := h edge (by simp)
    simp [pairAverage, hi.1, hi.2]

structure Stage (ι : Type*) where
  word : List (ι × ι)
  after : ι → ℝ
  error : ℝ

def Certified (before : ι → ℝ) : List (Stage ι) → Prop
  | [] => True
  | stage::stages => Near stage.error (run stage.word before) stage.after ∧
      Certified stage.after stages

def concatenate : List (Stage ι) → List (ι × ι)
  | [] => []
  | stage::stages => stage.word ++ concatenate stages

def budget : List (Stage ι) → ℝ
  | [] => 0
  | stage::stages => stage.error + budget stages

def finalState (before : ι → ℝ) : List (Stage ι) → (ι → ℝ)
  | [] => before
  | stage::stages => finalState stage.after stages

/-- Each local certificate is composed on the actual concatenated word.
The initial discrepancy is retained through every comparison-state change. -/
theorem composition (stages : List (Stage ι)) (before x : ι → ℝ) (E : ℝ)
    (hc : Certified before stages) (hx : Near E x before) :
    Near (E+budget stages) (run (concatenate stages) x) (finalState before stages) := by
  induction stages generalizing before x E with
  | nil => simpa [budget, concatenate, finalState, run] using hx
  | cons stage stages ih =>
    have hs := near_trans _ _ _ E stage.error (run_near stage.word x before E hx) hc.1
    have ht := ih stage.after (run stage.word x) (E+stage.error) hc.2 hs
    simpa [concatenate, run_append, finalState, budget, add_assoc] using ht

omit [DecidableEq ι] in
theorem concatenated_work (stages : List (Stage ι)) :
    (concatenate stages).length = (stages.map (fun stage => stage.word.length)).sum := by
  induction stages with
  | nil => rfl
  | cons stage stages ih => simp [concatenate, ih]

/-- Preparation, arbitrary signed per-mean errors and all bus residuals are
charged over the same physical history. No cleanup grants a fresh allowance. -/
theorem noisy_composition (stages : List (Stage ι)) (before x : ι → ℝ) (E δ : ℝ)
    (noisy : List ((ι × ι) × (ι → ℝ)))
    (hc : Certified before stages) (hx : Near E x before)
    (hw : noisy.map Prod.fst = concatenate stages)
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ) :
    Near (E+(concatenate stages).length*δ+budget stages)
      (noisyRun noisy x) (finalState before stages) := by
  have hn := noisy_run_bound noisy x before E δ hx he
  have hl : noisy.length = (concatenate stages).length := by
    simpa using congrArg List.length hw
  rw [hw, hl] at hn
  have hi := composition stages before before 0 hc (by intro i; simp)
  simp only [zero_add] at hi
  exact near_trans _ _ _ _ _ hn hi

end
end OPH.SourceNativeProgramError

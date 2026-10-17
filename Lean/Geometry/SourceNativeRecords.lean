module
public import Geometry.SourceReusableBus

@[expose] public section

/-!
# Native arithmetic and its boundary

Finite positive affine computations can use attenuating records: their scale
is part of the supplied interface. These statements do not derive a record
layout, a controller, a physical error allowance, or the metric read law.
Raw unscaled, unbounded growth is impossible in a fixed closed mean system.
-/

set_option autoImplicit false

namespace OPH.SourceNativeRecords
noncomputable section
open OPH.SourceEncodedMemory OPH.SourceReusableBus
open ObserverPatchHolography.ScalarSeamRepair

variable {ι : Type*} [DecidableEq ι]

def halve (s t : ι) : List (Instruction ι) := [.copy s t, .clear t]

theorem halve_formula (s t : ι) (a : ι → ℝ) (hst : s ≠ t) (ht : a t = 0) :
    execute (halve s t) a = fun i => if i = t then 0 else if i = s then a s/2 else a i := by
  ext i
  by_cases hi : i = t
  · subst i; simp [halve, execute, step, cleared]
  · by_cases hs : i = s
    · subst i; simp [halve, execute, step, cleared, copied, hst, ht]
    · simp [halve, execute, step, cleared, copied, hi, hs]

theorem halve_native (s t : ι) (b : ℝ) (a : ι → ℝ)
    (hst : s ≠ t) (ht : a t = 0) :
    run (compile (halve s t)) (encode b a) =
      encode b (fun i => if i = t then 0 else if i = s then a s/2 else a i) := by
  rw [program_native, halve_formula s t a hst ht]

theorem export_value (x : ℝ) (e : ℕ) :
    (x/(2:ℝ)^e)/2 = x/(2:ℝ)^(e+1) := by rw [pow_succ, div_div]

/-- Two equally scaled sources, two blank cells. Only means and a clear;
the old source values survive at half amplitude, and cell 3 holds the sum
at quarter amplitude. Cell 2 is available again. -/
def writeSum : List (Instruction (Fin 4)) :=
  [.copy 0 2, .copy 1 3, .copy 2 3, .clear 2]

theorem writeSum_formula (x y : ℝ) :
    execute writeSum ![x,y,0,0] = ![x/2,y/2,0,(x+y)/4] := by
  ext i
  fin_cases i <;> simp [writeSum, execute, step, copied, cleared]
  ring

theorem writeSum_native (b x y : ℝ) :
    run (compile writeSum) (encode b ![x,y,0,0]) =
      encode b ![x/2,y/2,0,(x+y)/4] := by
  rw [program_native, writeSum_formula]

theorem writeSum_length : (compile writeSum).length = 7 := rfl

theorem writeSum_decoded (x y : ℝ) (e : ℕ) :
    execute writeSum ![x/(2:ℝ)^e,y/(2:ℝ)^e,0,0] =
      ![x/(2:ℝ)^(e+1),y/(2:ℝ)^(e+1),0,(x+y)/(2:ℝ)^(e+2)] := by
  rw [writeSum_formula]
  ext i
  fin_cases i <;> simp [pow_succ] <;> ring

/-- The same convex range is invariant for every finite native word. A word
may be the result of adaptive control; the conclusion quantifies over all
realized words. It makes no assumption of a preselected schedule. -/
theorem mean_range (u v : ι) (a : ι → ℝ) (lo hi : ℝ)
    (ha : ∀ i, lo ≤ a i ∧ a i ≤ hi) :
    ∀ i, lo ≤ pairAverage u v a i ∧ pairAverage u v a i ≤ hi := by
  intro i
  by_cases h : i = u ∨ i = v
  · simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left h]
    have hu := ha u
    have hv := ha v
    constructor <;> linarith
  · simpa [pairAverage, h] using ha i

theorem run_range (es : List (ι × ι)) (a : ι → ℝ) (lo hi : ℝ)
    (ha : ∀ i, lo ≤ a i ∧ a i ≤ hi) :
    ∀ i, lo ≤ run es a i ∧ run es a i ≤ hi := by
  induction es generalizing a with
  | nil => exact ha
  | cons e es ih => exact ih _ (mean_range e.1 e.2 a lo hi ha)

/-- An unscaled logical sequence with at least unit growth eventually exceeds
any fixed initial upper bound. Scaled codes, fresh inputs and expanding
representations are outside this obstruction. -/
theorem growth_lower (v : ℕ → ℝ) (h : ∀ t, v t+1 ≤ v (t+1)) (t : ℕ) :
    v 0 + t ≤ v t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht := h t
    push_cast
    linarith

theorem raw_growth_obstruction (a : ι → ℝ) (lo hi : ℝ)
    (ha : ∀ i, lo ≤ a i ∧ a i ≤ hi) (v : ℕ → ℝ)
    (hv : ∀ t, v t+1 ≤ v (t+1)) (words : ℕ → List (ι × ι)) (read : ℕ → ι) :
    ¬ (∀ t, run (words t) a (read t) = v t) := by
  intro h
  obtain ⟨t, ht⟩ := exists_nat_gt (hi-v 0)
  have hr := (run_range (words t) a lo hi ha (read t)).2
  rw [h t] at hr
  have hg := growth_lower v hv t
  linarith

/-- The same two supported means in a different order give different records.
This is a schedule-selection obstruction for the candidate local law, not
a complete A1--A3 countermodel. -/
theorem schedule_dependence :
    run [(0,1),(1,2)] (![1,3,5] : Fin 3 → ℝ) 0 = 2 ∧
    run [(1,2),(0,1)] (![1,3,5] : Fin 3 → ℝ) 0 = 5/2 := by
  change ((1+3:ℝ)/2 = 2) ∧ ((1:ℝ)+(3+5)/2)/2 = 5/2
  norm_num

end
end OPH.SourceNativeRecords

module
public import Geometry.SourceBankMachine

@[expose] public section

/-!
# Native lowering of the bank instruction machine

Routes are finite geometric inputs, not local correctness certificates.
Their endpoints and blank scratch cells determine a retained-source shuttle.
The logical state transition, native word and error allowance are derived
from the native primitive theorems.
-/

set_option autoImplicit false

namespace OPH.SourceBankLowering
noncomputable section
open OPH.SourceBankMachine OPH.SourceNativeAccumulator OPH.SourceReusableBus
open OPH.SourceEncodedMemory OPH.SourceNativeShuttle OPH.SourceNativeCore
open OPH.SourceNativeProgramError OPH.SourceNativeStoredProgram

def amplitude (g : ℝ) (v : Values) (e : Scales) : ℕ → ℝ :=
  represented (fun i => g*(v i:ℝ)) e

def railPerm (f : Equiv.Perm ℕ) : Equiv.Perm (ℕ × Bool) :=
  Equiv.prodCongr f (Equiv.refl Bool)

theorem encode_relabel (f : Equiv.Perm ℕ) (b : ℝ) (a : ℕ → ℝ) :
    (encode b a) ∘ (railPerm f).symm = encode b (a ∘ f.symm) := by
  funext p
  rcases p with ⟨i,r⟩
  cases r <;> simp [encode, railPerm]

theorem start_amplitude (g : ℝ) (v : Values) (e : Scales) :
    amplitude g (valueStep .start v) (scaleStep .start e) =
      represented (startedValues (fun i => g*(v i:ℝ))) (startedScales e) := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp [amplitude, represented, valueStep, scaleStep, startedValues, startedScales, h0,h1]

theorem add_amplitude (g : ℝ) (v : Values) (e : Scales) :
    amplitude g (valueStep .add v) (scaleStep .add e) =
      represented (addedValues 3 (fun i => g*(v i:ℝ))) (addedScales 3 e) := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h3 : i = 3 <;>
    simp [amplitude, represented, valueStep, scaleStep, addedValues, addedScales,
      commonScale, h0,h3, mul_add]

theorem retire_amplitude (g : ℝ) (v : Values) (e : Scales) :
    amplitude g (valueStep .retire v) (scaleStep .retire e) =
      cleared 3 (cleared 1 (amplitude g v e)) := by
  funext i
  by_cases h1 : i = 1 <;> by_cases h3 : i = 3 <;>
    simp [amplitude, represented, valueStep, scaleStep, cleared,h1,h3]

theorem lower_start (k : ℕ) (b g A : ℝ) (v : Values) (e : Scales)
    (hA : 0 ≤ A) (ha : |amplitude g v e 0| ≤ A) :
    Construction (encode b (amplitude g v e))
      (encode b (amplitude g (valueStep .start v) (scaleStep .start e)))
      (compile (startCore k)) (A/(2:ℝ)^k) := by
  rw [start_amplitude]
  exact Construction.start k b A _ e hA ha

theorem lower_add (b g : ℝ) (v : Values) (e : Scales) (hw : v 1 = 0) :
    Construction (encode b (amplitude g v e))
      (encode b (amplitude g (valueStep .add v) (scaleStep .add e)))
      (compile (addWord 3 e)) 0 := by
  rw [add_amplitude]
  exact Construction.add 3 (by decide) b _ e (by simp [hw])

theorem lower_retire (b g : ℝ) (v : Values) (e : Scales) :
    Construction (encode b (amplitude g v e))
      (encode b (amplitude g (valueStep .retire v) (scaleStep .retire e)))
      (resetWord 3 1) 0 := by
  rw [retire_amplitude]
  exact Construction.retire 3 1 (by decide) b _

structure Route (source target depth : ℕ) where
  cells : Equiv.Perm ℕ
  depth_pos : 3 ≤ depth
  source_eq : cells depth = source
  target_eq : cells (depth-1) = target

def Route.Blank {s t d : ℕ} (r : Route s t d) (v : Values) : Prop :=
  ∀ i < d-1, v (r.cells i) = 0

theorem route_distinct {s t d : ℕ} (r : Route s t d) : s ≠ t := by
  intro h
  have he : r.cells d = r.cells (d-1) := r.source_eq.trans (h.trans r.target_eq.symm)
  have := r.cells.injective he
  have := r.depth_pos
  omega

/-- The endpoint and blank-bus conditions imply the complete reference
transition, including preservation of every other logical register. -/
theorem transfer_reference {s t d : ℕ} (r : Route s t d) (g : ℝ)
    (v : Values) (e : Scales) (hb : r.Blank v) :
    (reference (d-2) (amplitude g v e ∘ r.cells)) ∘ r.cells.symm =
      amplitude g (valueStep (.transfer s t d) v) (scaleStep (.transfer s t d) e) := by
  have hd := r.depth_pos
  have hn1 : d-2+1 = d-1 := by omega
  have hn2 : d-2+2 = d := by omega
  have hst := route_distinct r
  funext j
  obtain ⟨i,rfl⟩ := r.cells.surjective j
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hs : r.cells i = s ↔ i = d :=
    ⟨fun h => r.cells.injective (h.trans r.source_eq.symm),
      fun h => (congrArg r.cells h).trans r.source_eq⟩
  have ht : r.cells i = t ↔ i = d-1 :=
    ⟨fun h => r.cells.injective (h.trans r.target_eq.symm),
      fun h => (congrArg r.cells h).trans r.target_eq⟩
  by_cases hiS : i = d
  · subst i
    simp [reference, hn2, amplitude, represented, valueStep, scaleStep, r.source_eq,
      hst, pow_succ, div_div]
  by_cases hiT : i = d-1
  · subst i
    simp [reference, hn1, hn2, show d-1 ≠ d by omega, amplitude, represented,
      valueStep, scaleStep, r.source_eq, r.target_eq, pow_add, div_div]
  by_cases hiB : i ≤ d-2
  · have hz := hb i (by omega)
    simp [reference, hn1,hn2,hiS,hiT,hiB, amplitude, represented,
      valueStep,scaleStep,hs,ht,hz]
  · simp [reference, hn1,hn2,hiS,hiT,hiB, amplitude, represented,
      valueStep,scaleStep,hs,ht]

def transferWord {s t d : ℕ} (r : Route s t d) (k : ℕ) : Word :=
  mapped (railPerm r.cells) (compile (if t = 3 then freshHandoff (d-2) k else handoff (d-2) k))

theorem lower_transfer {s t d : ℕ} (r : Route s t d) (k : ℕ) (b g A : ℝ)
    (v : Values) (e : Scales) (hA : 0 ≤ A) (ha : Bounded A (amplitude g v e))
    (hb : r.Blank v) (ht : t = 3 → v t = 0) :
    Construction (encode b (amplitude g v e))
      (encode b (amplitude g (valueStep (.transfer s t d) v) (scaleStep (.transfer s t d) e)))
      (transferWord r k) (residual (d-2) k A) := by
  have hd := r.depth_pos
  have hn : 1 ≤ d-2 := by omega
  have hab : Bounded A (amplitude g v e ∘ r.cells) := fun i => ha (r.cells i)
  have hblank : ∀ i ≤ d-2, (amplitude g v e ∘ r.cells) i = 0 := by
    intro i hi
    simp [amplitude, represented, hb i (by omega)]
  have hstep : Construction (encode b (amplitude g v e ∘ r.cells))
      (encode b (reference (d-2) (amplitude g v e ∘ r.cells)))
      (compile (if t = 3 then freshHandoff (d-2) k else handoff (d-2) k))
      (residual (d-2) k A) := by
    split_ifs with h
    · apply Construction.read (d-2) k b A _ hn hA hab
      intro i hi
      by_cases hz : i ≤ d-2
      · exact hblank i hz
      · have hi' : i = d-1 := by omega
        subst i
        simp [amplitude, represented, r.target_eq, ht h]
    · exact Construction.store (d-2) k b A _ hn hA hab hblank
  have moved := Construction.relabel (railPerm r.cells) hstep
  rw [encode_relabel, encode_relabel, transfer_reference r g v e hb] at moved
  have initial : (amplitude g v e ∘ r.cells) ∘ r.cells.symm = amplitude g v e := by
    funext i
    simp
  rw [initial] at moved
  exact moved

theorem divide_bounded (x A : ℝ) (k : ℕ) (hA : 0 ≤ A) (hx : |x| ≤ A) :
    |x/(2:ℝ)^k| ≤ A := by
  have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2^k)]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^k)).mpr
  nlinarith

theorem reference_bounded (n : ℕ) (a : ℕ → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (ha : Bounded A a) : Bounded A (reference n a) := by
  intro i
  unfold reference
  split_ifs with hs ht hb
  · simpa using divide_bounded (a (n+2)) A 1 hA (ha (n+2))
  · exact divide_bounded (a (n+2)) A (n+2) hA (ha (n+2))
  · simpa using hA
  · exact ha i

theorem start_bounded (g A : ℝ) (v : Values) (e : Scales)
    (hA : 0 ≤ A) (ha : Bounded A (amplitude g v e)) :
    Bounded A (amplitude g (valueStep .start v) (scaleStep .start e)) := by
  rw [start_amplitude, ← ideal_start]
  exact execute_bounded [.clear 1,.clear 0,.copy 2 0] A (amplitude g v e) hA ha

theorem add_bounded (g A : ℝ) (v : Values) (e : Scales)
    (hA : 0 ≤ A) (ha : Bounded A (amplitude g v e)) (hw : v 1 = 0) :
    Bounded A (amplitude g (valueStep .add v) (scaleStep .add e)) := by
  rw [add_amplitude, ← add_formula 3 (by decide) _ _ (by simp [hw])]
  exact execute_bounded _ A _ hA ha

theorem retire_bounded (g A : ℝ) (v : Values) (e : Scales)
    (hA : 0 ≤ A) (ha : Bounded A (amplitude g v e)) :
    Bounded A (amplitude g (valueStep .retire v) (scaleStep .retire e)) := by
  rw [retire_amplitude]
  exact execute_bounded [.clear 1,.clear 3] A (amplitude g v e) hA ha

theorem transfer_bounded {s t d : ℕ} (r : Route s t d) (g A : ℝ)
    (v : Values) (e : Scales) (hA : 0 ≤ A) (ha : Bounded A (amplitude g v e))
    (hb : r.Blank v) :
    Bounded A (amplitude g (valueStep (.transfer s t d) v) (scaleStep (.transfer s t d) e)) := by
  rw [← transfer_reference r g v e hb]
  exact fun i => reference_bounded _ _ A hA (fun j => ha (r.cells j)) (r.cells.symm i)

end
end OPH.SourceBankLowering

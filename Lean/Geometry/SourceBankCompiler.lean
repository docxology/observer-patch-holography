module
public import Geometry.SourceBankLowering
public import Geometry.SourceBankInvariant

@[expose] public section

/-!
# End-to-end native compilation of finite bank programs

The backend receives geometric route data. It has no field for a desired
output, a local correctness proof, an arbitrary word or an error oracle.
The compiler supplies retirement and workspace invariants, native lowering
supplies the comparison errors, and the recurrence follows from the emitted
instructions. Preparation, supported placement and the controller are inputs.
-/

set_option autoImplicit false

namespace OPH.SourceBankCompiler
noncomputable section
open OPH.SourceBankMachine OPH.SourceBankInvariant OPH.SourceBankLowering
open OPH.SourceNativeShuttle OPH.SourceNativeStoredProgram OPH.SourceEncodedMemory
open OPH.SourceNativeAccumulator OPH.SourceNativeCore OPH.SourceReusableBus

/-- A route annotation for each transfer in the compiled instruction
stream. No constructor admits a pre-certified arbitrary operation. -/
inductive Placed : List Op → Type
  | nil : Placed []
  | start {ops : List Op} (rest : Placed ops) : Placed (.start::ops)
  | add {ops : List Op} (rest : Placed ops) : Placed (.add::ops)
  | retire {ops : List Op} (rest : Placed ops) : Placed (.retire::ops)
  | transfer {s t d : ℕ} {ops : List Op} (route : Route s t d) (rest : Placed ops) :
      Placed (.transfer s t d::ops)

def nativeWord {ops : List Op} : Placed ops → ℕ → Scales → Word
  | .nil, _, _ => []
  | .start rest, k, e => compile (startCore k) ++ nativeWord rest k (scaleStep .start e)
  | .add rest, k, e => compile (addWord 3 e) ++ nativeWord rest k (scaleStep .add e)
  | .retire rest, k, e => resetWord 3 1 ++ nativeWord rest k (scaleStep .retire e)
  | .transfer (s := s) (t := t) (d := d) r rest, k, e => transferWord r k ++
      nativeWord rest k (scaleStep (.transfer s t d) e)

def error {ops : List Op} : Placed ops → ℕ → ℝ → ℝ
  | .nil, _, _ => 0
  | .start rest, k, A => A/(2:ℝ)^k+error rest k A
  | .add rest, k, A => 0+error rest k A
  | .retire rest, k, A => 0+error rest k A
  | .transfer (d := d) _ rest, k, A => residual (d-2) k A+error rest k A

def Scratch (R : ℕ) {ops : List Op} : Placed ops → Prop
  | .nil => True
  | .start rest => Scratch R rest
  | .add rest => Scratch R rest
  | .retire rest => Scratch R rest
  | .transfer (d := d) r rest =>
      (∀ i < d-1, r.cells i = 1 ∨ R ≤ r.cells i) ∧ Scratch R rest

theorem scratch_blank {R s t d : ℕ} (r : Route s t d) (v : Values)
    (hs : ∀ i < d-1, r.cells i = 1 ∨ R ≤ r.cells i)
    (hw : v 1 = 0) (hv : Supported R v) : r.Blank v := by
  intro i hi
  rcases hs i hi with h | h
  · simpa [h] using hw
  · exact hv _ h

/-- Whole-word compilation is derived by induction. In particular the
caller supplies neither a `Construction` nor the correct final state. -/
theorem native_construction {ops : List Op} (p : Placed ops) (R k : ℕ)
    (b g A : ℝ) (v : Values) (e : Scales) (hR : 4 ≤ R) (hA : 0 ≤ A)
    (ha : Bounded A (amplitude g v e)) (hs : Safe ops v) (hv : Supported R v)
    (ho : ∀ op ∈ ops, Confined R op) (hr : Scratch R p) :
    Construction (encode b (amplitude g v e))
      (encode b (amplitude g (values ops v) (scales ops e)))
      (nativeWord p k e) (error p k A) := by
  induction p generalizing v e with
  | nil => exact Construction.empty _
  | start rest ih =>
    exact Construction.append (lower_start k b g A v e hA (ha 0))
      (ih _ _ (start_bounded g A v e hA ha) hs.2
        (step_supported R hR .start v trivial hv)
        (fun op h => ho op (by simp [h])) hr)
  | add rest ih =>
    exact Construction.append (lower_add b g v e hs.1.1)
      (ih _ _ (add_bounded g A v e hA ha hs.1.1) hs.2
        (step_supported R hR .add v trivial hv)
        (fun op h => ho op (by simp [h])) hr)
  | retire rest ih =>
    exact Construction.append (lower_retire b g v e)
      (ih _ _ (retire_bounded g A v e hA ha) hs.2
        (step_supported R hR .retire v trivial hv)
        (fun op h => ho op (by simp [h])) hr)
  | @transfer s t d ops r rest ih =>
    have hb := scratch_blank r v hr.1 hs.1.1 hv
    have ht : t = 3 → v t = 0 := fun h => by simpa [h] using hs.1.2 h
    exact Construction.append (lower_transfer r k b g A v e hA ha hb ht)
      (ih _ _ (transfer_bounded r g A v e hA ha hb) hs.2
        (step_supported R hR (.transfer s t d) v (ho _ (by simp)) hv)
        (fun op h => ho op (by simp [h])) hr.2)

theorem compiled_program {n : ℕ} (rd wd : ℕ → ℕ) (side : Bool) (menus : List (Layer n))
    (p : Placed (program n rd wd side menus)) (k : ℕ) (b g A : ℝ)
    (v : Values) (e : Scales) (hA : 0 ≤ A) (ha : Bounded A (amplitude g v e))
    (hc : Clean v) (hv : Supported (4+2*n) v) (hr : Scratch (4+2*n) p) :
    Construction (encode b (amplitude g v e))
      (encode b (amplitude g (values (program n rd wd side menus) v)
        (scales (program n rd wd side menus) e)))
      (nativeWord p k e) (error p k A) :=
  native_construction p (4+2*n) k b g A v e (by omega) hA ha
    (program_safe n rd wd side menus v hc) hv (program_confined n rd wd side menus) hr

/-- Local publication of the computed final-layer value. The value and its
cap are both derived by the compiler theorem; the receiver gets only local
samples, a public cap and the full-history error allowance. -/
theorem compiled_publication {n : ℕ} (rd wd : ℕ → ℕ) (side : Bool) (menus : List (Layer n))
    (p : Placed (program n rd wd side menus)) (k : ℕ) (b g A E δ ρ : ℝ)
    (v : Values) (e : Scales) (cap : Fin n → ℤ) (i : Fin n)
    (hA : 0 ≤ A) (ha : Bounded A (amplitude g v e)) (hc : Clean v)
    (hv : Supported (4+2*n) v) (hr : Scratch (4+2*n) p) (hg : 0 < g)
    (hu : v 2 = 1) (hcap : ∀ j, |v (bank n side j)| ≤ cap j)
    (x : State) (plus minus : ℝ) (noisy : List ((Port × Port) × State))
    (hw : noisy.map Prod.fst = nativeWord p k e)
    (hx : Near E x (encode b (amplitude g v e)))
    (he : ∀ en ∈ noisy, ∀ j, |en.2 j| ≤ δ)
    (hp : |plus-noisyRun noisy x (bank n (finalSide side menus) i,false)| ≤ ρ)
    (hm : |minus-noisyRun noisy x (bank n (finalSide side menus) i,true)| ≤ ρ)
    (hsmall : 2*((2:ℝ)^(scales (program n rd wd side menus) e
        (bank n (finalSide side menus) i))/g)*
      (E+(nativeWord p k e).length*δ+error p k A+ρ) < 1) :
    OPH.SourceAccumulatorDecoder.decode
      (((2:ℝ)^(scales (program n rd wd side menus) e
          (bank n (finalSide side menus) i))/g)*((plus-minus)/2))
      (((2:ℝ)^(scales (program n rd wd side menus) e
          (bank n (finalSide side menus) i))/g)*
        (E+(nativeWord p k e).length*δ+error p k A+ρ))
      (recurrence n 1 menus cap i) =
        some (recurrence n 1 menus (fun j => v (bank n side j)) i) := by
  apply publication b g E δ ρ _ _ _ _ _
    (compiled_program rd wd side menus p k b g A v e hA ha hc hv hr)
    x plus minus noisy hg _ hw hx he hp hm _ hsmall
  · simp only [amplitude,represented,program_recurrence,hu]
  · simpa using recurrence_bound n 1 menus (fun j => v (bank n side j)) cap hcap i

theorem native_word_length {ops : List Op} (p : Placed ops) (k : ℕ) (e : Scales) :
    (nativeWord p k e).length = work ops k e := by
  induction p generalizing e with
  | nil => rfl
  | start rest ih => simp [nativeWord,work,opWork,startCore_length,ih]
  | add rest ih => simp [nativeWord,work,opWork,add_length,commonScale,ih]
  | retire rest ih => simp [nativeWord,work,opWork,resetWord,copyWord,ih]; omega
  | @transfer s t d ops r rest ih =>
    simp only [nativeWord,List.length_append,ih,transferWord,
      OPH.SourceNativeProgramError.mapped,List.length_map,work,opWork]
    split_ifs <;> simp [freshHandoff_length,handoff_length]

theorem residual_upper (n k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    residual n k A ≤ A*OPH.SourceBusScaling.mass n/(2:ℝ)^k := by
  have hx : 0 ≤ A*OPH.SourceBusScaling.mass n/(2:ℝ)^k := by
    unfold OPH.SourceBusScaling.mass
    positivity
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hid : residual n k A =
      (A*OPH.SourceBusScaling.mass n/(2:ℝ)^k)/(2*(n:ℝ)+1) := by
    simp only [OPH.SourceNativeShuttle.residual,one_div_pow]
    ring
  rw [hid]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*n+1)).mpr
  nlinarith

theorem error_nonneg {ops : List Op} (p : Placed ops) (k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ error p k A := by
  induction p with
  | nil => exact le_refl _
  | start rest ih => exact add_nonneg (div_nonneg hA (by positivity)) ih
  | add rest ih => exact add_nonneg (le_refl _) ih
  | retire rest ih => exact add_nonneg (le_refl _) ih
  | transfer r rest ih => exact add_nonneg (residual_nonneg _ k A hA) ih

theorem error_bound {ops : List Op} (p : Placed ops) (k : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    error p k A ≤ A*(cleanupBudget ops:ℝ)/(2:ℝ)^k := by
  induction p with
  | nil => simp [error,cleanupBudget]
  | start rest ih =>
    simp only [error,cleanupBudget,List.map_cons,List.sum_cons,cleanupCharge,Nat.cast_add,Nat.cast_one] at *
    calc
      _ ≤ A/2^k+A*(List.map cleanupCharge _).sum/2^k := add_le_add (le_refl _) ih
      _ = _ := by ring
  | add rest ih => simpa [error,cleanupBudget,cleanupCharge] using ih
  | retire rest ih => simpa [error,cleanupBudget,cleanupCharge] using ih
  | @transfer s t d ops r rest ih =>
    have hd := r.depth_pos
    have hn : d-2+1 = d-1 := by omega
    have hh := residual_upper (d-2) k A hA
    have hm : OPH.SourceBusScaling.mass (d-2) = ((d-1:ℕ):ℝ)^2 := by
      simp only [OPH.SourceBusScaling.mass]
      rw [← Nat.cast_one,← Nat.cast_add,hn]
    rw [hm] at hh
    simp only [error,cleanupBudget,List.map_cons,List.sum_cons,cleanupCharge,Nat.cast_add,Nat.cast_pow] at *
    calc
      _ ≤ A*(↑(d-1))^2/2^k+A*(List.map cleanupCharge ops).sum/2^k := add_le_add hh ih
      _ = _ := by ring

end
end OPH.SourceBankCompiler

module
public import Geometry.SourceNativeCore

@[expose] public section

/-!
# Composable stored computation using scalar means

The construction relation admits only native start, aligned addition,
retirement, and retained-source transfer, together with scalar-port
permutations and concatenation. Its error certificate is derived from those
constructors. A supplied layout must support the resulting scalar edges.
Neither the temporal word nor that layout is selected from the source axioms.
-/

set_option autoImplicit false

namespace OPH.SourceNativeStoredProgram
noncomputable section
open OPH.SourceEncodedMemory OPH.SourceReusableBus OPH.SourceNativeAccumulator
open OPH.SourceNativeShuttle OPH.SourceNativeProgramError OPH.SourceNativeCore

abbrev Port := ℕ × Bool
abbrev State := Port → ℝ
abbrev Word := List (Port × Port)

inductive Construction : State → State → Word → ℝ → Prop
  | empty (x : State) : Construction x x [] 0
  | start (k : ℕ) (b A : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ)
      (hA : 0 ≤ A) (ha : |represented v e 0| ≤ A) :
      Construction (encode b (represented v e))
        (encode b (represented (startedValues v) (startedScales e)))
        (compile (startCore k)) (A/(2:ℝ)^k)
  | add (s : ℕ) (hs : 2 ≤ s) (b : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ)
      (hw : v 1 = 0) :
      Construction (encode b (represented v e))
        (encode b (represented (addedValues s v) (addedScales s e)))
        (compile (addWord s e)) 0
  | retire (s t : ℕ) (hne : s ≠ t) (b : ℝ) (a : ℕ → ℝ) :
      Construction (encode b a) (encode b (cleared s (cleared t a))) (resetWord s t) 0
  | store (n k : ℕ) (b A : ℝ) (a : ℕ → ℝ)
      (hn : 1 ≤ n) (hA : 0 ≤ A) (ha : Bounded A a) (hz : ∀ i ≤ n, a i = 0) :
      Construction (encode b a) (encode b (reference n a))
        (compile (handoff n k)) (residual n k A)
  | read (n k : ℕ) (b A : ℝ) (a : ℕ → ℝ)
      (hn : 1 ≤ n) (hA : 0 ≤ A) (ha : Bounded A a) (hz : ∀ i ≤ n+1, a i = 0) :
      Construction (encode b a) (encode b (reference n a))
        (compile (freshHandoff n k)) (residual n k A)
  | relabel (f : Equiv.Perm Port) {x y : State} {w : Word} {R : ℝ}
      (h : Construction x y w R) :
      Construction (x ∘ f.symm) (y ∘ f.symm) (mapped f w) R
  | append {x y z : State} {w v : Word} {R S : ℝ}
      (first : Construction x y w R) (second : Construction y z v S) :
      Construction x z (w++v) (R+S)

theorem run_relabel (f : Equiv.Perm Port) (w : Word) (x : State) :
    run (mapped f w) (x ∘ f.symm) = (run w x) ∘ f.symm := by
  ext i
  have h := congrFun (run_pullback f f.injective w (x ∘ f.symm)) (f.symm i)
  simpa [Function.comp_def] using h

/-- A closed proof over the native constructors, with no local correctness
certificate supplied as a hypothesis. Bus comparison errors accumulate. -/
theorem correct {x y : State} {w : Word} {R : ℝ}
    (h : Construction x y w R) : Near R (run w x) y := by
  induction h with
  | empty x => intro i; simp [run]
  | start k b A v e hA ha => exact startCore_native_error k b A v e hA ha
  | add s hs b v e hw =>
    rw [program_native, add_formula s hs v e hw]
    intro i; simp
  | retire s t hne b a =>
    rw [reset_rectangle s t hne b a]
    intro i; simp
  | store n k b A a hn hA ha hz => exact handoff_native_error n k b A a hn hA ha hz
  | read n k b A a hn hA ha hz => exact freshHandoff_native_error n k b A a hn hA ha hz
  | relabel f h ih =>
    rw [run_relabel]
    exact fun i => ih (f.symm i)
  | append first second ih₁ ih₂ =>
    rw [run_append]
    exact near_trans _ _ _ _ _ (run_near _ _ _ _ ih₁) ih₂

theorem noisy_correct {initial final : State} {w : Word} {R : ℝ}
    (h : Construction initial final w R) (x : State) (E δ : ℝ)
    (noisy : List ((Port × Port) × State))
    (hw : noisy.map Prod.fst = w) (hx : Near E x initial)
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ) :
    Near (E+w.length*δ+R) (noisyRun noisy x) final := by
  have hn := noisy_run_bound noisy x initial E δ hx he
  have hl : noisy.length = w.length := by simpa using congrArg List.length hw
  rw [hw, hl] at hn
  exact near_trans _ _ _ _ _ hn (correct h)

/-- Publication uses a local contrast and a public magnitude cap. The complete
word length, preparation, every cleanup residual, and sampling error enter
the same radius. Reusing a bank does not grant a fresh precision budget. -/
theorem publication {initial : State} {w : Word} {R : ℝ}
    (b g E δ ρ : ℝ) (a : ℕ → ℝ) (receiver exponent : ℕ) (value bound : ℤ)
    (h : Construction initial (encode b a) w R)
    (x : State) (p m : ℝ) (noisy : List ((Port × Port) × State))
    (hg : 0 < g) (ha : a receiver = g*value/(2:ℝ)^exponent)
    (hw : noisy.map Prod.fst = w) (hx : Near E x initial)
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (receiver,false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (receiver,true)| ≤ ρ)
    (hb : |value| ≤ bound)
    (hsmall : 2*((2:ℝ)^exponent/g)*(E+w.length*δ+R+ρ) < 1) :
    SourceAccumulatorDecoder.decode (((2:ℝ)^exponent/g)*((p-m)/2))
      (((2:ℝ)^exponent/g)*(E+w.length*δ+R+ρ)) bound = some value := by
  have hn := noisy_correct h x E δ noisy hw hx he
  have hplus := hn (receiver,false)
  have hminus := hn (receiver,true)
  simp only [encode, Bool.false_eq_true, ite_false, ite_true] at hplus hminus
  have hp' := (abs_add_le (p-noisyRun noisy x (receiver,false))
    (noisyRun noisy x (receiver,false)-(b+a receiver))).trans (add_le_add hp hplus)
  have hm' := (abs_add_le (m-noisyRun noisy x (receiver,true))
    (noisyRun noisy x (receiver,true)-(b-a receiver))).trans (add_le_add hm hminus)
  rw [sub_add_sub_cancel] at hp' hm'
  have hc := contrast_error b (a receiver) p m (E+w.length*δ+R+ρ)
    (by linarith) (by linarith)
  rw [ha] at hc
  exact SourceAccumulatorDecoder.decode_available _ _ bound value
    (by nlinarith [hsmall])
    (SourceAccumulatorProgram.normalized_error _ g _ value exponent hg hc) hb

end
end OPH.SourceNativeStoredProgram

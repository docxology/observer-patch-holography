module
public import Geometry.SourceBankBusWitness
public import Geometry.SourceBankPrecision

@[expose] public section

/-!
# Finite noisy publication for every bank program on the declared bus

The compiler, route witness and precision theorem discharge the complete
native word, route existence, lifetimes, error ledger and strict decoder
margin. Preparation and a controller realizing that word with the stated
physical error allowances remain hypotheses. This is not an A1--A3 derivation
of the M1 population, menu, observer cover or source selection.
-/

set_option autoImplicit false

namespace OPH.SourceBankExecution
noncomputable section
open OPH.SourceBankMachine OPH.SourceBankInvariant OPH.SourceBankLowering
open OPH.SourceBankCompiler OPH.SourceBankBusWitness OPH.SourceBankPrecision
open OPH.SourceEncodedMemory OPH.SourceNativeAccumulator OPH.SourceReusableBus
open OPH.SourceNativeStoredProgram

def grid (B : ℕ) : ℝ := (2:ℝ)^B
def gain (B : ℕ) : ℝ := (grid B-3)/grid B

def finalScale (n : ℕ) (side : Bool) (menus : List (Layer n)) (i : Fin n) : ℕ :=
  scales (program n (fun _ => 3) (fun _ => 3) side menus) (fun _ => 0)
    (bank n (finalSide side menus) i)

def allowance (n : ℕ) (side : Bool) (menus : List (Layer n)) (k B : ℕ) (A : ℝ) : ℝ :=
  1/(4*grid B)+(nativeWord (placement n side menus) k (fun _ => 0)).length*(5/(8*grid B))+
    error (placement n side menus) k A+1/(4*grid B)

/-- No desired output, construction certificate, route-existence premise,
or final strict-margin assumption is supplied to this theorem. Precision
and the word are independent of the payload values within the public bound. -/
theorem finite_execution (n : ℕ) (side : Bool) (menus : List (Layer n))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ k B : ℕ, 3 < grid B ∧
      ∀ (v : Values) (cap : Fin n → ℤ) (b : ℝ),
      (∀ j, |(v j:ℝ)| ≤ A) → Clean v → Supported (4+2*n) v → v 2 = 1 →
      (∀ j, |v (bank n side j)| ≤ cap j) →
      ∀ (i : Fin n) (x : State) (plus minus : ℝ)
        (noisy : List ((Port × Port) × State)),
      noisy.map Prod.fst = nativeWord (placement n side menus) k (fun _ => 0) →
      Near (1/(4*grid B)) x (encode b (amplitude (gain B) v (fun _ => 0))) →
      (∀ en ∈ noisy, ∀ j, |en.2 j| ≤ 5/(8*grid B)) →
      |plus-noisyRun noisy x (bank n (finalSide side menus) i,false)| ≤ 1/(4*grid B) →
      |minus-noisyRun noisy x (bank n (finalSide side menus) i,true)| ≤ 1/(4*grid B) →
      OPH.SourceAccumulatorDecoder.decode
        (((2:ℝ)^(finalScale n side menus i)/gain B)*((plus-minus)/2))
        (((2:ℝ)^(finalScale n side menus i)/gain B)*allowance n side menus k B A)
        (recurrence n 1 menus cap i) =
          some (recurrence n 1 menus (fun j => v (bank n side j)) i) := by
  obtain ⟨k,B,hQ,hm⟩ := exists_global_margin (placement n side menus) (fun _ => 0)
    0 (by intro i; exact le_refl _) A hA
  refine ⟨k,B,hQ,?_⟩
  intro v cap b hv hc hs hu hcap i x plus minus noisy hw hx he hp hminus
  have hq : 0 < grid B := by unfold grid; positivity
  have hg : 0 < gain B := by unfold gain; exact div_pos (by change 3 < grid B at hQ; linarith) hq
  have hg1 : gain B ≤ 1 := by unfold gain; apply (div_le_iff₀ hq).mpr; linarith
  have ha : OPH.SourceNativeShuttle.Bounded A (amplitude (gain B) v (fun _ => 0)) := by
    intro j
    simp only [amplitude,represented,pow_zero,div_one,abs_mul,abs_of_pos hg]
    calc
      gain B*|(v j:ℝ)| ≤ 1*A := mul_le_mul hg1 (hv j) (abs_nonneg _) (by norm_num)
      _ = A := one_mul _
  exact compiled_publication (fun _ => 3) (fun _ => 3) side menus (placement n side menus)
    k b (gain B) A (1/(4*grid B)) (5/(8*grid B)) (1/(4*grid B))
    v (fun _ => 0) cap i hA ha hc hs (placement_scratch n side menus) hg hu hcap
    x plus minus noisy hw hx he hp hminus (hm _)

end
end OPH.SourceBankExecution

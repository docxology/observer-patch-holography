module
public import Geometry.SourceTemporalNative
public import Geometry.SourceTemporalMenu

@[expose] public section

/-!
# Permanent loss before the first discriminating observation

Equal post-event states and equal initial receiver samples give identical
complete receiver histories for any common continuation, including infinite
words. This applies to a declared preparation and sample interface. It does
not exclude redundancy, a retained discriminating sample, protected records
or an input-dependent side channel.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalErasure
noncomputable section
open ObserverPatchHolography.ScalarSeamRepair
open OPH.SourceReadAcceptance OPH.SourceTemporalNative OPH.SourceTemporalMenu

variable {P R Value : Type*} [DecidableEq P]

def streamState (word : ℕ → P × P) (x : P → ℝ) : ℕ → P → ℝ
  | 0 => x
  | k+1 => pairAverage (word k).1 (word k).2 (streamState word x k)

/-- No finite or infinite common suffix restores an erased state difference. -/
theorem erased_future_eq (word : ℕ → P × P) (x y : P → ℝ)
    (he : pairAverage (word 0).1 (word 0).2 x = pairAverage (word 0).1 (word 0).2 y)
    (k : ℕ) : streamState word x (k+1) = streamState word y (k+1) := by
  induction k with
  | zero => exact he
  | succ k ih => exact congrArg (pairAverage (word (k+1)).1 (word (k+1)).2) ih

theorem erased_transcript_eq (word : ℕ → P × P) (x y : P → ℝ)
    (he : pairAverage (word 0).1 (word 0).2 x = pairAverage (word 0).1 (word 0).2 y)
    (read : R → P) (hi : ∀ r, x (read r) = y (read r)) :
    (fun k r => streamState word x k (read r)) =
      (fun k r => streamState word y k (read r)) := by
  funext k r
  cases k with
  | zero => exact hi r
  | succ k => rw [erased_future_eq word x y he k]

/-- Even a decoder of the complete infinite transcript cannot return both
different source values. A common random seed can be included in the decoder. -/
theorem erased_not_both_correct (word : ℕ → P × P) (x y : P → ℝ)
    (he : pairAverage (word 0).1 (word 0).2 x = pairAverage (word 0).1 (word 0).2 y)
    (read : R → P) (hi : ∀ r, x (read r) = y (read r))
    (decode : (ℕ → R → ℝ) → Value) (a b : Value) (hab : a ≠ b) :
    ¬ (decode (fun k r => streamState word x k (read r)) = a ∧
       decode (fun k r => streamState word y k (read r)) = b) := by
  rw [erased_transcript_eq word x y he read hi]
  rintro ⟨ha,hb⟩
  exact hab (ha.symm.trans hb)

/-- A sound partial publication rule must abstain on a permanently merged
pair, regardless of the permitted waiting time. -/
theorem erased_sound_abstains (word : ℕ → P × P) (x y : P → ℝ)
    (he : pairAverage (word 0).1 (word 0).2 x = pairAverage (word 0).1 (word 0).2 y)
    (read : R → P) (hi : ∀ r, x (read r) = y (read r))
    (possible : Value → (ℕ → R → ℝ) → Prop)
    (publish : (ℕ → R → ℝ) → Option Value) (hs : Sound possible publish)
    (a b : Value) (hab : a ≠ b)
    (ha : possible a (fun k r => streamState word x k (read r)))
    (hb : possible b (fun k r => streamState word y k (read r))) :
    publish (fun k r => streamState word x k (read r)) = none := by
  rw [← erased_transcript_eq word x y he read hi] at hb
  exact shared_observation_abstains possible publish hs _ a b ha hb hab

def preparation : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 15360 → ℝ) :=
  LinearMap.pi (fun p => if p=0 then coordinate 0 else if p=1 then coordinate 1 else 0)

def aggregateWord : List (Fin 15360 × Fin 15360) := [(0,1),(1,⟨14, by decide⟩),(⟨14, by decide⟩,⟨23, by decide⟩),(⟨23, by decide⟩,⟨45, by decide⟩)]
def separateWord : List (Fin 15360 × Fin 15360) := [(1,⟨14, by decide⟩),(⟨14, by decide⟩,⟨23, by decide⟩),(⟨23, by decide⟩,⟨45, by decide⟩),(0,1),(1,⟨14, by decide⟩),(⟨14, by decide⟩,⟨23, by decide⟩),(⟨23, by decide⟩,⟨45, by decide⟩)]
def reversedWord : List (Fin 15360 × Fin 15360) := [(⟨23, by decide⟩,⟨45, by decide⟩),(⟨14, by decide⟩,⟨23, by decide⟩),(1,⟨14, by decide⟩),(0,1)]

theorem port_disequalities :
    (0 : Fin 15360) ≠ (1 : Fin 15360) ∧
    (0 : Fin 15360) ≠ (⟨14, by decide⟩ : Fin 15360) ∧
    (0 : Fin 15360) ≠ (⟨23, by decide⟩ : Fin 15360) ∧
    (0 : Fin 15360) ≠ (⟨45, by decide⟩ : Fin 15360) ∧
    (1 : Fin 15360) ≠ (⟨14, by decide⟩ : Fin 15360) ∧
    (1 : Fin 15360) ≠ (⟨23, by decide⟩ : Fin 15360) ∧
    (1 : Fin 15360) ≠ (⟨45, by decide⟩ : Fin 15360) ∧
    (⟨14, by decide⟩ : Fin 15360) ≠ (⟨23, by decide⟩ : Fin 15360) ∧
    (⟨14, by decide⟩ : Fin 15360) ≠ (⟨45, by decide⟩ : Fin 15360) ∧
    (⟨23, by decide⟩ : Fin 15360) ≠ (⟨45, by decide⟩ : Fin 15360) := by decide

/-- Exact native response of the finite captured aggregate route. Support
membership of its edges is checked separately against the pinned capture. -/
theorem aggregate_response (x : Fin 2 → ℝ) :
    wordMap aggregateWord (preparation x) ⟨45, by decide⟩ = (x 0+x 1)/16 := by
  obtain ⟨h01,h02,h03,h04,h12,h13,h14,h23,h24,h34⟩ := port_disequalities
  norm_num [h01,h02,h03,h04,h12,h13,h14,h23,h24,h34,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34,wordMap,aggregateWord,preparation,coordinate,pairAverage]
  ring

theorem separate_first_response (x : Fin 2 → ℝ) :
    wordMap (separateWord.take 3) (preparation x) ⟨45, by decide⟩ = x 1/8 := by
  obtain ⟨h01,h02,h03,h04,h12,h13,h14,h23,h24,h34⟩ := port_disequalities
  norm_num [h01,h02,h03,h04,h12,h13,h14,h23,h24,h34,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34,wordMap,separateWord,preparation,coordinate,pairAverage]
  ring

theorem separate_final_response (x : Fin 2 → ℝ) :
    wordMap separateWord (preparation x) ⟨45, by decide⟩ = x 0/16+5*x 1/32 := by
  obtain ⟨h01,h02,h03,h04,h12,h13,h14,h23,h24,h34⟩ := port_disequalities
  norm_num [h01,h02,h03,h04,h12,h13,h14,h23,h24,h34,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34,wordMap,separateWord,preparation,coordinate,pairAverage]
  ring

theorem separate_record_decoder (x : Fin 2 → ℝ) :
    16*wordMap separateWord (preparation x) ⟨45, by decide⟩ -
      20*wordMap (separateWord.take 3) (preparation x) ⟨45, by decide⟩ = x 0 ∧
    8*wordMap (separateWord.take 3) (preparation x) ⟨45, by decide⟩ = x 1 := by
  rw [separate_first_response,separate_final_response]
  constructor <;> ring

theorem reversed_response (x : Fin 2 → ℝ) :
    wordMap reversedWord (preparation x) ⟨45, by decide⟩ = 0 := by
  obtain ⟨h01,h02,h03,h04,h12,h13,h14,h23,h24,h34⟩ := port_disequalities
  norm_num [h01,h02,h03,h04,h12,h13,h14,h23,h24,h34,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34,wordMap,reversedWord,preparation,coordinate,pairAverage]

/-- The two initial preparations differ. Their first mean is identical
at every scalar port. -/
theorem prepared_pair_erased :
    pairAverage (0 : Fin 15360) 1 (preparation ![1,0]) =
      pairAverage (0 : Fin 15360) 1 (preparation ![0,1]) := by
  ext p
  by_cases hp : p=0
  · subst p; norm_num [pairAverage,preparation,coordinate]
  by_cases hq : p=1
  · subst p; norm_num [pairAverage,preparation,coordinate]
  simp [pairAverage,preparation,coordinate,hp,hq]

theorem prepared_pair_initial_receiver :
    preparation ![1,0] (⟨45, by decide⟩ : Fin 15360) = preparation ![0,1] (⟨45, by decide⟩ : Fin 15360) := by
  obtain ⟨h01,h02,h03,h04,h12,h13,h14,h23,h24,h34⟩ := port_disequalities
  norm_num [h01,h02,h03,h04,h12,h13,h14,h23,h24,h34,Ne.symm h01,Ne.symm h02,Ne.symm h03,Ne.symm h04,Ne.symm h12,Ne.symm h13,Ne.symm h14,Ne.symm h23,Ne.symm h24,Ne.symm h34,preparation,coordinate]

end
end OPH.SourceTemporalErasure

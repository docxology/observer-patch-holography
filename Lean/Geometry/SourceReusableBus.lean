module
public import Geometry.SourceEncodedMemory

@[expose] public section

/-!
# Finite reusable paired-rail bus

The ideal operations are scalar pair means. Preparation, isolation, schedule,
rail embedding and readout are inputs. A four-cell bus contracts toward its
encoded blank under a seven-mean sweep. Logical payload errors include the
cleanup residual and any separately bounded implementation perturbations.
-/

set_option autoImplicit false

namespace OPH.SourceReusableBus
noncomputable section
open OPH.SourceEncodedMemory

variable {ι : Type*} [DecidableEq ι]

inductive Instruction (ι : Type*) where
  | copy (source target : ι)
  | clear (cell : ι)

def word : Instruction ι → List ((ι × Bool) × (ι × Bool))
  | .copy s t => copyWord s t
  | .clear s => clearWord s

def step : Instruction ι → (ι → ℝ) → (ι → ℝ)
  | .copy s t, a => copied s t a
  | .clear s, a => cleared s a

def compile : List (Instruction ι) → List ((ι × Bool) × (ι × Bool))
  | [] => []
  | op :: ops => word op ++ compile ops

def execute : List (Instruction ι) → (ι → ℝ) → (ι → ℝ)
  | [], a => a
  | op :: ops, a => execute ops (step op a)

theorem instruction_native (op : Instruction ι) (b : ℝ) (a : ι → ℝ) :
    run (word op) (encode b a) = encode b (step op a) := by
  cases op with
  | copy s t => exact copy_native s t b a
  | clear s => exact clear_native s b a

theorem program_native (ops : List (Instruction ι)) (b : ℝ) (a : ι → ℝ) :
    run (compile ops) (encode b a) = encode b (execute ops a) := by
  induction ops generalizing a with
  | nil => rfl
  | cons op ops ih =>
    rw [compile, run_append, instruction_native, ih]
    rfl

omit [DecidableEq ι] in
theorem compile_append (u v : List (Instruction ι)) :
    compile (u++v) = compile u ++ compile v := by
  induction u with
  | nil => rfl
  | cons op ops ih => simp [compile, ih, List.append_assoc]

def forward : List (Instruction (Fin 6)) := [.copy 2 3, .copy 3 4, .copy 4 5]
def scrub : List (Instruction (Fin 6)) := .clear 2 :: forward

def scrubbed (a : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![a 0, a 1, a 3/2, a 3/4+a 4/2,
    a 3/8+a 4/4+a 5/2, a 3/8+a 4/4+a 5/2]

theorem scrub_formula (a : Fin 6 → ℝ) : execute scrub a = scrubbed a := by
  ext i
  fin_cases i <;> simp [execute, scrub, forward, step, copied, cleared, scrubbed] <;> ring

theorem forward_receiver (a : Fin 6 → ℝ) :
    execute forward a 5 = a 2/8+a 3/8+a 4/4+a 5/2 := by
  simp [execute, forward, step, copied]
  ring

theorem scrub_native (b : ℝ) (a : Fin 6 → ℝ) :
    run (compile scrub) (encode b a) = encode b (scrubbed a) := by
  rw [program_native, scrub_formula]

theorem scrub_length : (compile scrub).length = 7 := by rfl
theorem forward_length : (compile forward).length = 6 := by rfl

def BusBound (E : ℝ) (a : Fin 6 → ℝ) : Prop :=
  |a 2| ≤ E ∧ |a 3| ≤ E ∧ |a 4| ≤ E ∧ |a 5| ≤ E

theorem scrub_contraction (a : Fin 6 → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (h : BusBound E a) : BusBound ((7/8:ℝ)*E) (execute scrub a) := by
  rw [scrub_formula]
  obtain ⟨h2,h3,h4,h5⟩ := h
  have h3' := abs_le.mp h3
  have h4' := abs_le.mp h4
  have h5' := abs_le.mp h5
  dsimp [BusBound, scrubbed]
  constructor
  · apply abs_le.mpr; constructor <;> linarith
  constructor
  · apply abs_le.mpr; constructor <;> linarith
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem scrub_archives (a : Fin 6 → ℝ) :
    execute scrub a 0 = a 0 ∧ execute scrub a 1 = a 1 := by
  simp [scrub_formula, scrubbed]

def clean : ℕ → (Fin 6 → ℝ) → (Fin 6 → ℝ)
  | 0, a => a
  | n+1, a => clean n (execute scrub a)

def cleaning : ℕ → List (Instruction (Fin 6))
  | 0 => []
  | n+1 => scrub ++ cleaning n

theorem cleaning_length (n : ℕ) : (compile (cleaning n)).length = 7*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cleaning, compile_append, List.length_append, scrub_length, ih]
    omega

def readCycle (s : Fin 6) (n : ℕ) : List (Instruction (Fin 6)) :=
  [.copy s 2] ++ forward ++ cleaning n

theorem readCycle_length (s : Fin 6) (n : ℕ) :
    (compile (readCycle s n)).length = 8+7*n := by
  simp [readCycle, compile_append, compile, word, copyWord, forward_length, cleaning_length]
  omega

theorem execute_append (u v : List (Instruction ι)) (a : ι → ℝ) :
    execute (u++v) a = execute v (execute u a) := by
  induction u generalizing a with
  | nil => rfl
  | cons op ops ih => exact ih _

theorem cleaning_native (n : ℕ) (b : ℝ) (a : Fin 6 → ℝ) :
    run (compile (cleaning n)) (encode b a) = encode b (clean n a) := by
  rw [program_native]
  congr 1
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simpa only [cleaning, execute_append, clean] using ih (execute scrub a)

theorem clean_bound (n : ℕ) (a : Fin 6 → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (h : BusBound E a) : BusBound ((7/8:ℝ)^n*E) (clean n a) := by
  induction n generalizing a E with
  | zero => simpa [clean] using h
  | succ n ih =>
    have hb := ih (execute scrub a) ((7/8:ℝ)*E) (by positivity)
      (scrub_contraction a E hE h)
    simpa [clean, pow_succ, mul_assoc] using hb

theorem clean_archives (n : ℕ) (a : Fin 6 → ℝ) :
    clean n a 0 = a 0 ∧ clean n a 1 = a 1 := by
  induction n generalizing a with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    have hi := ih (execute scrub a)
    have hs := scrub_archives a
    exact ⟨hi.1.trans hs.1, hi.2.trans hs.2⟩

theorem export_error (s r a E ε : ℝ) (hs : |s-a| ≤ E) (hr : |r| ≤ ε) :
    |(s+r)/2-a/2| ≤ (E+ε)/2 := by
  have hs' := abs_le.mp hs
  have hr' := abs_le.mp hr
  apply abs_le.mpr
  constructor <;> linarith

def retained (a : ℝ) (residual : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | n+1 => (retained a residual n + residual n)/2

theorem retained_error (a ε : ℝ) (residual : ℕ → ℝ)
    (h : ∀ n, |residual n| ≤ ε) (n : ℕ) :
    |retained a residual n-a/(2:ℝ)^n| ≤ ε*(1-1/(2:ℝ)^n) := by
  induction n with
  | zero => simp [retained]
  | succ n ih =>
    have hb := export_error (retained a residual n) (residual n)
      (a/(2:ℝ)^n) (ε*(1-1/(2:ℝ)^n)) ε ih (h n)
    have he : (ε*(1-1/(2:ℝ)^n)+ε)/2 = ε*(1-1/(2:ℝ)^(n+1)) := by
      rw [pow_succ]; field_simp; ring
    rw [he] at hb
    simpa only [retained, pow_succ, div_div] using hb

theorem receiver_error (a : Fin 6 → ℝ) (reference ε : ℝ)
    (h2 : |a 2-reference| ≤ ε) (h3 : |a 3| ≤ ε)
    (h4 : |a 4| ≤ ε) (h5 : |a 5| ≤ ε) :
    |execute forward a 5-reference/8| ≤ ε := by
  rw [forward_receiver]
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  have h4' := abs_le.mp h4
  have h5' := abs_le.mp h5
  apply abs_le.mpr
  constructor <;> linarith

theorem contrast_error (b a p m E : ℝ)
    (hp : |p-(b+a)| ≤ E) (hm : |m-(b-a)| ≤ E) :
    |(p-m)/2-a| ≤ E := by
  have hp' := abs_le.mp hp
  have hm' := abs_le.mp hm
  apply abs_le.mpr
  constructor <;> linarith

/-- Compose native compilation, arbitrary signed per-step error, local readout
error and an ideal transfer estimate. The error bounds are hypotheses. -/
theorem program_readout_error (ops : List (Instruction ι)) (receiver : ι)
    (b reference E δ ρ ε : ℝ) (a : ι → ℝ) (x : ι × Bool → ℝ) (p m : ℝ)
    (es : List (((ι × Bool) × (ι × Bool)) × ((ι × Bool) → ℝ)))
    (hword : es.map Prod.fst = compile ops)
    (hx : Near E x (encode b a))
    (he : ∀ en ∈ es, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun es x (receiver, false)| ≤ ρ)
    (hm : |m-noisyRun es x (receiver, true)| ≤ ρ)
    (hideal : |execute ops a receiver-reference| ≤ ε) :
    |(p-m)/2-reference| ≤ ε + E + (compile ops).length*δ + ρ := by
  have hn := noisy_run_bound es x (encode b a) E δ hx he
  have hlen : es.length = (compile ops).length := by
    simpa using congrArg List.length hword
  rw [hlen, hword, program_native] at hn
  have hpos := abs_add_le (p-noisyRun es x (receiver, false))
    (noisyRun es x (receiver, false)-(b+execute ops a receiver))
  have hneg := abs_add_le (m-noisyRun es x (receiver, true))
    (noisyRun es x (receiver, true)-(b-execute ops a receiver))
  rw [sub_add_sub_cancel] at hpos hneg
  have hnp : |noisyRun es x (receiver, false)-(b+execute ops a receiver)| ≤
      E+(compile ops).length*δ := by simpa [encode] using hn (receiver, false)
  have hnm : |noisyRun es x (receiver, true)-(b-execute ops a receiver)| ≤
      E+(compile ops).length*δ := by simpa [encode, sub_eq_add_neg] using hn (receiver, true)
  have hc := contrast_error b (execute ops a receiver) p m
    (E+(compile ops).length*δ+ρ) (by linarith) (by linarith)
  have ht := abs_add_le ((p-m)/2-execute ops a receiver)
    (execute ops a receiver-reference)
  rw [sub_add_sub_cancel] at ht
  linarith

theorem separated_readouts (x y observation radius : ℝ)
    (hsep : 2*radius ≤ |x-y|) (hx : |observation-x| < radius)
    (hy : |observation-y| < radius) : False := by
  have ht := abs_add_le (x-observation) (observation-y)
  rw [sub_add_sub_cancel] at ht
  rw [abs_sub_comm x observation] at ht
  linarith

/-- Nearest integer to half an integer, with ties resolved toward even. -/
def roundedHalf (z : ℤ) : ℤ := z / 2 + if z % 4 = 3 then 1 else 0

theorem roundedHalf_integer_error (z : ℤ) : |2*roundedHalf z-z| ≤ 1 := by
  unfold roundedHalf
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

theorem roundedHalf_error (z : ℤ) (Q : ℝ) (hQ : 0 < Q) :
    |(roundedHalf z : ℝ)/Q - (z : ℝ)/(2*Q)| ≤ 1/(2*Q) := by
  have hb : |2*(roundedHalf z : ℝ)-(z : ℝ)| ≤ 1 := by
    exact_mod_cast roundedHalf_integer_error z
  have he : (roundedHalf z : ℝ)/Q - (z : ℝ)/(2*Q) =
      (2*(roundedHalf z : ℝ)-(z : ℝ))/(2*Q) := by ring
  rw [he, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Q)]
  exact div_le_div_of_nonneg_right hb (by positivity)

theorem roundedHalf_between (u v : ℤ) (h : u ≤ v) :
    u ≤ roundedHalf (u+v) ∧ roundedHalf (u+v) ≤ v := by
  unfold roundedHalf
  split_ifs <;> constructor <;> omega

end
end OPH.SourceReusableBus

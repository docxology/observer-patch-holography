module
public import Geometry.SourceNativeAccumulator
public import Geometry.SourceReadAcceptance

@[expose] public section

/-!
# Finite native accumulation programs and publication

The request lists and retirement of the mutable accumulator are supplied.
Input records retain their logical values across all episodes. All scalar
means, preparation error, disturbances and readout uncertainty remain in
the whole-program estimate; clearing does not refresh its error allowance.
-/

set_option autoImplicit false

namespace OPH.SourceAccumulatorProgram
noncomputable section
open OPH.SourceNativeAccumulator OPH.SourceEncodedMemory OPH.SourceReusableBus

def Valid (ps : List (List ℕ)) : Prop := ∀ ss ∈ ps, ∀ s ∈ ss, 2 ≤ s

def programScales : List (List ℕ) → (ℕ → ℕ) → (ℕ → ℕ)
  | [], e => e
  | ss::ps, e => programScales ps (episodeScales ss e)

def programValues : List (List ℕ) → (ℕ → ℝ) → (ℕ → ℝ)
  | [], v => v
  | ss::ps, v => programValues ps (episodeValues ss v)

def programWord : List (List ℕ) → (ℕ → ℕ) → List ((ℕ × Bool) × (ℕ × Bool))
  | [], _ => []
  | ss::ps, e => episodeWord ss e ++ programWord ps (episodeScales ss e)

/-- Actual whole-word composition, including every accumulator retirement,
native clear, seed export and scale-aligned addition. -/
theorem program_native (ps : List (List ℕ)) (hv : Valid ps)
    (b : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ) :
    run (programWord ps e) (encode b (represented v e)) =
      encode b (represented (programValues ps v) (programScales ps e)) := by
  induction ps generalizing v e with
  | nil => rfl
  | cons ss ps ih =>
    rw [programWord, run_append, episode_native ss (hv ss (by simp))]
    exact ih (fun ts ht => hv ts (by simp [ht])) _ _

theorem program_input_records (ps : List (List ℕ)) (v : ℕ → ℝ)
    (i : ℕ) (hi : 2 ≤ i) : programValues ps v i = v i := by
  induction ps generalizing v with
  | nil => rfl
  | cons ss ps ih =>
    rw [programValues, ih, episode_inputs ss v i hi]

theorem program_values_append (ps qs : List (List ℕ)) (v : ℕ → ℝ) :
    programValues (ps++qs) v = programValues qs (programValues ps v) := by
  induction ps generalizing v with
  | nil => rfl
  | cons ss ps ih => simpa [programValues] using ih (episodeValues ss v)

/-- The last result depends on the original retained inputs, even after
arbitrarily many earlier episodes have consumed their raw amplitudes. -/
theorem program_last_sum (ps : List (List ℕ)) (ss : List ℕ)
    (hs : ∀ s ∈ ss, 2 ≤ s) (v : ℕ → ℝ) :
    programValues (ps++[ss]) v 0 = v 2+(ss.map v).sum := by
  rw [program_values_append]
  change episodeValues ss (programValues ps v) 0 = _
  rw [episode_sum ss hs, program_input_records ps v 2 (by decide)]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  exact program_input_records ps v i (hs i hi)

theorem program_last_integer (ps : List (List ℕ)) (ss : List ℕ)
    (hs : ∀ s ∈ ss, 2 ≤ s) (g : ℝ) (z : ℕ → ℤ) :
    programValues (ps++[ss]) (fun i => g*(z i:ℝ)) 0 =
      g*((z 2+(ss.map z).sum:ℤ):ℝ) := by
  rw [program_last_sum ps ss hs]
  have hm : (ss.map (fun i => g*(z i:ℝ))).sum = g*((ss.map z).sum:ℤ) := by
    clear hs
    induction ss with
    | nil => simp
    | cons s ss ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]
      ring
  rw [hm]
  push_cast
  ring

theorem episode_scales_bound (ss : List ℕ) (e : ℕ → ℕ) (M : ℕ)
    (h : ∀ i, e i ≤ M) : ∀ i, episodeScales ss e i ≤ M+1+2*ss.length :=
  accumulated_scales_bound ss _ (M+1) (started_scales_bound e M h)

def requestCount (ps : List (List ℕ)) : ℕ := (ps.map List.length).sum

theorem program_scales_bound (ps : List (List ℕ)) (e : ℕ → ℕ) (M : ℕ)
    (h : ∀ i, e i ≤ M) :
    ∀ i, programScales ps e i ≤ M+ps.length+2*requestCount ps := by
  induction ps generalizing e M with
  | nil => simpa [programScales, requestCount] using h
  | cons ss ps ih =>
    have hb := ih (episodeScales ss e) (M+1+2*ss.length)
      (episode_scales_bound ss e M h)
    intro i
    have := hb i
    simp only [programScales, requestCount, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem episode_cost_bound (ss : List ℕ) (e : ℕ → ℕ) (M : ℕ)
    (h : ∀ i, e i ≤ M) :
    (episodeWord ss e).length ≤ 6+ss.length*(3*M+3*ss.length+8) := by
  have hb := accumulation_cost_bound ss (startedScales e) (M+1)
    (started_scales_bound e M h)
  simp only [episodeWord, List.length_append, start_length]
  nlinarith

/-- A finite polynomial work bound with the complete native word as its
left side. Controller metadata and physical publication have separate costs. -/
theorem program_cost_bound (ps : List (List ℕ)) (e : ℕ → ℕ) (M : ℕ)
    (h : ∀ i, e i ≤ M) :
    (programWord ps e).length ≤ 6*ps.length +
      requestCount ps*(8+3*(M+ps.length+2*requestCount ps)) := by
  induction ps generalizing e M with
  | nil => simp [programWord, requestCount]
  | cons ss ps ih =>
    have he := episode_cost_bound ss e M h
    have ht := ih (episodeScales ss e) (M+1+2*ss.length)
      (episode_scales_bound ss e M h)
    simp only [programWord, List.length_append, requestCount,
      List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith [Nat.zero_le (ss.length * ps.length),
      Nat.zero_le (ss.length * (ps.map List.length).sum)]

def remoteRead : List (Instruction ℕ) :=
  [.copy 0 1, .copy 1 4, .copy 4 5, .copy 5 6]

theorem remote_receiver (a : ℕ → ℝ)
    (h1 : a 1 = 0) (h4 : a 4 = 0) (h5 : a 5 = 0) (h6 : a 6 = 0) :
    execute remoteRead a 6 = a 0/16 := by
  simp [remoteRead, execute, step, copied, h1, h4, h5, h6]
  ring

theorem remote_source (a : ℕ → ℝ) (h1 : a 1 = 0) :
    execute remoteRead a 0 = a 0/2 := by
  simp [remoteRead, execute, step, copied, h1]

theorem remote_inputs (a : ℕ → ℝ) :
    execute remoteRead a 2 = a 2 ∧ execute remoteRead a 3 = a 3 := by
  simp [remoteRead, execute, step, copied]

theorem remote_length : (compile remoteRead).length = 8 := rfl

theorem program_workspace (ps : List (List ℕ)) (v : ℕ → ℝ) (h : v 1 = 0) :
    programValues ps v 1 = 0 := by
  induction ps generalizing v with
  | nil => exact h
  | cons ss ps ih =>
    apply ih
    simp [episodeValues, accumulated_input ss _ 1 (by decide), startedValues]

/-- The final result reaches the captured receiver through eight further
means. Its additional factor sixteen is retained in the decoding scale. -/
theorem program_remote_native (ps : List (List ℕ)) (hv : Valid ps)
    (b : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ)
    (h1 : v 1 = 0) (h4 : v 4 = 0) (h5 : v 5 = 0) (h6 : v 6 = 0) :
    run (programWord ps e ++ compile remoteRead) (encode b (represented v e)) =
      encode b (execute remoteRead (represented (programValues ps v) (programScales ps e))) ∧
    execute remoteRead (represented (programValues ps v) (programScales ps e)) 6 =
      programValues ps v 0/(2:ℝ)^(programScales ps e 0+4) := by
  constructor
  · rw [run_append, program_native ps hv, OPH.SourceReusableBus.program_native]
  · rw [remote_receiver _
      (by simp [represented, program_workspace ps v h1])
      (by simp [represented, program_input_records ps v 4 (by decide), h4])
      (by simp [represented, program_input_records ps v 5 (by decide), h5])
      (by simp [represented, program_input_records ps v 6 (by decide), h6])]
    norm_num [represented, pow_add, div_div]

theorem native_word_readout_error
    (word : List ((ℕ × Bool) × (ℕ × Bool))) (b E δ ρ : ℝ)
    (initial final : ℕ → ℝ) (x : ℕ × Bool → ℝ) (receiver : ℕ) (p m : ℝ)
    (noisy : List (((ℕ × Bool) × (ℕ × Bool)) × ((ℕ × Bool) → ℝ)))
    (hideal : run word (encode b initial) = encode b final)
    (hword : noisy.map Prod.fst = word) (hx : Near E x (encode b initial))
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (receiver,false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (receiver,true)| ≤ ρ) :
    |(p-m)/2-final receiver| ≤ E+word.length*δ+ρ := by
  have hn := noisy_run_bound noisy x (encode b initial) E δ hx he
  have hlen : noisy.length = word.length := by simpa using congrArg List.length hword
  rw [hword, hideal, hlen] at hn
  have ha := hn (receiver,false)
  have hb := hn (receiver,true)
  simp only [encode, Bool.false_eq_true, ite_false, ite_true] at ha hb
  have hap := abs_add_le (p-noisyRun noisy x (receiver,false))
    (noisyRun noisy x (receiver,false)-(b+final receiver))
  have hbm := abs_add_le (m-noisyRun noisy x (receiver,true))
    (noisyRun noisy x (receiver,true)-(b-final receiver))
  rw [sub_add_sub_cancel] at hap hbm
  have hb' : |noisyRun noisy x (receiver,true)-(b-final receiver)| ≤
      E+word.length*δ := by simpa [sub_eq_add_neg] using hb
  exact contrast_error b (final receiver) p m (E+word.length*δ+ρ)
    (by linarith) (by linarith)

/-- Arbitrary signed errors are charged over the whole program. Every
input record can also be checked by choosing its register as receiver. -/
theorem program_readout_error (ps : List (List ℕ)) (hv : Valid ps)
    (b E δ ρ : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ)
    (x : ℕ × Bool → ℝ) (receiver : ℕ) (p m : ℝ)
    (noisy : List (((ℕ × Bool) × (ℕ × Bool)) × ((ℕ × Bool) → ℝ)))
    (hword : noisy.map Prod.fst = programWord ps e)
    (hx : Near E x (encode b (represented v e)))
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (receiver,false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (receiver,true)| ≤ ρ) :
    |(p-m)/2-programValues ps v receiver/(2:ℝ)^(programScales ps e receiver)| ≤
      E+(programWord ps e).length*δ+ρ :=
  native_word_readout_error _ b E δ ρ _ _ x receiver p m noisy
    (program_native ps hv b v e) hword hx he hp hm

theorem integer_identification (z radius : ℝ) (k j : ℤ)
    (hsmall : 2*radius < 1) (hk : |z-k| ≤ radius) (hj : |z-j| ≤ radius) : j = k := by
  have ht := abs_add_le ((j:ℝ)-z) (z-k)
  rw [sub_add_sub_cancel, abs_sub_comm (j:ℝ) z] at ht
  have hd : |((j-k:ℤ):ℝ)| < 1 := by push_cast; linarith
  have hi : |j-k| < 1 := by exact_mod_cast hd
  have hh := abs_lt.mp hi
  omega

theorem integer_publication (z radius : ℝ) (k : ℤ)
    (hsmall : 2*radius < 1) (hk : |z-k| ≤ radius) :
    OPH.SourceReadAcceptance.canonical (fun value : ℤ => fun obs : ℝ => |obs-value| ≤ radius) z = some k := by
  apply (OPH.SourceReadAcceptance.canonical_some_iff _ z k).mpr
  exact ⟨hk,fun j hj => integer_identification z radius k j hsmall hk hj⟩

/-- Decoding an attenuated record multiplies its complete error allowance by
the same gain as its observation. -/
theorem normalized_error (z g R : ℝ) (k : ℤ) (e : ℕ) (hg : 0 < g)
    (hz : |z-g*k/(2:ℝ)^e| ≤ R) :
    |((2:ℝ)^e/g)*z-k| ≤ ((2:ℝ)^e/g)*R := by
  have hp : (0:ℝ) < 2^e := by positivity
  have hid : ((2:ℝ)^e/g)*z-k = ((2:ℝ)^e/g)*(z-g*k/(2:ℝ)^e) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos (div_pos hp hg)]
  exact mul_le_mul_of_nonneg_left hz (le_of_lt (div_pos hp hg))

/-- Whole-program local publication: the hypothesis concerns the native
noisy word itself, not an ideal operation substituted for that word. -/
theorem program_remote_publication (ps : List (List ℕ)) (hv : Valid ps)
    (b E δ ρ g : ℝ) (v : ℕ → ℝ) (e : ℕ → ℕ) (k : ℤ)
    (x : ℕ × Bool → ℝ) (p m : ℝ)
    (noisy : List (((ℕ × Bool) × (ℕ × Bool)) × ((ℕ × Bool) → ℝ)))
    (h1 : v 1 = 0) (h4 : v 4 = 0) (h5 : v 5 = 0) (h6 : v 6 = 0)
    (hg : 0 < g) (hk : programValues ps v 0 = g*k)
    (hword : noisy.map Prod.fst = programWord ps e ++ compile remoteRead)
    (hx : Near E x (encode b (represented v e)))
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (6,false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (6,true)| ≤ ρ)
    (hsmall : 2*((2:ℝ)^(programScales ps e 0+4)/g)*
      (E+((programWord ps e).length+8)*δ+ρ) < 1) :
    OPH.SourceReadAcceptance.canonical
      (fun value : ℤ => fun obs : ℝ => |obs-value| ≤
        ((2:ℝ)^(programScales ps e 0+4)/g)*
          (E+((programWord ps e).length+8)*δ+ρ))
      (((2:ℝ)^(programScales ps e 0+4)/g)*((p-m)/2)) = some k := by
  obtain ⟨hideal, hreceiver⟩ := program_remote_native ps hv b v e h1 h4 h5 h6
  have herr := native_word_readout_error _ b E δ ρ _ _ x 6 p m noisy
    hideal hword hx he hp hm
  rw [hreceiver, hk] at herr
  simp only [List.length_append, remote_length] at herr
  apply integer_publication
  · nlinarith [hsmall]
  · apply normalized_error _ g _ k _ hg
    simpa only [Nat.cast_add, Nat.cast_ofNat] using herr

/-- For the certified finite-grid error model, a finite precision always
suffices. The strict inequality is the actual uniqueness margin. -/
theorem grid_margin (Q : ℝ) (W e : ℕ) (hq : 3 < Q)
    (hprecision : (4+5*(W:ℝ))*2^e < 4*(Q-3)) :
    2*((2:ℝ)^e / ((Q-3)/Q))*
      (1/(4*Q)+(W:ℝ)*(5/(8*Q))+1/(4*Q)) < 1 := by
  have hQ : Q ≠ 0 := ne_of_gt (by linarith)
  have hG : 0 < Q-3 := by linarith
  have hid : 2*((2:ℝ)^e / ((Q-3)/Q))*
      (1/(4*Q)+(W:ℝ)*(5/(8*Q))+1/(4*Q)) =
      ((4+5*(W:ℝ))*2^e)/(4*(Q-3)) := by
    field_simp
    ring
  rw [hid]
  exact (div_lt_one (by positivity)).mpr hprecision

/-- Native realization of `1 + sum(requested original inputs)`, including
arbitrary earlier accumulator episodes and the final noisy remote read.
The desired arithmetic result is derived here, not supplied as a hypothesis. -/
theorem native_recurrence_publication (ps : List (List ℕ)) (ss : List ℕ)
    (hv : Valid (ps++[ss])) (b E δ ρ g : ℝ) (z : ℕ → ℤ) (e : ℕ → ℕ)
    (x : ℕ × Bool → ℝ) (p m : ℝ)
    (noisy : List (((ℕ × Bool) × (ℕ × Bool)) × ((ℕ × Bool) → ℝ)))
    (h1 : z 1 = 0) (h2 : z 2 = 1) (h4 : z 4 = 0) (h5 : z 5 = 0) (h6 : z 6 = 0)
    (hg : 0 < g)
    (hword : noisy.map Prod.fst = programWord (ps++[ss]) e ++ compile remoteRead)
    (hx : Near E x (encode b (represented (fun i => g*(z i:ℝ)) e)))
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (6,false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (6,true)| ≤ ρ)
    (hsmall : 2*((2:ℝ)^(programScales (ps++[ss]) e 0+4)/g)*
      (E+((programWord (ps++[ss]) e).length+8)*δ+ρ) < 1) :
    OPH.SourceReadAcceptance.canonical
      (fun value : ℤ => fun obs : ℝ => |obs-value| ≤
        ((2:ℝ)^(programScales (ps++[ss]) e 0+4)/g)*
          (E+((programWord (ps++[ss]) e).length+8)*δ+ρ))
      (((2:ℝ)^(programScales (ps++[ss]) e 0+4)/g)*((p-m)/2)) =
      some (1+(ss.map z).sum) := by
  apply program_remote_publication (ps++[ss]) hv b E δ ρ g _ e _ x p m noisy
    (by simp [h1]) (by simp [h4]) (by simp [h5]) (by simp [h6]) hg
    _ hword hx he hp hm hsmall
  simpa [h2] using program_last_integer ps ss (hv ss (by simp)) g z

end
end OPH.SourceAccumulatorProgram

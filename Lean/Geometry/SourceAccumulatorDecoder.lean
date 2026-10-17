module
public import Geometry.SourceAccumulatorProgram

@[expose] public section

/-!
# Bounded integer decoder for native accumulation

The public integer bound restricts the possible payloads. The executable
closed-interval rule is identified with the canonical singleton policy,
including empty intervals, ambiguous intervals and both endpoints.
-/

set_option autoImplicit false

namespace OPH.SourceAccumulatorDecoder
noncomputable section
open OPH.SourceAccumulatorProgram OPH.SourceReadAcceptance
open OPH.SourceNativeAccumulator OPH.SourceEncodedMemory OPH.SourceReusableBus

def possible (radius : ℝ) (bound : ℤ) (value : ℤ) (obs : ℝ) : Prop :=
  |value| ≤ bound ∧ |obs-value| ≤ radius

def lower (obs radius : ℝ) (bound : ℤ) : ℤ := max (-bound) ⌈obs-radius⌉

def upper (obs radius : ℝ) (bound : ℤ) : ℤ := min bound ⌊obs+radius⌋

def decode (obs radius : ℝ) (bound : ℤ) : Option ℤ :=
  if lower obs radius bound = upper obs radius bound then
    some (lower obs radius bound) else none

theorem candidate_iff (obs radius : ℝ) (bound value : ℤ) :
    lower obs radius bound ≤ value ∧ value ≤ upper obs radius bound ↔
      possible radius bound value obs := by
  simp only [lower, upper, max_le_iff, le_min_iff, Int.ceil_le, Int.le_floor,
    possible, abs_le]
  constructor
  · rintro ⟨⟨hb, hl⟩, hu, hr⟩
    exact ⟨⟨hb, hu⟩, by constructor <;> linarith⟩
  · rintro ⟨⟨hb, hu⟩, hl, hr⟩
    exact ⟨⟨hb, by linarith⟩, hu, by linarith⟩

theorem decode_some_iff (obs radius : ℝ) (bound value : ℤ) :
    decode obs radius bound = some value ↔ Identifies (possible radius bound) obs value := by
  constructor
  · intro hd
    unfold decode at hd
    split_ifs at hd with he
    · cases Option.some.inj hd
      refine ⟨(candidate_iff _ _ _ _).mp ⟨le_rfl, le_of_eq he⟩, ?_⟩
      intro j hj
      have hh := (candidate_iff _ _ _ _).mpr hj
      omega
  · intro hi
    have hk := (candidate_iff _ _ _ _).mpr hi.1
    have hlu : lower obs radius bound ≤ upper obs radius bound := hk.1.trans hk.2
    have hl := hi.2 _ ((candidate_iff _ _ _ _).mp ⟨le_rfl, hlu⟩)
    have hu := hi.2 _ ((candidate_iff _ _ _ _).mp ⟨hlu, le_rfl⟩)
    simp [decode, hl, hu]

theorem decode_is_canonical (obs radius : ℝ) (bound : ℤ) :
    decode obs radius bound = canonical (possible radius bound) obs := by
  cases hd : decode obs radius bound with
  | some k => exact ((canonical_some_iff _ _ _).mpr ((decode_some_iff _ _ _ _).mp hd)).symm
  | none =>
    cases hc : canonical (possible radius bound) obs with
    | none => rfl
    | some k =>
      have hk := (decode_some_iff _ _ _ _).mpr ((canonical_some_iff _ _ _).mp hc)
      rw [hd] at hk
      cases hk

theorem decode_sound (radius : ℝ) (bound : ℤ) :
    Sound (possible radius bound) (fun obs => decode obs radius bound) := by
  intro k obs hk result hr
  exact ((decode_some_iff _ _ _ _).mp hr).2 k hk |>.symm

theorem decode_available (obs radius : ℝ) (bound k : ℤ)
    (hsmall : 2*radius < 1) (hk : |obs-k| ≤ radius) (hb : |k| ≤ bound) :
    decode obs radius bound = some k := by
  apply (decode_some_iff _ _ _ _).mpr
  exact ⟨⟨hb, hk⟩, fun j hj => integer_identification obs radius k j hsmall hk hj.2⟩

/-- The magnitude cap is a sum of public input bounds, independent of their
values. In the captured fixture the unit bound is one and payload bound two. -/
theorem recurrence_bound (ss : List ℕ) (z caps : ℕ → ℤ)
    (h : ∀ i ∈ ss, |z i| ≤ caps i) :
    |1+(ss.map z).sum| ≤ 1+(ss.map caps).sum := by
  have hs : |(ss.map z).sum| ≤ (ss.map caps).sum := by
    induction ss with
    | nil => simp
    | cons s ss ih =>
      have ht := ih (fun i hi => h i (by simp [hi]))
      have hh := h s (by simp)
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add hh ht)
  calc
    |1+(ss.map z).sum| ≤ |(1:ℤ)|+|(ss.map z).sum| := abs_add_le _ _
    _ ≤ 1+(ss.map caps).sum := by simpa using add_le_add_left hs 1

/-- The actual clipped interval rule publishes the derived recurrence.
Its public magnitude cap is obtained from input bounds, not from the answer. -/
theorem native_bounded_publication (ps : List (List ℕ)) (ss : List ℕ)
    (hv : Valid (ps++[ss])) (b E δ ρ g : ℝ) (z caps : ℕ → ℤ) (e : ℕ → ℕ)
    (x : ℕ × Bool → ℝ) (p m : ℝ)
    (noisy : List (((ℕ × Bool) × (ℕ × Bool)) × ((ℕ × Bool) → ℝ)))
    (h1 : z 1 = 0) (h2 : z 2 = 1) (h4 : z 4 = 0) (h5 : z 5 = 0) (h6 : z 6 = 0)
    (hg : 0 < g) (hcaps : ∀ i ∈ ss, |z i| ≤ caps i)
    (hword : noisy.map Prod.fst = programWord (ps++[ss]) e ++ compile remoteRead)
    (hx : Near E x (encode b (represented (fun i => g*(z i:ℝ)) e)))
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (6,false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (6,true)| ≤ ρ)
    (hsmall : 2*((2:ℝ)^(programScales (ps++[ss]) e 0+4)/g)*
      (E+((programWord (ps++[ss]) e).length+8)*δ+ρ) < 1) :
    decode (((2:ℝ)^(programScales (ps++[ss]) e 0+4)/g)*((p-m)/2))
      (((2:ℝ)^(programScales (ps++[ss]) e 0+4)/g)*
        (E+((programWord (ps++[ss]) e).length+8)*δ+ρ))
      (1+(ss.map caps).sum) = some (1+(ss.map z).sum) := by
  have hu := native_recurrence_publication ps ss hv b E δ ρ g z e x p m noisy
    h1 h2 h4 h5 h6 hg hword hx he hp hm hsmall
  have herr := ((canonical_some_iff _ _ _).mp hu).1
  apply decode_available
  · nlinarith [hsmall]
  · exact herr
  · exact recurrence_bound ss z caps hcaps

end
end OPH.SourceAccumulatorDecoder

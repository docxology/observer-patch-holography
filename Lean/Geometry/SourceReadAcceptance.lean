module
public import Geometry.SourceReadSelection
public import Geometry.SourceReusableBus

@[expose] public section

/-!
# Publication from observational distinguishability

The possible-observation relation is an input, derived independently of the
publication policy. The theorems characterize sound partial readout and its
native scalar realization; they do not derive the source grammar or an A3
cover, reference, physical comparator or mandatory publication instrument.
-/

set_option autoImplicit false

namespace OPH.SourceReadAcceptance
noncomputable section
open OPH.SourceEncodedMemory OPH.SourceReadSelection
open ObserverPatchHolography.ScalarSeamRepair

variable {Value Obs : Type*}

def Sound (possible : Value → Obs → Prop) (publish : Obs → Option Value) : Prop :=
  ∀ v o, possible v o → ∀ result, publish o = some result → result = v

def Identifies (possible : Value → Obs → Prop) (o : Obs) (v : Value) : Prop :=
  possible v o ∧ ∀ other, possible other o → other = v

theorem identifies_unique (possible : Value → Obs → Prop) (o : Obs) (v w : Value)
    (hv : Identifies possible o v) (hw : Identifies possible o w) : v = w :=
  hw.2 v hv.1

/-- Feasibility prevents vacuous acceptance of an impossible observation. -/
theorem sound_publication_identifies (possible : Value → Obs → Prop)
    (publish : Obs → Option Value) (hs : Sound possible publish)
    (o : Obs) (ho : ∃ v, possible v o) (result : Value)
    (hp : publish o = some result) : Identifies possible o result := by
  obtain ⟨v, hv⟩ := ho
  have h := hs v o hv result hp
  subst result
  exact ⟨hv, fun w hw => (hs w o hw v hp).symm⟩

def canonical (possible : Value → Obs → Prop) (o : Obs) : Option Value := by
  classical
  exact if h : ∃ v, Identifies possible o v then some (Classical.choose h) else none

theorem canonical_some_iff (possible : Value → Obs → Prop) (o : Obs) (v : Value) :
    canonical possible o = some v ↔ Identifies possible o v := by
  classical
  unfold canonical
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro he
      cases Option.some.inj he
      exact hc
    · intro hv
      exact congrArg some (identifies_unique possible o _ v hc hv)
  · simp only [false_iff]
    exact fun hv => h ⟨v, hv⟩

theorem canonical_sound (possible : Value → Obs → Prop) :
    Sound possible (canonical possible) := by
  intro v o hv result hp
  exact ((canonical_some_iff possible o result).mp hp).2 v hv |>.symm

theorem canonical_maximal (possible : Value → Obs → Prop)
    (publish : Obs → Option Value) (hs : Sound possible publish)
    (o : Obs) (ho : ∃ v, possible v o) (v : Value)
    (hp : publish o = some v) : canonical possible o = some v :=
  (canonical_some_iff possible o v).mpr
    (sound_publication_identifies possible publish hs o ho v hp)

theorem shared_observation_abstains (possible : Value → Obs → Prop)
    (publish : Obs → Option Value) (hs : Sound possible publish)
    (o : Obs) (v w : Value) (hv : possible v o) (hw : possible w o)
    (hne : v ≠ w) : publish o = none := by
  cases hp : publish o with
  | none => rfl
  | some result => exact (hne ((hs v o hv result hp).symm.trans
      (hs w o hw result hp))).elim

/-- Adding observed prefixes cannot erase an identification if the actual
payload remains feasible and the candidate set can only shrink. -/
theorem identification_refines (coarse fine : Value → Prop) (v : Value)
    (hc : ∀ w, coarse w → w = v) (hf : ∃ w, fine w)
    (hsub : ∀ w, fine w → coarse w) :
    fine v ∧ ∀ w, fine w → w = v := by
  obtain ⟨w, hw⟩ := hf
  have he := hc w (hsub w hw)
  subst w
  exact ⟨hw, fun w h => hc w (hsub w h)⟩

variable {ι : Type*} [DecidableEq ι]

theorem cut_transcript_abstains {R : Type*}
    (source : ι → Prop) (readPort : R → ι) (hr : ∀ r, ¬ source (readPort r))
    (es : List (ι × ι)) (hes : ∀ e ∈ es, NoCross source e)
    (x y : ι → ℝ) (hxy : ∀ i, ¬ source i → x i = y i)
    (possible : Value → (ℕ → R → ℝ) → Prop)
    (publish : (ℕ → R → ℝ) → Option Value) (hs : Sound possible publish)
    (v w : Value) (hne : v ≠ w)
    (hv : possible v (transcript es x readPort))
    (hw : possible w (transcript es y readPort)) :
    publish (transcript es x readPort) = none := by
  rw [← local_transcript_eq source readPort hr es hes x y hxy] at hw
  exact shared_observation_abstains possible publish hs _ v w hv hw hne

theorem run_affine (es : List (ι × ι)) (x : ι → ℝ) (b a : ℝ) :
    run es (fun i => b + a*x i) = fun i => b + a*run es x i := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    have step : pairAverage e.1 e.2 (fun i => b+a*x i) =
        fun i => b+a*pairAverage e.1 e.2 x i := by
      ext i
      by_cases hi : i = e.1 ∨ i = e.2
      · simp [pairAverage, hi]
        ring
      · simp [pairAverage, hi]
    simpa only [run, step] using ih (pairAverage e.1 e.2 x)

theorem run_upper_bound (es : List (ι × ι)) (x : ι → ℝ) (A : ℝ)
    (hx : ∀ i, x i ≤ A) : ∀ i, run es x i ≤ A := by
  have h := run_nonnegative es (fun i => A+(-1)*x i) (by intro i; linarith [hx i])
  rw [run_affine] at h
  intro i
  linarith [h i]

/-- A positive source coefficient cannot disappear under further means. -/
theorem mean_retains_positive (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (u v i : ι) (hi : 0 < x i) : 0 < pairAverage u v x i := by
  by_cases hu : i = u
  · subst i
    simpa [pairAverage] using (show 0 < (x u+x v)/2 by linarith [hx v])
  by_cases hv : i = v
  · subst i
    simpa [pairAverage] using (show 0 < (x u+x v)/2 by linarith [hx u])
  · simpa [pairAverage, hu, hv] using hi

theorem run_retains_positive (es : List (ι × ι)) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (i : ι) (hi : 0 < x i) : 0 < run es x i := by
  induction es generalizing x with
  | nil => exact hi
  | cons e es ih =>
    exact ih _ (run_nonnegative [e] x hx) (mean_retains_positive x hx e.1 e.2 i hi)

/-- Every nonzero coefficient has a finite-horizon lower bound. -/
theorem mean_gap (x : ι → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hx : ∀ i, x i = 0 ∨ m ≤ x i) (u v i : ι) :
    pairAverage u v x i = 0 ∨ m/2 ≤ pairAverage u v x i := by
  by_cases hi : i = u ∨ i = v
  · simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hi]
    rcases hx u with hu | hu <;> rcases hx v with hv | hv
    · left; rw [hu, hv]; ring
    all_goals right; linarith
  · simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hi]
    rcases hx i with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem run_gap (es : List (ι × ι)) (x : ι → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hx : ∀ i, x i = 0 ∨ m ≤ x i) :
    ∀ i, run es x i = 0 ∨ m/(2:ℝ)^es.length ≤ run es x i := by
  induction es generalizing x m with
  | nil => simpa [run] using hx
  | cons e es ih =>
    have h := ih (pairAverage e.1 e.2 x) (m/2) (by positivity)
      (mean_gap x m hm hx e.1 e.2)
    simpa [run, pow_succ, div_div, mul_comm] using h

/-- A supplied absolute error budget produces a local partial decoder.
None includes the exact threshold; zero is never interpreted as a payload. -/
def threshold (E z : ℝ) : Option Bool :=
  if E < z then some true else if z < -E then some false else none

theorem threshold_positive_sound (a E z : ℝ) (ha : 0 ≤ a)
    (h : |z+a| ≤ E) : threshold E z ≠ some true := by
  have hz := (abs_le.mp h).2
  have hn : ¬ E < z := by linarith
  simp [threshold, hn]

theorem threshold_negative_sound (a E z : ℝ) (ha : 0 ≤ a)
    (h : |z-a| ≤ E) : threshold E z ≠ some false := by
  have hz := (abs_le.mp h).1
  have hn : ¬ z < -E := by linarith
  simp [threshold, hn]

theorem threshold_positive_complete (a E z : ℝ) (ha : 2*E < a)
    (h : |z-a| ≤ E) : threshold E z = some true := by
  have hz := (abs_le.mp h).1
  have hp : E < z := by linarith
  simp [threshold, hp]

theorem threshold_negative_complete (a E z : ℝ) (hE : 0 ≤ E) (ha : 2*E < a)
    (h : |z+a| ≤ E) : threshold E z = some false := by
  have hz := (abs_le.mp h).2
  have hn : z < -E := by linarith
  have hp : ¬ E < z := by linarith
  simp [threshold, hp, hn]

theorem threshold_zero_abstains (E z : ℝ) (h : |z| ≤ E) :
    threshold E z = none := by
  have hh := abs_le.mp h
  simp [threshold, not_lt.mpr hh.2, not_lt.mpr hh.1]

/-- A shared receiver value at overlapping uncertainty intervals precludes
sound publication, including a randomized policy with its coins fixed. -/
theorem uncertainty_overlap (a E : ℝ) (ha : 0 ≤ a) (hE : a ≤ E) :
    |(0:ℝ)-a| ≤ E ∧ |(0:ℝ)+a| ≤ E := by
  simpa [abs_of_nonneg ha] using And.intro hE hE

/-- Observable intervals generated by an unknown nonnegative transfer gain
bounded by A and an absolute readout error E. This is a conservative
abstraction of the finite native word model, not an extra success constraint. -/
def ConePossible (A E : ℝ) (bit : Bool) (z : ℝ) : Prop :=
  if bit then -E ≤ z ∧ z ≤ A+E else -A-E ≤ z ∧ z ≤ E

def boundedThreshold (A E z : ℝ) : Option Bool :=
  if |z| ≤ A+E then threshold E z else none

theorem positive_identification (A E z : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Identifies (ConePossible A E) z true ↔ E < z ∧ z ≤ A+E := by
  simp only [Identifies, ConePossible, Bool.forall_bool, Bool.false_eq_true,
    ite_false, ite_true, imp_false, implies_true, and_true]
  constructor
  · rintro ⟨hz, hn⟩
    have hn' : ¬ z ≤ E := fun h => hn ⟨by linarith [hz.1],h⟩
    exact ⟨lt_of_not_ge hn',hz.2⟩
  · rintro ⟨hz, hu⟩
    exact ⟨⟨by linarith,hu⟩,fun h => (not_le_of_gt hz) h.2⟩

theorem negative_identification (A E z : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Identifies (ConePossible A E) z false ↔ z < -E ∧ -A-E ≤ z := by
  simp only [Identifies, ConePossible, Bool.forall_bool, Bool.false_eq_true,
    ite_false, ite_true, imp_false, Bool.true_eq_false, implies_true, true_and]
  constructor
  · rintro ⟨hz, hn⟩
    have hn' : ¬ -E ≤ z := fun h => hn ⟨h,by linarith [hz.2]⟩
    exact ⟨lt_of_not_ge hn',hz.1⟩
  · rintro ⟨hz, hl⟩
    exact ⟨⟨hl,by linarith⟩,fun h => (not_le_of_gt hz) h.1⟩

theorem bounded_positive_iff (A E z : ℝ) (_hA : 0 ≤ A) (hE : 0 ≤ E) :
    boundedThreshold A E z = some true ↔ E < z ∧ z ≤ A+E := by
  by_cases hb : |z| ≤ A+E
  · simp only [boundedThreshold, ite_eq_left hb]
    have bounds := abs_le.mp hb
    by_cases hp : E < z <;> simp [threshold, hp, bounds.2]
  · have hn : ¬ (E < z ∧ z ≤ A+E) := by
      rintro ⟨hp,hu⟩
      exact hb (abs_le.mpr ⟨by linarith,hu⟩)
    simp only [boundedThreshold, ite_eq_right hb, reduceCtorEq, false_iff]
    exact hn

theorem bounded_negative_iff (A E z : ℝ) (_hA : 0 ≤ A) (hE : 0 ≤ E) :
    boundedThreshold A E z = some false ↔ z < -E ∧ -A-E ≤ z := by
  by_cases hb : |z| ≤ A+E
  · simp only [boundedThreshold, ite_eq_left hb]
    have bounds := abs_le.mp hb
    have hl : -A-E ≤ z := by linarith [bounds.1]
    by_cases hp : E < z
    · have hn : ¬ z < -E := by linarith
      simp [threshold, hp, hn]
    · simp [threshold, hp, hl]
  · have hn : ¬ (z < -E ∧ -A-E ≤ z) := by
      rintro ⟨hp,hl⟩
      exact hb (abs_le.mpr ⟨by linarith,by linarith⟩)
    simp only [boundedThreshold, ite_eq_right hb, reduceCtorEq, false_iff]
    exact hn

/-- The executable interval rule is the maximal sound policy on the declared
uncertainty abstraction. Impossible observations and ambiguous ones abstain. -/
theorem bounded_is_canonical (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) (z : ℝ) :
    boundedThreshold A E z = canonical (ConePossible A E) z := by
  apply Option.ext
  intro bit
  rw [canonical_some_iff]
  cases bit
  · exact (bounded_negative_iff A E z hA hE).trans (negative_identification A E z hA hE).symm
  · exact (bounded_positive_iff A E z hA hE).trans (positive_identification A E z hA hE).symm

theorem positive_observation_possible (A E a z : ℝ) (ha : 0 ≤ a) (hA : a ≤ A)
    (hz : |z-a| ≤ E) : ConePossible A E true z := by
  have h := abs_le.mp hz
  simp only [ConePossible, ite_true]
  constructor <;> linarith

theorem negative_observation_possible (A E a z : ℝ) (ha : 0 ≤ a) (hA : a ≤ A)
    (hz : |z+a| ≤ E) : ConePossible A E false z := by
  have h := abs_le.mp hz
  simp only [ConePossible]
  constructor <;> linarith

/-- The interval relation is derived from a bounded gain and an absolute
error ball. Its definition does not insert a successful-output predicate. -/
theorem positive_interval_iff_gain (A E z : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    ConePossible A E true z ↔ ∃ gain, 0 ≤ gain ∧ gain ≤ A ∧ |z-gain| ≤ E := by
  constructor
  · intro h
    change -E ≤ z ∧ z ≤ A+E at h
    by_cases hn : z < 0
    · refine ⟨0, le_rfl, hA, ?_⟩
      apply abs_le.mpr
      constructor <;> linarith
    by_cases hu : A < z
    · refine ⟨A, hA, le_rfl, ?_⟩
      apply abs_le.mpr
      constructor <;> linarith
    · exact ⟨z, le_of_not_gt hn, le_of_not_gt hu, by simpa using hE⟩
  · rintro ⟨gain,hl,hu,hz⟩
    exact positive_observation_possible A E gain z hl hu hz

theorem negative_interval_iff_gain (A E z : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    ConePossible A E false z ↔ ∃ gain, 0 ≤ gain ∧ gain ≤ A ∧ |z+gain| ≤ E := by
  have he : ConePossible A E false z ↔ ConePossible A E true (-z) := by
    simp only [ConePossible]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [he, positive_interval_iff_gain A E (-z) hA hE]
  have habs (gain : ℝ) : |-z-gain| = |z+gain| := by
    rw [show -z-gain = -(z+gain) by ring, abs_neg]
  simp_rw [habs]

theorem bounded_policy_sound (A E : ℝ) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    Sound (ConePossible A E) (boundedThreshold A E) := by
  have he : boundedThreshold A E = canonical (ConePossible A E) :=
    funext (bounded_is_canonical A E hA hE)
  rw [he]
  exact canonical_sound _

/-- The guard cannot discard a valid noisy positive native observation.
Together with the negative version this connects the implemented bounded
policy, native transport and finite-horizon availability. -/
theorem bounded_native_positive (es : List (ι × ι)) (x : ι → ℝ) (A m E z : ℝ)
    (hA : 0 ≤ A) (hm : 0 ≤ m) (hE : 0 ≤ E)
    (hx : ∀ i, x i = 0 ∨ m ≤ x i) (hu : ∀ i, x i ≤ A)
    (receiver : ι) (harrive : run es x receiver ≠ 0)
    (hmargin : 2*E < m/(2:ℝ)^es.length)
    (hz : |z-run es x receiver| ≤ E) : boundedThreshold A E z = some true := by
  have hg := (run_gap es x m hm hx receiver).resolve_left harrive
  have hp := (abs_le.mp hz).1
  have hb := (abs_le.mp hz).2
  have hr := run_upper_bound es x A hu receiver
  apply (bounded_positive_iff A E z hA hE).mpr
  constructor <;> linarith

theorem bounded_native_negative (es : List (ι × ι)) (x : ι → ℝ) (A m E z : ℝ)
    (hA : 0 ≤ A) (hm : 0 ≤ m) (hE : 0 ≤ E)
    (hx : ∀ i, x i = 0 ∨ m ≤ x i) (hu : ∀ i, x i ≤ A)
    (receiver : ι) (harrive : run es x receiver ≠ 0)
    (hmargin : 2*E < m/(2:ℝ)^es.length)
    (hz : |z+run es x receiver| ≤ E) : boundedThreshold A E z = some false := by
  have hg := (run_gap es x m hm hx receiver).resolve_left harrive
  have hp := (abs_le.mp hz).1
  have hb := (abs_le.mp hz).2
  have hr := run_upper_bound es x A hu receiver
  apply (bounded_negative_iff A E z hA hE).mpr
  constructor <;> linarith

open OPH.SourceReusableBus

def paired (es : List (ι × ι)) : List (Instruction ι) :=
  es.map fun e => .copy e.1 e.2

theorem paired_execution (es : List (ι × ι)) (a : ι → ℝ) :
    execute (paired es) a = run es a := by
  induction es generalizing a with
  | nil => rfl
  | cons e es ih =>
    change execute (paired es) (copied e.1 e.2 a) = run es (copied e.1 e.2 a)
    exact ih (copied e.1 e.2 a)

theorem paired_native (es : List (ι × ι)) (b : ℝ) (a : ι → ℝ) :
    run (compile (paired es)) (encode b a) = encode b (run es a) := by
  rw [program_native, paired_execution]

omit [DecidableEq ι] in
theorem paired_cost (es : List (ι × ι)) : (compile (paired es)).length = 2*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [paired, compile, word, copyWord, Nat.mul_add] using ih

/-- The local contrast error includes preparation, both physical means per
checkpoint, arbitrary signed disturbance and both receiver sample errors. -/
theorem paired_readout_error (es : List (ι × ι)) (receiver : ι)
    (b E δ ρ : ℝ) (a : ι → ℝ) (x : ι × Bool → ℝ) (p m : ℝ)
    (noisy : List (((ι × Bool) × (ι × Bool)) × ((ι × Bool) → ℝ)))
    (hword : noisy.map Prod.fst = compile (paired es))
    (hx : Near E x (encode b a))
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (receiver, false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (receiver, true)| ≤ ρ) :
    |(p-m)/2-run es a receiver| ≤ E + (2*es.length:ℕ)*δ + ρ := by
  have h := program_readout_error (paired es) receiver b (run es a receiver)
    E δ ρ 0 a x p m noisy hword hx he hp hm (by simp [paired_execution])
  simpa [paired_cost] using h

def signed (bit : Bool) (a : ι → ℝ) : ι → ℝ := fun i => if bit then a i else -a i

theorem run_signed (es : List (ι × ι)) (a : ι → ℝ) (bit : Bool) :
    run es (signed bit a) = signed bit (run es a) := by
  cases bit
  · funext i
    change run es (fun i => -a i) i = -(run es a i)
    have h := congrFun (run_affine es a 0 (-1)) i
    simpa only [zero_add, neg_one_mul] using h
  · rfl

/-- End-to-end conditional service: all signed implementation errors are
charged, published results are sound, and nonzero source influence is
published under the explicit finite-horizon margin. The two payloads share
the same word, public decoder parameters and unsigned amplitude profile. -/
theorem paired_publication_contract (es : List (ι × ι)) (receiver : ι) (bit : Bool)
    (b A gap E δ ρ : ℝ) (a : ι → ℝ) (x : ι × Bool → ℝ) (p m : ℝ)
    (hA : 0 ≤ A) (hgap : 0 ≤ gap) (hE : 0 ≤ E) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (ha : ∀ i, 0 ≤ a i) (hu : ∀ i, a i ≤ A)
    (hg : ∀ i, a i = 0 ∨ gap ≤ a i)
    (noisy : List (((ι × Bool) × (ι × Bool)) × ((ι × Bool) → ℝ)))
    (hword : noisy.map Prod.fst = compile (paired es))
    (hx : Near E x (encode b (signed bit a)))
    (he : ∀ en ∈ noisy, ∀ i, |en.2 i| ≤ δ)
    (hp : |p-noisyRun noisy x (receiver, false)| ≤ ρ)
    (hm : |m-noisyRun noisy x (receiver, true)| ≤ ρ) :
    let radius := E + (2*es.length:ℕ)*δ + ρ
    let observation := (p-m)/2
    (∀ result, boundedThreshold A radius observation = some result → result = bit) ∧
    (run es a receiver ≠ 0 → 2*radius < gap/(2:ℝ)^es.length →
      boundedThreshold A radius observation = some bit) := by
  dsimp only
  let radius := E + (2*es.length:ℕ)*δ + ρ
  have hr : 0 ≤ radius := by dsimp [radius]; positivity
  have hz := paired_readout_error es receiver b E δ ρ (signed bit a) x p m
    noisy hword hx he hp hm
  rw [run_signed] at hz
  have hlow := run_nonnegative es a ha receiver
  have hhigh := run_upper_bound es a A hu receiver
  cases bit
  · have hneg : |(p-m)/2+run es a receiver| ≤ radius := by simpa [signed, radius] using hz
    constructor
    · exact bounded_policy_sound A radius hA hr false ((p-m)/2)
        (negative_observation_possible A radius _ _ hlow hhigh hneg)
    · intro arrive margin
      exact bounded_native_negative es a A gap radius ((p-m)/2)
        hA hgap hr hg hu receiver arrive margin hneg
  · have hpos : |(p-m)/2-run es a receiver| ≤ radius := by simpa [signed, radius] using hz
    constructor
    · exact bounded_policy_sound A radius hA hr true ((p-m)/2)
        (positive_observation_possible A radius _ _ hlow hhigh hpos)
    · intro arrive margin
      exact bounded_native_positive es a A gap radius ((p-m)/2)
        hA hgap hr hg hu receiver arrive margin hpos

/-- Safety for every native word, even when its signal is too small to read. -/
theorem native_positive_safety (es : List (ι × ι)) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (receiver : ι) (E z : ℝ)
    (hz : |z-run es a receiver| ≤ E) : threshold E z ≠ some false :=
  threshold_negative_sound _ E z (run_nonnegative es a ha receiver) hz

/-- Uniform finite-horizon separation supplies availability whenever influence
has reached the receiver. This does not assert that every word delivers it. -/
theorem native_positive_availability (es : List (ι × ι)) (a : ι → ℝ)
    (m : ℝ) (hm : 0 ≤ m) (ha : ∀ i, a i = 0 ∨ m ≤ a i)
    (receiver : ι) (harrive : run es a receiver ≠ 0) (E z : ℝ)
    (hmargin : 2*E < m/(2:ℝ)^es.length)
    (hz : |z-run es a receiver| ≤ E) : threshold E z = some true := by
  have hg := (run_gap es a m hm ha receiver).resolve_left harrive
  exact threshold_positive_complete _ E z (lt_of_lt_of_le hmargin hg) hz

theorem native_negative_availability (es : List (ι × ι)) (a : ι → ℝ)
    (m : ℝ) (hm : 0 ≤ m) (ha : ∀ i, a i = 0 ∨ m ≤ a i)
    (receiver : ι) (harrive : run es a receiver ≠ 0) (E z : ℝ) (hE : 0 ≤ E)
    (hmargin : 2*E < m/(2:ℝ)^es.length)
    (hz : |z+run es a receiver| ≤ E) : threshold E z = some false := by
  have hg := (run_gap es a m hm ha receiver).resolve_left harrive
  exact threshold_negative_complete _ E z hE (lt_of_lt_of_le hmargin hg) hz

theorem mean_positive_iff (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (u v i : ι) :
    0 < pairAverage u v x i ↔
      if i = u ∨ i = v then 0 < x u ∨ 0 < x v else 0 < x i := by
  by_cases hi : i = u ∨ i = v
  · simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_left hi]
    constructor
    · intro h
      by_contra hn
      push Not at hn
      linarith
    · intro h
      rcases h with h | h <;> linarith [hx u, hx v]
  · simp [pairAverage, hi]

/-- On a path, influence occupies a prefix. Only the unique edge at its
frontier advances that prefix, regardless of the analog amplitudes. -/
def advance (frontier move : ℕ) : ℕ := if move = frontier then frontier+1 else frontier

theorem prefix_step (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (frontier move : ℕ)
    (hp : ∀ i, 0 < x i ↔ i ≤ frontier) :
    ∀ i, 0 < pairAverage move (move+1) x i ↔ i ≤ advance frontier move := by
  intro i
  rw [mean_positive_iff x hx, hp, hp, hp]
  by_cases he : move = frontier
  · subst move
    simp only [advance]
    split_ifs <;> omega
  · simp only [advance, ite_eq_right he]
    split_ifs <;> omega

def progress : ℕ → List ℕ → ℕ
  | frontier, [] => frontier
  | frontier, move :: moves => progress (advance frontier move) moves

theorem path_frontier (moves : List ℕ) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i)
    (frontier : ℕ) (hp : ∀ i, 0 < x i ↔ i ≤ frontier) :
    ∀ i, 0 < run (moves.map fun j => (j,j+1)) x i ↔ i ≤ progress frontier moves := by
  induction moves generalizing x frontier with
  | nil => exact hp
  | cons move moves ih =>
    exact ih (pairAverage move (move+1) x) (run_nonnegative [(move,move+1)] x hx)
      (advance frontier move) (prefix_step x hx frontier move hp)

theorem source_path_frontier (moves : List ℕ) (amplitude : ℝ) (ha : 0 < amplitude) :
    ∀ i, 0 < run (moves.map fun j => (j,j+1)) (signal 0 amplitude) i ↔
      i ≤ progress 0 moves := by
  apply path_frontier
  · intro i; simp only [signal]; split_ifs <;> linarith
  · intro i; by_cases hi : i = 0 <;> simp [signal, hi, ha]

/-- Uniform event identities give exactly one advancing letter at every
unfinished frontier. This is a counting statement, not an A3 grammar claim. -/
theorem advancing_letter_count (d frontier : ℕ) (hf : frontier < d) :
    (∑ move : Fin d, if move.val = frontier then (1:ℕ) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single (⟨frontier,hf⟩ : Fin d)]
  · simp
  · intro b _ hb
    have h : b.val ≠ frontier := fun he => hb (Fin.ext he)
    simp [h]
  · simp

theorem uniform_frontier_sum (d frontier : ℕ) (hf : frontier < d) :
    (∑ move : Fin d, advance frontier move.val) = d*frontier+1 := by
  have he (move : Fin d) : advance frontier move.val =
      frontier + if move.val = frontier then 1 else 0 := by
    unfold advance; split_ifs <;> omega
  simp_rw [he]
  rw [Finset.sum_add_distrib, advancing_letter_count d frontier hf]
  simp

theorem completed_frontier_absorbs (d : ℕ) (move : Fin d) : advance d move.val = d := by
  simp [advance, ne_of_lt move.isLt]

end
end OPH.SourceReadAcceptance

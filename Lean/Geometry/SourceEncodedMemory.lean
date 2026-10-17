module
public import ObserverPatchHolography.ScalarSeamRepair

@[expose] public section

/-!
# Native balanced-rail copy and logical reset

All writes below are the existing scalar pair mean. The schedule, two-rail
support, preparation and sign comparator are inputs. Copying halves both
amplitudes; no physical gain, protected archive or refresh is supplied.
-/

set_option autoImplicit false

namespace OPH.SourceEncodedMemory
noncomputable section
open ObserverPatchHolography.ScalarSeamRepair

variable {ι : Type*} [DecidableEq ι]

def run : List (ι × ι) → (ι → ℝ) → (ι → ℝ)
  | [], x => x
  | e :: es, x => run es (pairAverage e.1 e.2 x)

theorem run_append (u v : List (ι × ι)) (x : ι → ℝ) :
    run (u ++ v) x = run v (run u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons e es ih => exact ih _

theorem run_nonnegative (word : List (ι × ι)) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ run word x i := by
  induction word generalizing x with
  | nil => exact hx
  | cons e es ih =>
    apply ih
    intro i
    by_cases h : i = e.1 ∨ i = e.2
    · simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, h, ite_true]
      exact div_nonneg (add_nonneg (hx e.1) (hx e.2)) (by norm_num)
    · simpa [pairAverage, h] using hx i

/-- False is the positive rail; true is the negative rail. -/
def encode (b : ℝ) (a : ι → ℝ) (p : ι × Bool) : ℝ :=
  b + if p.2 then -a p.1 else a p.1

def copyWord (s t : ι) : List ((ι × Bool) × (ι × Bool)) :=
  [((s, false), (t, false)), ((s, true), (t, true))]

def clearWord (s : ι) : List ((ι × Bool) × (ι × Bool)) :=
  [((s, false), (s, true))]

def copied (s t : ι) (a : ι → ℝ) (i : ι) : ℝ :=
  if i = s ∨ i = t then (a s + a t)/2 else a i

def cleared (s : ι) (a : ι → ℝ) (i : ι) : ℝ :=
  if i = s then 0 else a i

theorem copy_native (s t : ι) (b : ℝ) (a : ι → ℝ) :
    run (copyWord s t) (encode b a) = encode b (copied s t a) := by
  ext ⟨i, r⟩
  cases r <;> by_cases hs : i = s <;> by_cases ht : i = t <;>
    simp [run, copyWord, pairAverage, encode, copied, hs, ht] <;> ring

theorem clear_native (s : ι) (b : ℝ) (a : ι → ℝ) :
    run (clearWord s) (encode b a) = encode b (cleared s a) := by
  ext ⟨i, r⟩
  cases r <;> by_cases hs : i = s <;>
    simp [run, clearWord, pairAverage, encode, cleared, hs] <;> ring

omit [DecidableEq ι] in
theorem encode_nonnegative (b : ℝ) (a : ι → ℝ) (h : ∀ i, |a i| ≤ b) :
    ∀ p, 0 ≤ encode b a p := by
  rintro ⟨i, r⟩
  have hi := abs_le.mp (h i)
  cases r <;> simp [encode] <;> linarith

omit [DecidableEq ι] in
theorem encode_gap (b : ℝ) (a : ι → ℝ) (i : ι) :
    encode b a (i, false) - encode b a (i, true) = 2*a i := by
  simp [encode]
  ring

theorem blank_copy_source (s t : ι) (a : ι → ℝ) (ht : a t = 0) :
    copied s t a s = a s/2 := by simp [copied, ht]

theorem blank_copy_target (s t : ι) (a : ι → ℝ) (ht : a t = 0) :
    copied s t a t = a s/2 := by simp [copied, ht]

theorem blank_copy_sign (s t : ι) (a : ι → ℝ) (ht : a t = 0) :
    (0 < copied s t a s ↔ 0 < a s) ∧
    (0 < copied s t a t ↔ 0 < a s) := by
  rw [blank_copy_source s t a ht, blank_copy_target s t a ht]
  constructor <;> exact div_pos_iff_of_pos_right (by norm_num)

def signal (s : ι) (a : ℝ) (i : ι) : ℝ := if i = s then a else 0

def hopWord (s t : ι) := copyWord s t ++ clearWord s
def readWord (s t : ι) := copyWord s t ++ clearWord t

theorem hop_signal (s t : ι) (hne : s ≠ t) (b a : ℝ) :
    run (hopWord s t) (encode b (signal s a)) = encode b (signal t (a/2)) := by
  rw [hopWord, run_append, copy_native, clear_native]
  congr 1
  ext i
  by_cases hs : i = s <;> by_cases ht : i = t <;>
    simp [cleared, copied, signal, hs, ht, hne, hne.symm]

/-- The output exists after the first two means. The third mean clears only
that output; the original logical sign remains, with half its amplitude. -/
theorem read_signal (s t : ι) (hne : s ≠ t) (b a : ℝ) :
    run (readWord s t) (encode b (signal s a)) = encode b (signal s (a/2)) := by
  rw [readWord, run_append, copy_native, clear_native]
  congr 1
  ext i
  by_cases hs : i = s <;> by_cases ht : i = t <;>
    simp [cleared, copied, signal, hs, ht, hne, hne.symm]

def reads (s t : ι) : ℕ → List ((ι × Bool) × (ι × Bool))
  | 0 => []
  | n+1 => readWord s t ++ reads s t n

theorem reads_signal (s t : ι) (hne : s ≠ t) (b a : ℝ) (n : ℕ) :
    run (reads s t n) (encode b (signal s a)) =
      encode b (signal s (a / (2:ℝ)^n)) := by
  induction n generalizing a with
  | zero => simp [reads, run]
  | succ n ih =>
    rw [reads, run_append, read_signal s t hne, ih]
    congr 2
    rw [pow_succ]
    ring

omit [DecidableEq ι] in
theorem reads_length (s t : ι) (n : ℕ) : (reads s t n).length = 3*n := by
  induction n <;> simp_all [reads, readWord, copyWord, clearWord]
  omega

def routeWord (s : ι) : List ι → List ((ι × Bool) × (ι × Bool))
  | [] => []
  | t :: ts => hopWord s t ++ routeWord t ts

def GoodWalk (s : ι) : List ι → Prop
  | [] => True
  | t :: ts => s ≠ t ∧ GoodWalk t ts

def finish (s : ι) : List ι → ι
  | [] => s
  | t :: ts => finish t ts

/-- Revisits are permitted: all cells except the current one are blank. -/
theorem route_signal (s : ι) (ts : List ι) (h : GoodWalk s ts) (b a : ℝ) :
    run (routeWord s ts) (encode b (signal s a)) =
      encode b (signal (finish s ts) (a/(2:ℝ)^ts.length)) := by
  induction ts generalizing s a with
  | nil => simp [routeWord, run, finish]
  | cons t ts ih =>
    obtain ⟨hne, ht⟩ := h
    rw [routeWord, run_append, hop_signal s t hne, ih t ht]
    simp only [finish, List.length_cons, pow_succ]
    congr 2
    ring

omit [DecidableEq ι] in
theorem route_length (s : ι) (ts : List ι) : (routeWord s ts).length = 3*ts.length := by
  induction ts generalizing s <;>
    simp_all [routeWord, hopWord, copyWord, clearWord]
  omega

theorem attenuation_positive (a : ℝ) (ha : 0 < a) (n : ℕ) :
    0 < a/(2:ℝ)^n := div_pos ha (by positivity)

theorem attenuation_preserves_sign (a : ℝ) (n : ℕ) :
    (0 < a/(2:ℝ)^n ↔ 0 < a) ∧ (a/(2:ℝ)^n = 0 ↔ a = 0) := by
  constructor
  · exact div_pos_iff_of_pos_right (by positivity)
  · simp

/-- A sup error bound; no probabilistic or hardware-noise assumption. -/
def Near (E : ℝ) (x y : ι → ℝ) : Prop := ∀ i, |x i-y i| ≤ E

omit [DecidableEq ι] in
theorem near_trans (x y z : ι → ℝ) (E R : ℝ) (hxy : Near E x y)
    (hyz : Near R y z) : Near (E+R) x z := by
  intro i
  have h := abs_add_le (x i-y i) (y i-z i)
  have he : x i-y i+(y i-z i) = x i-z i := by ring
  rw [he] at h
  exact h.trans (add_le_add (hxy i) (hyz i))

theorem pairAverage_near (u v : ι) (x y : ι → ℝ) (E : ℝ) (h : Near E x y) :
    Near E (pairAverage u v x) (pairAverage u v y) := by
  intro i
  by_cases hi : i = u ∨ i = v
  · have hu := abs_le.mp (h u)
    have hv := abs_le.mp (h v)
    simp only [pairAverage, LinearMap.coe_mk, AddHom.coe_mk, hi, ite_true]
    rw [abs_le]
    constructor <;> linarith
  · simpa [pairAverage, hi] using h i

def noisyRun : List ((ι × ι) × (ι → ℝ)) → (ι → ℝ) → (ι → ℝ)
  | [], x => x
  | (e, noise) :: es, x => noisyRun es (fun i => pairAverage e.1 e.2 x i + noise i)

/-- Includes preparation error and arbitrary signed disturbances after every
native mean. Idle-register drift is allowed, so reuse does not erase errors. -/
theorem noisy_run_bound (es : List ((ι × ι) × (ι → ℝ)))
    (x y : ι → ℝ) (E δ : ℝ) (hxy : Near E x y)
    (he : ∀ en ∈ es, ∀ i, |en.2 i| ≤ δ) :
    Near (E + es.length*δ) (noisyRun es x) (run (es.map Prod.fst) y) := by
  induction es generalizing x y E with
  | nil => simpa [noisyRun, run, Near] using hxy
  | cons en es ih =>
    obtain ⟨e, noise⟩ := en
    have hm := pairAverage_near e.1 e.2 x y E hxy
    have hstep : Near (E+δ) (fun i => pairAverage e.1 e.2 x i + noise i)
        (pairAverage e.1 e.2 y) := by
      intro i
      have hh := he (e, noise) (by simp) i
      have hb := abs_add_le (pairAverage e.1 e.2 x i - pairAverage e.1 e.2 y i) (noise i)
      have hr := hm i
      have hid : pairAverage e.1 e.2 x i + noise i - pairAverage e.1 e.2 y i =
          (pairAverage e.1 e.2 x i - pairAverage e.1 e.2 y i) + noise i := by ring
      rw [hid]
      linarith
    have ht := ih _ _ (E+δ) hstep (by
      intro en hn i
      exact he en (by simp [hn]) i)
    simpa [noisyRun, run, Nat.cast_add, Nat.cast_one, add_mul, add_assoc,
      add_left_comm, add_comm] using ht

theorem robust_positive_read (b a E yp ym : ℝ) (ha : E < a)
    (hp : |yp-(b+a)| ≤ E) (hm : |ym-(b-a)| ≤ E) : ym < yp := by
  have hh := abs_le.mp hp
  have hl := abs_le.mp hm
  linarith

theorem robust_negative_read (b a E yp ym : ℝ) (ha : E < a)
    (hp : |yp-(b-a)| ≤ E) (hm : |ym-(b+a)| ≤ E) : yp < ym := by
  exact robust_positive_read b a E ym yp ha hm hp

/-- End-to-end sufficient sign margin for the same native walk, retaining
preparation error, every mean disturbance and terminal readout uncertainty. -/
theorem robust_route_positive (s : ι) (ts : List ι) (hw : GoodWalk s ts)
    (b a E δ ρ : ℝ) (x observed : ι × Bool → ℝ)
    (es : List (((ι × Bool) × (ι × Bool)) × ((ι × Bool) → ℝ)))
    (hword : es.map Prod.fst = routeWord s ts)
    (hx : Near E x (encode b (signal s a)))
    (he : ∀ en ∈ es, ∀ i, |en.2 i| ≤ δ)
    (hr : Near ρ observed (noisyRun es x))
    (hmargin : ρ + (E + (3*ts.length : ℕ)*δ) < a/(2:ℝ)^ts.length) :
    observed (finish s ts, true) < observed (finish s ts, false) := by
  have hn := noisy_run_bound es x (encode b (signal s a)) E δ hx he
  have hlen : es.length = 3*ts.length := by
    simpa [route_length] using congrArg List.length hword
  rw [hlen, hword, route_signal s ts hw] at hn
  have ht := near_trans observed (noisyRun es x)
    (encode b (signal (finish s ts) (a/(2:ℝ)^ts.length)))
    ρ (E + (3*ts.length : ℕ)*δ) hr hn
  apply robust_positive_read b (a/(2:ℝ)^ts.length)
    (ρ+(E+(3*ts.length : ℕ)*δ)) _ _ hmargin
  · simpa [encode, signal, sub_eq_add_neg] using ht (finish s ts, false)
  · simpa [encode, signal, sub_eq_add_neg] using ht (finish s ts, true)

/-- At the exact terminal uncertainty threshold, both opposite bits admit
the same observation [b,b]. No decoder of that observation can distinguish. -/
theorem ambiguous_at_margin (b a E : ℝ) (ha : 0 ≤ a) (hE : a ≤ E) :
    |b-(b+a)| ≤ E ∧ |b-(b-a)| ≤ E := by
  constructor <;> simpa [abs_of_nonneg ha] using hE

/-- The analog inverse has exponential readout gain; it is analysis, not
another native write or a physically supplied amplifier. -/
theorem analog_readout_error (a e : ℝ) (n : ℕ) :
    (2:ℝ)^n * (a/(2:ℝ)^n + e) - a = (2:ℝ)^n * e := by
  have hn : (2:ℝ)^n ≠ 0 := by positivity
  field_simp
  ring

end
end OPH.SourceEncodedMemory

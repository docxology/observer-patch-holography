module
public import ObserverPatchHolography.ScalarSeamRepair

@[expose] public section

/-!
# Destination-local reconstruction through canonical seam means

A declared path is calibrated from its destination backwards. Each calibration
phase performs one forward sweep through the calibrated suffix. The
receiver records its own scalar after each phase; remote pre-states are not
inputs to the decoder. All scalar writes are pair means. The theorem establishes
finite exact information transport for this schedule, not a selected routing
law, repeatable immutable-version reads, bounded physical precision or time.
-/

namespace OPH.SourceSeamPathTomography

noncomputable section

/-- Destination value after a forward sweep with the stated relay pre-states. -/
def endpoint (x : ℝ) : List ℝ → ℝ
  | [] => x
  | b :: bs => endpoint ((x + b) / 2) bs

/-- All path values after that sweep, including both endpoints. -/
def swept (x : ℝ) : List ℝ → List ℝ
  | [] => [x]
  | b :: bs => ((x + b) / 2) :: swept ((x + b) / 2) bs

/-- Invert a sweep when its actual, calibrated relay pre-states are known. -/
def invert : List ℝ → ℝ → ℝ
  | [], y => y
  | b :: bs, y => 2 * invert bs y - b

theorem invert_endpoint (bs : List ℝ) (x : ℝ) :
    invert bs (endpoint x bs) = x := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih => simp only [endpoint, invert, ih]; ring

/-- A perturbation at the source is attenuated by exactly one half per seam. -/
theorem endpoint_difference (bs : List ℝ) (x y : ℝ) :
    endpoint x bs - endpoint y bs = (x - y) / (2 : ℝ) ^ bs.length := by
  induction bs generalizing x y with
  | nil => simp [endpoint]
  | cons b bs ih =>
    simp only [endpoint, List.length_cons, ih, pow_succ]
    ring

/-- Consequently fixed-baseline inverse noise grows by exactly two per seam. -/
theorem invert_difference (bs : List ℝ) (x y : ℝ) :
    invert bs x - invert bs y = (2 : ℝ) ^ bs.length * (x - y) := by
  induction bs with
  | nil => simp [invert]
  | cons b bs ih =>
    simp only [invert, List.length_cons, pow_succ]
    calc
      2 * invert bs x - b - (2 * invert bs y - b) =
          2 * (invert bs x - invert bs y) := by ring
      _ = _ := by rw [ih]; ring

/-- Recursive suffix calibration: resulting port state and observations in
reverse chronological order. The terminal singleton is a local initial read. -/
def encode : List ℝ → List ℝ × List ℝ
  | [] => ([], [])
  | x :: xs =>
    let previous := encode xs
    (swept x previous.1, endpoint x previous.1 :: previous.2)

/-- Reconstruction receives only the destination observations. It reconstructs
both the original values and the actual evolving suffix state. -/
def decode : List ℝ → List ℝ × List ℝ
  | [] => ([], [])
  | y :: ys =>
    let previous := decode ys
    let x := invert previous.2 y
    (x :: previous.1, swept x previous.2)

/-- The complete path's original values are recovered from destination-local
observations; the second component reconstructs the changed physical state. -/
theorem decode_encode (xs : List ℝ) :
    decode (encode xs).2 = (xs, (encode xs).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [encode, decode, ih, invert_endpoint]

/-- No two distinct initial path states have the same local calibration record. -/
theorem encode_observations_injective : Function.Injective (fun xs => (encode xs).2) := by
  intro xs ys h
  have hd := congrArg decode h
  rw [decode_encode, decode_encode] at hd
  exact congrArg Prod.fst hd

theorem swept_length (bs : List ℝ) (x : ℝ) :
    (swept x bs).length = bs.length + 1 := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih => simp [swept, ih]

theorem encode_lengths (xs : List ℝ) :
    (encode xs).1.length = xs.length ∧ (encode xs).2.length = xs.length := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih => simp [encode, swept_length, ih]

/-- Total seam operations on a path with d edges, including calibration. -/
def meanCost : ℕ → ℕ
  | 0 => 0
  | d + 1 => meanCost d + (d + 1)

theorem twice_meanCost (d : ℕ) : 2 * meanCost d = d * (d + 1) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [meanCost, Nat.mul_add, ih]; ring

/-- Every hop is the existing canonical scalar seam law, with endpoint sum
preserved. Readback arithmetic does not add a different physical update. -/
theorem canonical_hop_decode {ι : Type*} [DecidableEq ι]
    (u v : ι) (x : ι → ℝ) :
    2 * ObserverPatchHolography.ScalarSeamRepair.pairAverage u v x v - x v = x u := by
  rw [ObserverPatchHolography.ScalarSeamRepair.pairAverage_right]
  ring

end
end OPH.SourceSeamPathTomography

#print axioms OPH.SourceSeamPathTomography.decode_encode
#print axioms OPH.SourceSeamPathTomography.encode_observations_injective
#print axioms OPH.SourceSeamPathTomography.endpoint_difference
#print axioms OPH.SourceSeamPathTomography.invert_difference
#print axioms OPH.SourceSeamPathTomography.twice_meanCost

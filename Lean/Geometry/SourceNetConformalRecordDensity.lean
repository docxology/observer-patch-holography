module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Geometry.SourceNetLayeredOrder
public import Time.SourceCountClock
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Expansion as record density on the conformally invariant source order

INPUTS.  A real normed space `E` of comoving positions; an edge radius `a`;
a layer profile `σ : ℕ → ℝ`, the scale factor read at the conformal tick of
each layer, so that the physical position of the comoving site `x` at layer
`j` is `σ j • x` and the physical read radius at that layer is `σ j * a`;
a finite set `I` of events `(j, s)` on a site type `S`; comoving cell masses
`v : S → ℝ`; a conformal tick `Δ`; and the constant-physical-density count
measure, in which an event at layer `j` carries the physical tick `σ j * Δ`
times the physical cell volume `σ j ^ 3 * v s`.  The fourth root is the real
power `x ^ (1 / 4)`.  The de Sitter profile is `-1 / (H * η)` on `η < 0`.

WHAT IS PROVED.  Positive scaling preserves and reflects the ball read law:
`‖s • y - s • x‖ ≤ s * a ↔ ‖y - x‖ ≤ a` for `s > 0` (`scaled_step_iff`).
For a positive profile the physical read law at every layer equals the
comoving read law as a relation (`scaledStep_eq`), so the layered orders of
`Geometry/SourceNetLayeredOrder.lean` built from the two laws are equal
(`layerPrec_scaledStep`); the layer-dependent physical one-layer reads equal
the comoving reads (`scaledRead_eq`) and their reflexive transitive closure
is the comoving layered order (`reflTransGen_scaledRead_iff`); on a
population `P ⊆ E` the scaled ball law is `ballStep P a` and its layered
order is the paper's `Precedes a` (`layerPrec_scaledBallStep_iff_precedes`).
The count measure factorizes as `∑ σ j ^ 4 * (Δ * v s)`, the discrete form
of the FLRW four-volume weight `a⁴ dη d³x` (`flrwMass_eq`); a constant
profile `s` gives `s ^ 4` times the flat mass (`flrwMass_const`); a profile
confined to `[σmin, σmax]` on `I` gives
`σmin ^ 4 * flat ≤ flrw ≤ σmax ^ 4 * flat` (`flrwMass_sandwich`); and the
fourth root of the ratio of two such masses lies within the factors
`σmin_I / σmax_J` and `σmax_I / σmin_J` of the fourth root of the flat ratio
(`expanding_count_clock_enclosure`, `expanding_count_clock`).  For counts
`n = κ * σ ^ 4` with a common positive factor, the fourth root of the count
ratio is the scale-factor ratio (`scaleFactor_ratio_of_counts`), so
`1 + z = σ₀ / σₑ = (n₀ / nₑ) ^ (1 / 4)`
(`one_add_redshift_eq_fourthRoot_count_ratio`).  The de Sitter profile is
positive on `η < 0` (`deSitterProfile_pos`), satisfies `dσ/dη = H σ ^ 2`
(`hasDerivAt_deSitterProfile`), has record density
`κ σ ^ 4 = κ / (H η) ^ 4` (`deSitter_density`), and has epoch ratio
`σ(η₀) / σ(ηₑ) = ηₑ / η₀` (`deSitterProfile_ratio`).

NOT CLAIMED.  No source law selects the profile `σ`: record production per
comoving cell is a supplied datum, the subject of the sourced-density issue.
No physical clock is identified, no population is selected by native repair,
and no continuum limit or manifold is reconstructed here.  The conformal
invariance is a statement about the order, and the `σ ^ 4` weight is the
definition of a constant-physical-density count measure; nothing here
derives the Friedmann equation.  The de Sitter identities are properties of
one named profile over `ℝ`, with no dynamics selecting it.
-/

namespace OPH.SourceNetConformalRecordDensity

open OPH.SourceNetLayeredOrder OPH.SourceNetCausalCone OPH.SourceCountClock Relation

/-! ### Conformal invariance of the layered order -/

section Order

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive scaling of positions and radius preserves and reflects the ball read law. -/
theorem scaled_step_iff {s : ℝ} (hs : 0 < s) (a : ℝ) (x y : E) :
    ‖s • y - s • x‖ ≤ s * a ↔ ‖y - x‖ ≤ a := by
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hs.le]
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hs
  · intro h
    exact mul_le_mul_of_nonneg_left h hs.le

/-- The read law at layer `j` in physical coordinates: physical positions `σ j • x`,
physical read radius `σ j * a`. -/
def scaledStep (σ : ℕ → ℝ) (a : ℝ) (j : ℕ) (x y : E) : Prop :=
  ‖σ j • y - σ j • x‖ ≤ σ j * a

theorem scaledStep_iff {σ : ℕ → ℝ} (hσ : ∀ j, 0 < σ j) (a : ℝ) (j : ℕ) (x y : E) :
    scaledStep σ a j x y ↔ ‖y - x‖ ≤ a :=
  scaled_step_iff (hσ j) a x y

/-- For a positive profile the physical read law at every layer is the comoving read
law, as a relation. -/
theorem scaledStep_eq {σ : ℕ → ℝ} (hσ : ∀ j, 0 < σ j) (a : ℝ) (j : ℕ) :
    scaledStep σ a j = fun x y : E => ‖y - x‖ ≤ a := by
  funext x y
  exact propext (scaledStep_iff hσ a j x y)

/-- The layered order of the physical read law at any layer is the layered order of
the comoving read law. -/
theorem layerPrec_scaledStep {σ : ℕ → ℝ} (hσ : ∀ j, 0 < σ j) (a : ℝ) (j : ℕ) :
    LayerPrec (scaledStep σ a j) = LayerPrec (fun x y : E => ‖y - x‖ ≤ a) := by
  rw [scaledStep_eq hσ a j]

/-- The one-layer read with the scale of the reading layer: the event at layer `j + 1`
reads a site within physical radius `σ (j + 1) * a` of its own physical position. -/
def scaledRead (σ : ℕ → ℝ) (a : ℝ) (e f : ℕ × E) : Prop :=
  f.1 = e.1 + 1 ∧ scaledStep σ a f.1 e.2 f.2

/-- The layer-dependent physical reads are the comoving reads. -/
theorem scaledRead_eq {σ : ℕ → ℝ} (hσ : ∀ j, 0 < σ j) (a : ℝ) :
    scaledRead σ a = Read (fun x y : E => ‖y - x‖ ≤ a) := by
  funext e f
  show (f.1 = e.1 + 1 ∧ scaledStep σ a f.1 e.2 f.2) = (f.1 = e.1 + 1 ∧ ‖f.2 - e.2‖ ≤ a)
  rw [scaledStep_eq hσ a f.1]

/-- The reflexive transitive closure of the physical one-layer reads is the comoving
layered order. -/
theorem reflTransGen_scaledRead_iff {σ : ℕ → ℝ} (hσ : ∀ j, 0 < σ j) (a : ℝ)
    (e f : ℕ × E) :
    ReflTransGen (scaledRead σ a) e f ↔ LayerPrec (fun x y : E => ‖y - x‖ ≤ a) e f := by
  rw [scaledRead_eq hσ a]
  exact (layerPrec_iff_reflTransGen e f).symm

/-- The physical ball read law on a population `P` at layer `j`. -/
def scaledBallStep (P : Set E) (σ : ℕ → ℝ) (a : ℝ) (j : ℕ) (u v : P) : Prop :=
  ‖σ j • (v : E) - σ j • (u : E)‖ ≤ σ j * a

theorem scaledBallStep_eq (P : Set E) {σ : ℕ → ℝ} (hσ : ∀ j, 0 < σ j) (a : ℝ) (j : ℕ) :
    scaledBallStep P σ a j = ballStep P a := by
  funext u v
  exact propext (scaled_step_iff (hσ j) a (u : E) (v : E))

/-- On a population the layered order of the physical ball law is the paper's
`Precedes a`, for every positive profile and every layer. -/
theorem layerPrec_scaledBallStep_iff_precedes (P : Set E) {σ : ℕ → ℝ}
    (hσ : ∀ j, 0 < σ j) (a : ℝ) (j : ℕ) (e f : ℕ × P) :
    LayerPrec (scaledBallStep P σ a j) e f ↔ Precedes a e f := by
  rw [scaledBallStep_eq P hσ a j]
  exact (precedes_iff_layerPrec P a e f).symm

end Order

/-! ### The count clock -/

/-- The positive fourth root of a fourth power. -/
theorem rpow_quarter_pow_four {x : ℝ} (hx : 0 ≤ x) : (x ^ 4) ^ ((1 : ℝ) / 4) = x := by
  rw [show ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hx (by norm_num)

/-- The fourth root of the ratio of two sandwiched masses lies within the extreme
scale ratios of the fourth root of the flat mass ratio. -/
theorem expanding_count_clock_enclosure {MI MJ FI FJ sI SI sJ SJ : ℝ}
    (hFI : 0 ≤ FI) (hFJ : 0 < FJ) (hsI : 0 ≤ sI) (hSI : 0 ≤ SI) (hsJ : 0 < sJ)
    (hSJ : 0 < SJ) (hIlo : sI ^ 4 * FI ≤ MI) (hIhi : MI ≤ SI ^ 4 * FI)
    (hJlo : sJ ^ 4 * FJ ≤ MJ) (hJhi : MJ ≤ SJ ^ 4 * FJ) :
    (sI / SJ) * (FI / FJ) ^ ((1 : ℝ) / 4) ≤ (MI / MJ) ^ ((1 : ℝ) / 4) ∧
      (MI / MJ) ^ ((1 : ℝ) / 4) ≤ (SI / sJ) * (FI / FJ) ^ ((1 : ℝ) / 4) := by
  have hMJ : 0 < MJ := lt_of_lt_of_le (by positivity) hJlo
  have hMI : 0 ≤ MI := le_trans (by positivity) hIlo
  have hlo : sI ^ 4 * FI / (SJ ^ 4 * FJ) ≤ MI / MJ := div_le_div₀ hMI hIlo hMJ hJhi
  have hhi : MI / MJ ≤ SI ^ 4 * FI / (sJ ^ 4 * FJ) :=
    div_le_div₀ (by positivity) hIhi (by positivity) hJlo
  have e1 : sI ^ 4 * FI / (SJ ^ 4 * FJ) = (sI / SJ) ^ 4 * (FI / FJ) := by
    rw [div_pow, div_mul_div_comm]
  have e2 : SI ^ 4 * FI / (sJ ^ 4 * FJ) = (SI / sJ) ^ 4 * (FI / FJ) := by
    rw [div_pow, div_mul_div_comm]
  have hq : 0 ≤ FI / FJ := div_nonneg hFI hFJ.le
  have r1 : ((sI / SJ) ^ 4 * (FI / FJ)) ^ ((1 : ℝ) / 4)
      = (sI / SJ) * (FI / FJ) ^ ((1 : ℝ) / 4) := by
    rw [Real.mul_rpow (pow_nonneg (div_nonneg hsI hSJ.le) 4) hq,
      rpow_quarter_pow_four (div_nonneg hsI hSJ.le)]
  have r2 : ((SI / sJ) ^ 4 * (FI / FJ)) ^ ((1 : ℝ) / 4)
      = (SI / sJ) * (FI / FJ) ^ ((1 : ℝ) / 4) := by
    rw [Real.mul_rpow (pow_nonneg (div_nonneg hSI hsJ.le) 4) hq,
      rpow_quarter_pow_four (div_nonneg hSI hsJ.le)]
  constructor
  · rw [← r1, ← e1]
    exact Real.rpow_le_rpow (by positivity) hlo (by norm_num)
  · rw [← r2, ← e2]
    exact Real.rpow_le_rpow (by positivity) hhi (by norm_num)

/-! ### The constant-physical-density count measure -/

section Measure

variable {S : Type*}

/-- The flat count measure: conformal tick times comoving cell mass, summed over the
events of `I`. -/
noncomputable def flatMass (Δ : ℝ) (v : S → ℝ) (I : Finset (ℕ × S)) : ℝ :=
  ∑ e ∈ I, Δ * v e.2

/-- The count measure at constant physical density: the physical tick `σ j * Δ` times
the physical cell volume `σ j ^ 3 * v s` at every event `(j, s)` of `I`. -/
noncomputable def flrwMass (σ : ℕ → ℝ) (Δ : ℝ) (v : S → ℝ) (I : Finset (ℕ × S)) : ℝ :=
  ∑ e ∈ I, (σ e.1 * Δ) * (σ e.1 ^ 3 * v e.2)

/-- The FLRW four-volume weight: every event carries `σ j ^ 4` times its flat mass. -/
theorem flrwMass_eq (σ : ℕ → ℝ) (Δ : ℝ) (v : S → ℝ) (I : Finset (ℕ × S)) :
    flrwMass σ Δ v I = ∑ e ∈ I, σ e.1 ^ 4 * (Δ * v e.2) := by
  unfold flrwMass
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- A constant profile scales the flat mass by its fourth power. -/
theorem flrwMass_const (s Δ : ℝ) (v : S → ℝ) (I : Finset (ℕ × S)) :
    flrwMass (fun _ => s) Δ v I = s ^ 4 * flatMass Δ v I := by
  rw [flrwMass_eq, flatMass, Finset.mul_sum]

theorem flatMass_nonneg {Δ : ℝ} {v : S → ℝ} (hΔ : 0 ≤ Δ) (hv : ∀ s, 0 ≤ v s)
    (I : Finset (ℕ × S)) : 0 ≤ flatMass Δ v I :=
  Finset.sum_nonneg fun e _ => mul_nonneg hΔ (hv e.2)

/-- The sandwich: a profile confined to `[σmin, σmax]` on the layers of `I` confines the
count measure between `σmin ^ 4` and `σmax ^ 4` times the flat mass. -/
theorem flrwMass_sandwich {σ : ℕ → ℝ} {Δ : ℝ} {v : S → ℝ} {I : Finset (ℕ × S)}
    {σmin σmax : ℝ} (hΔ : 0 ≤ Δ) (hv : ∀ s, 0 ≤ v s) (hmin : 0 ≤ σmin)
    (hlo : ∀ e ∈ I, σmin ≤ σ e.1) (hhi : ∀ e ∈ I, σ e.1 ≤ σmax) :
    σmin ^ 4 * flatMass Δ v I ≤ flrwMass σ Δ v I ∧
      flrwMass σ Δ v I ≤ σmax ^ 4 * flatMass Δ v I := by
  rw [flrwMass_eq, flatMass, Finset.mul_sum, Finset.mul_sum]
  constructor
  · refine Finset.sum_le_sum fun e he => ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmin (hlo e he) 4)
      (mul_nonneg hΔ (hv e.2))
  · refine Finset.sum_le_sum fun e he => ?_
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hmin.trans (hlo e he)) (hhi e he) 4) (mul_nonneg hΔ (hv e.2))

/-- The count clock on an expanding family, from the sandwich bounds of two event
sets `I` and `J`: the fourth root of the FLRW mass ratio lies within the extreme scale
ratios of the fourth root of the flat mass ratio. -/
theorem expanding_count_clock {σ : ℕ → ℝ} {Δ : ℝ} {v : S → ℝ} {I J : Finset (ℕ × S)}
    {sI SI sJ SJ : ℝ} (hΔ : 0 ≤ Δ) (hv : ∀ s, 0 ≤ v s)
    (hsI : 0 ≤ sI) (hSI : 0 ≤ SI) (hsJ : 0 < sJ) (hSJ : 0 < SJ)
    (hIlo : ∀ e ∈ I, sI ≤ σ e.1) (hIhi : ∀ e ∈ I, σ e.1 ≤ SI)
    (hJlo : ∀ e ∈ J, sJ ≤ σ e.1) (hJhi : ∀ e ∈ J, σ e.1 ≤ SJ)
    (hFJ : 0 < flatMass Δ v J) :
    (sI / SJ) * (flatMass Δ v I / flatMass Δ v J) ^ ((1 : ℝ) / 4)
        ≤ (flrwMass σ Δ v I / flrwMass σ Δ v J) ^ ((1 : ℝ) / 4) ∧
      (flrwMass σ Δ v I / flrwMass σ Δ v J) ^ ((1 : ℝ) / 4)
        ≤ (SI / sJ) * (flatMass Δ v I / flatMass Δ v J) ^ ((1 : ℝ) / 4) := by
  obtain ⟨hI1, hI2⟩ := flrwMass_sandwich hΔ hv hsI hIlo hIhi
  obtain ⟨hJ1, hJ2⟩ := flrwMass_sandwich hΔ hv hsJ.le hJlo hJhi
  exact expanding_count_clock_enclosure (flatMass_nonneg hΔ hv I) hFJ hsI hSI hsJ hSJ
    hI1 hI2 hJ1 hJ2

end Measure

/-! ### The scale factor and the redshift as count readouts -/

/-- Counts proportional to the fourth power of the scale: the count ratio is the fourth
power of the scale ratio. -/
theorem count_ratio_eq_pow_four {κ σj σ0 : ℝ} (hκ : 0 < κ) :
    (κ * σj ^ 4) / (κ * σ0 ^ 4) = (σj / σ0) ^ 4 := by
  rw [common_weight_cancels _ _ _ hκ, div_pow]

/-- The scale-factor ratio is the fourth root of the count ratio. -/
theorem scaleFactor_ratio_of_counts {κ σj σ0 nj n0 : ℝ} (hκ : 0 < κ) (hσj : 0 < σj)
    (hσ0 : 0 < σ0) (hnj : nj = κ * σj ^ 4) (hn0 : n0 = κ * σ0 ^ 4) :
    (nj / n0) ^ ((1 : ℝ) / 4) = σj / σ0 := by
  rw [hnj, hn0, count_ratio_eq_pow_four hκ]
  exact rpow_quarter_pow_four (div_nonneg hσj.le hσ0.le)

/-- The cosmological redshift is the fourth root of a record-count ratio: with
`1 + z = σ0 / σe`, `1 + z = (n0 / ne) ^ (1 / 4)`. -/
theorem one_add_redshift_eq_fourthRoot_count_ratio {κ σ0 σe n0 ne z : ℝ} (hκ : 0 < κ)
    (hσ0 : 0 < σ0) (hσe : 0 < σe) (hn0 : n0 = κ * σ0 ^ 4) (hne : ne = κ * σe ^ 4)
    (hz : 1 + z = σ0 / σe) :
    1 + z = (n0 / ne) ^ ((1 : ℝ) / 4) := by
  rw [hz]
  exact (scaleFactor_ratio_of_counts hκ hσ0 hσe hn0 hne).symm

/-! ### The de Sitter conformal profile -/

/-- The de Sitter scale factor in conformal time, `σ(η) = -1 / (H η)` on `η < 0`. -/
noncomputable def deSitterProfile (H η : ℝ) : ℝ := -1 / (H * η)

theorem deSitterProfile_pos {H η : ℝ} (hH : 0 < H) (hη : η < 0) :
    0 < deSitterProfile H η := by
  unfold deSitterProfile
  exact div_pos_of_neg_of_neg (by norm_num) (mul_neg_of_pos_of_neg hH hη)

/-- The de Sitter profile satisfies `dσ/dη = H σ ^ 2`. -/
theorem hasDerivAt_deSitterProfile {H η : ℝ} (hH : 0 < H) (hη : η < 0) :
    HasDerivAt (deSitterProfile H) (H * deSitterProfile H η ^ 2) η := by
  have hne : H * η ≠ 0 := (mul_neg_of_pos_of_neg hH hη).ne
  have hH0 : H ≠ 0 := hH.ne'
  have hη0 : η ≠ 0 := hη.ne
  have hc : HasDerivAt (fun _ : ℝ => (-1 : ℝ)) 0 η := hasDerivAt_const η (-1 : ℝ)
  have hd : HasDerivAt (fun t : ℝ => H * t) H η := by
    simpa using (hasDerivAt_id η).const_mul H
  have h : HasDerivAt (deSitterProfile H)
      ((0 * (H * η) - (-1) * H) / (H * η) ^ 2) η := hc.div hd hne
  have hval : (0 * (H * η) - (-1) * H) / (H * η) ^ 2 = H * deSitterProfile H η ^ 2 := by
    unfold deSitterProfile
    field_simp
    ring
  rw [hval] at h
  exact h

/-- Record density per comoving cell on the de Sitter profile:
`κ σ ^ 4 = κ / (H η) ^ 4`. -/
theorem deSitter_density (κ H η : ℝ) :
    κ * deSitterProfile H η ^ 4 = κ / (H * η) ^ 4 := by
  unfold deSitterProfile
  ring

/-- The de Sitter epoch ratio: `σ(η0) / σ(ηe) = ηe / η0`. -/
theorem deSitterProfile_ratio {H η0 ηe : ℝ} (hH : 0 < H) (hη0 : η0 < 0) (hηe : ηe < 0) :
    deSitterProfile H η0 / deSitterProfile H ηe = ηe / η0 := by
  have hH0 : H ≠ 0 := hH.ne'
  have h0 : η0 ≠ 0 := hη0.ne
  have he : ηe ≠ 0 := hηe.ne
  unfold deSitterProfile
  field_simp

#print axioms scaled_step_iff
#print axioms scaledStep_eq
#print axioms layerPrec_scaledStep
#print axioms scaledRead_eq
#print axioms reflTransGen_scaledRead_iff
#print axioms layerPrec_scaledBallStep_iff_precedes
#print axioms flrwMass_eq
#print axioms flrwMass_const
#print axioms flrwMass_sandwich
#print axioms expanding_count_clock_enclosure
#print axioms expanding_count_clock
#print axioms scaleFactor_ratio_of_counts
#print axioms one_add_redshift_eq_fourthRoot_count_ratio
#print axioms deSitterProfile_pos
#print axioms hasDerivAt_deSitterProfile
#print axioms deSitter_density
#print axioms deSitterProfile_ratio

end OPH.SourceNetConformalRecordDensity

module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Flat-spacetime reference constants of the ordering fraction

INPUTS.  A time separation `T` between the two tips of a flat causal
diamond in units `c = 1`, the `dt d³x` volume convention, and the section
integrand `r² ((T - t)² - r²)²` of the strict oriented-pair integral: at
time `t` and radius `r` the volume of the diamond to the future of `(t, x)`
with `|x| = r` is `π ((T - t)² - r²)² / 24`, and the spatial section of the
diamond at time `t` is the ball of radius `min t (T - t)`.

WHAT IS PROVED.  These are the flat-spacetime reference constants of the
paper's limit statement (the four-dimensional ordering fraction).  The
polynomial double integral
`∫₀ᵀ ∫₀^{min(t, T - t)} r² ((T - t)² - r²)² dr dt = T⁸ / 1920`
(`orderedPair_double_integral`); with the diamond volume `V = π T⁴ / 24`
the oriented-pair integral `(π² / 6) · T⁸ / 1920 = π² T⁸ / 11520 = V² / 20`
(`orientedPairIntegral_eq_volume_sq`); the ordering fraction
`2 · (V² / 20) / V² = 1 / 10` (`orderingFraction_eq`); and the Myrheim-Meyer
values `Γ(d + 1) Γ(d / 2) / (2 Γ(3d / 2))` at `d = 4`, `d = 2` and `d = 3`,
namely `1 / 10`, `1 / 2` and `8 / 35` (`myrheimMeyer_four`,
`myrheimMeyer_two`, `myrheimMeyer_three`); the `d = 3` value is the `2 + 1`
reference used by the simulator.

SCOPE. The convergence of actual finite strict-pair counts is proved in
`GoldenSourcePairLimit`; `FlatDiamondPairIntegral` connects this polynomial
integral to the geometric pair set, and `FlatDiamondNormalization` proves
the resulting `1/10` limit. This module supplies the polynomial constants. No physical
clock, no selection of a population by native repair, and no manifold
reconstruction enter these identities; they are integrals and Gamma-function
values over `ℝ`.
-/

namespace OPH.OrderingFractionFourDimensional

open Real intervalIntegral

/-! ### The inner radial integral -/

/-- The radial primitive differentiates to the section integrand. -/
theorem hasDerivAt_innerPrimitive (u r : ℝ) :
    HasDerivAt (fun r : ℝ => u ^ 4 * r ^ 3 / 3 - 2 * u ^ 2 * r ^ 5 / 5 + r ^ 7 / 7)
      (r ^ 2 * (u ^ 2 - r ^ 2) ^ 2) r := by
  have h := ((((hasDerivAt_pow 3 r).const_mul (u ^ 4)).div_const 3).sub
    (((hasDerivAt_pow 5 r).const_mul (2 * u ^ 2)).div_const 5)).add
    ((hasDerivAt_pow 7 r).div_const 7)
  convert h using 1
  norm_num
  ring

/-- The closed form of the radial integral for every upper limit `m`. -/
theorem inner_integral (u m : ℝ) :
    ∫ r in (0:ℝ)..m, r ^ 2 * (u ^ 2 - r ^ 2) ^ 2
      = u ^ 4 * m ^ 3 / 3 - 2 * u ^ 2 * m ^ 5 / 5 + m ^ 7 / 7 := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_innerPrimitive u x)
    ((by fun_prop : Continuous fun r : ℝ => r ^ 2 * (u ^ 2 - r ^ 2) ^ 2).intervalIntegrable 0 m)]
  ring

/-- The section volume factor: the radial integral over the section radius. -/
noncomputable def innerVolume (T t : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..(min t (T - t)), r ^ 2 * ((T - t) ^ 2 - r ^ 2) ^ 2

theorem innerVolume_eq (T t : ℝ) :
    innerVolume T t = (T - t) ^ 4 * (min t (T - t)) ^ 3 / 3
      - 2 * (T - t) ^ 2 * (min t (T - t)) ^ 5 / 5 + (min t (T - t)) ^ 7 / 7 :=
  inner_integral (T - t) (min t (T - t))

theorem innerVolume_continuous (T : ℝ) : Continuous (innerVolume T) := by
  have h : innerVolume T = fun t => (T - t) ^ 4 * (min t (T - t)) ^ 3 / 3
      - 2 * (T - t) ^ 2 * (min t (T - t)) ^ 5 / 5 + (min t (T - t)) ^ 7 / 7 :=
    funext (innerVolume_eq T)
  rw [h]
  fun_prop

/-- Below the midpoint the section radius is `t`. -/
theorem innerVolume_first_half {T t : ℝ} (ht : t ≤ T - t) :
    innerVolume T t = T ^ 4 * t ^ 3 / 3 - 4 * T ^ 3 * t ^ 4 / 3 + 8 * T ^ 2 * t ^ 5 / 5
      - 8 * T * t ^ 6 / 15 + 8 * t ^ 7 / 105 := by
  rw [innerVolume_eq, min_eq_left ht]
  ring

/-- Above the midpoint the section radius is `T - t`. -/
theorem innerVolume_second_half {T t : ℝ} (ht : T - t ≤ t) :
    innerVolume T t = 8 * (T - t) ^ 7 / 105 := by
  rw [innerVolume_eq, min_eq_right ht]
  ring

/-! ### The outer time integral -/

theorem hasDerivAt_firstPrimitive (T t : ℝ) :
    HasDerivAt (fun t : ℝ => T ^ 4 * t ^ 4 / 12 - 4 * T ^ 3 * t ^ 5 / 15
        + 4 * T ^ 2 * t ^ 6 / 15 - 8 * T * t ^ 7 / 105 + t ^ 8 / 105)
      (T ^ 4 * t ^ 3 / 3 - 4 * T ^ 3 * t ^ 4 / 3 + 8 * T ^ 2 * t ^ 5 / 5
        - 8 * T * t ^ 6 / 15 + 8 * t ^ 7 / 105) t := by
  have h := ((((((hasDerivAt_pow 4 t).const_mul (T ^ 4)).div_const 12).sub
    (((hasDerivAt_pow 5 t).const_mul (4 * T ^ 3)).div_const 15)).add
    (((hasDerivAt_pow 6 t).const_mul (4 * T ^ 2)).div_const 15)).sub
    (((hasDerivAt_pow 7 t).const_mul (8 * T)).div_const 105)).add
    ((hasDerivAt_pow 8 t).div_const 105)
  convert h using 1
  norm_num
  ring

theorem hasDerivAt_secondPrimitive (T t : ℝ) :
    HasDerivAt (fun t : ℝ => -((T - t) ^ 8 / 105)) (8 * (T - t) ^ 7 / 105) t := by
  have h := ((((hasDerivAt_id' (x := t)).const_sub T).pow 8).div_const 105).neg
  convert h using 1
  norm_num
  ring

/-- The polynomial double integral of the ordering-fraction proposition. -/
theorem orderedPair_double_integral (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, innerVolume T t = T ^ 8 / 1920 := by
  have hc := innerVolume_continuous T
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable 0 (T / 2))
    (hc.intervalIntegrable (T / 2) T)]
  have h1 : ∫ t in (0:ℝ)..(T / 2), innerVolume T t
      = ∫ t in (0:ℝ)..(T / 2), (T ^ 4 * t ^ 3 / 3 - 4 * T ^ 3 * t ^ 4 / 3
          + 8 * T ^ 2 * t ^ 5 / 5 - 8 * T * t ^ 6 / 15 + 8 * t ^ 7 / 105) := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact innerVolume_first_half (by linarith [ht.1, ht.2])
  have h2 : ∫ t in (T / 2)..T, innerVolume T t
      = ∫ t in (T / 2)..T, 8 * (T - t) ^ 7 / 105 := by
    apply integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact innerVolume_second_half (by linarith [ht.1, ht.2])
  rw [h1, h2,
    integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_firstPrimitive T x)
      ((by fun_prop : Continuous fun t : ℝ => T ^ 4 * t ^ 3 / 3 - 4 * T ^ 3 * t ^ 4 / 3
          + 8 * T ^ 2 * t ^ 5 / 5 - 8 * T * t ^ 6 / 15
          + 8 * t ^ 7 / 105).intervalIntegrable _ _),
    integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_secondPrimitive T x)
      ((by fun_prop : Continuous fun t : ℝ => 8 * (T - t) ^ 7 / 105).intervalIntegrable _ _)]
  ring

/-! ### Volume normalization and the ordering fraction -/

/-- The flat diamond volume for tips at time separation `T`, `c = 1`, `dt d³x`. -/
noncomputable def diamondVolume (T : ℝ) : ℝ := Real.pi * T ^ 4 / 24

/-- The strict oriented-pair integral of the proposition. -/
noncomputable def orientedPairIntegral (T : ℝ) : ℝ :=
  (Real.pi ^ 2 / 6) * ∫ t in (0:ℝ)..T, innerVolume T t

theorem orientedPairIntegral_eq (T : ℝ) (hT : 0 ≤ T) :
    orientedPairIntegral T = Real.pi ^ 2 * T ^ 8 / 11520 := by
  rw [orientedPairIntegral, orderedPair_double_integral T hT]
  ring

theorem orientedPairIntegral_eq_volume_sq (T : ℝ) (hT : 0 ≤ T) :
    orientedPairIntegral T = diamondVolume T ^ 2 / 20 := by
  rw [orientedPairIntegral_eq T hT, diamondVolume]
  ring

/-- The ordering fraction: both orientations of distinct comparable pairs,
normalized by the squared diamond volume. -/
noncomputable def orderingFraction (T : ℝ) : ℝ :=
  2 * orientedPairIntegral T / diamondVolume T ^ 2

theorem diamondVolume_pos {T : ℝ} (hT : 0 < T) : 0 < diamondVolume T := by
  unfold diamondVolume
  positivity

/-- The four-dimensional ordering fraction is `1 / 10`. -/
theorem orderingFraction_eq (T : ℝ) (hT : 0 < T) : orderingFraction T = 1 / 10 := by
  have hV := (diamondVolume_pos hT).ne'
  rw [orderingFraction, orientedPairIntegral_eq_volume_sq T hT.le]
  field_simp
  ring

/-! ### The Myrheim-Meyer reference values -/

/-- The Myrheim-Meyer ordering fraction in dimension `d`, in the convention that
counts both orientations of distinct comparable pairs. -/
noncomputable def myrheimMeyer (d : ℝ) : ℝ :=
  Real.Gamma (d + 1) * Real.Gamma (d / 2) / (2 * Real.Gamma (3 * d / 2))

/-- `Γ(n + 1) = n!` read at a real numeral. -/
theorem Gamma_succ_nat (n : ℕ) (x : ℝ) (hx : (n : ℝ) + 1 = x) :
    Real.Gamma x = n.factorial := by
  rw [← hx]
  exact Real.Gamma_nat_eq_factorial n

theorem Gamma_two' : Real.Gamma 2 = 1 := by
  rw [Gamma_succ_nat 1 2 (by norm_num)]
  norm_num [Nat.factorial]

theorem Gamma_three : Real.Gamma 3 = 2 := by
  rw [Gamma_succ_nat 2 3 (by norm_num)]
  norm_num [Nat.factorial]

theorem Gamma_four : Real.Gamma 4 = 6 := by
  rw [Gamma_succ_nat 3 4 (by norm_num)]
  norm_num [Nat.factorial]

theorem Gamma_five : Real.Gamma 5 = 24 := by
  rw [Gamma_succ_nat 4 5 (by norm_num)]
  norm_num [Nat.factorial]

theorem Gamma_six : Real.Gamma 6 = 120 := by
  rw [Gamma_succ_nat 5 6 (by norm_num)]
  norm_num [Nat.factorial]

theorem Gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  rw [Real.Gamma_one_half_eq] at h
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, h]
  ring

theorem Gamma_nine_halves : Real.Gamma (9 / 2) = 105 * Real.sqrt Real.pi / 16 := by
  have h3 := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
  have h5 := Real.Gamma_add_one (s := (5 / 2 : ℝ)) (by norm_num)
  have h7 := Real.Gamma_add_one (s := (7 / 2 : ℝ)) (by norm_num)
  rw [show (9 / 2 : ℝ) = 7 / 2 + 1 by norm_num, h7,
    show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, h5,
    show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, h3, Gamma_three_halves]
  ring

/-- Myrheim-Meyer at `d = 4`: `Γ(5) Γ(2) / (2 Γ(6)) = 1 / 10`. -/
theorem myrheimMeyer_four : myrheimMeyer 4 = 1 / 10 := by
  unfold myrheimMeyer
  rw [show (4 : ℝ) + 1 = 5 by norm_num, show (4 : ℝ) / 2 = 2 by norm_num,
    show (3 : ℝ) * 4 / 2 = 6 by norm_num, Gamma_five, Gamma_two', Gamma_six]
  norm_num

/-- Myrheim-Meyer at `d = 2`: `Γ(3) Γ(1) / (2 Γ(3)) = 1 / 2`. -/
theorem myrheimMeyer_two : myrheimMeyer 2 = 1 / 2 := by
  unfold myrheimMeyer
  rw [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) / 2 = 1 by norm_num,
    show (3 : ℝ) * 2 / 2 = 3 by norm_num, Gamma_three, Real.Gamma_one]
  norm_num

/-- Myrheim-Meyer at `d = 3`: `Γ(4) Γ(3/2) / (2 Γ(9/2)) = 8 / 35`. -/
theorem myrheimMeyer_three : myrheimMeyer 3 = 8 / 35 := by
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold myrheimMeyer
  rw [show (3 : ℝ) + 1 = 4 by norm_num, show (3 : ℝ) * 3 / 2 = 9 / 2 by norm_num,
    Gamma_four, Gamma_three_halves, Gamma_nine_halves]
  field_simp
  ring

/-- The four-dimensional ordering fraction agrees with the Myrheim-Meyer value. -/
theorem orderingFraction_eq_myrheimMeyer (T : ℝ) (hT : 0 < T) :
    orderingFraction T = myrheimMeyer 4 := by
  rw [orderingFraction_eq T hT, myrheimMeyer_four]

#print axioms orderedPair_double_integral
#print axioms orientedPairIntegral_eq_volume_sq
#print axioms orderingFraction_eq
#print axioms myrheimMeyer_four
#print axioms myrheimMeyer_two
#print axioms myrheimMeyer_three
#print axioms orderingFraction_eq_myrheimMeyer

end OPH.OrderingFractionFourDimensional

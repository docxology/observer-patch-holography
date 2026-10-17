module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Seam-count area law: crossing reads per unit area

INPUTS.  A site density `n` (sites per unit volume) in `ℝ³`, a read radius
`a`, an oriented plane, and the complete-neighbour read law: an event at
layer `j + 1` reads every event at layer `j` within distance `a`.  A site at
depth `u ∈ [0, a]` below the plane has its upper neighbours in the spherical
cap of the ball `B(s, a)` beyond height `u`, whose volume is
`π (a - u)² (2a + u) / 3`.  The golden family has density `q³ / L³` and
squared read radius `L² / q`; the Planck-area dictionary reads one nat per
crossing read and identifies the cut entropy per unit area with
`1 / (4 ℓ²)`.

WHAT IS PROVED.  The cap-volume depth integral
`∫₀ᵃ π (a - u)² (2a + u) / 3 du = π a⁴ / 4` (`capVolume_integral`); the
crossing density, unordered crossing pairs per unit plane area and per layer
in the continuum limit, `n² ∫₀ᵃ capVolume a u du = (π / 4) n² a⁴`
(`crossingDensity_eq`); the golden identity
`(q³ / L³)² (L² / q)² = q⁴ / L²` (`golden_density_radius_identity`) and the
crossing count through a full cross-section of area `L²`, `π q⁴ / 4`
(`golden_crossing_count`); the dictionary
`(π / 4) n² a⁴ = 1 / (4 ℓ²)  →  ℓ² = 1 / (π n² a⁴)` (`planck_area_of_area_law`)
and its golden value `ℓ² = L² / (π q⁴)` (`golden_planck_length_sq`).

NOT CLAIMED.  The convergence of the finite crossing counts to the
continuum density is analytic and lives in the paper.  No horizon is
constructed, no temperature and no Hawking flux enter, and the length `ℓ`
is a declared calibration rather than a physical identification of the
Planck length.  The population, the read law and the layer structure are
inputs; these are integrals and field identities over `ℝ`.
-/

namespace OPH.CrossingReadAreaLaw

open Real intervalIntegral

/-! ### The cap-volume depth integral -/

/-- Volume of the spherical cap of the ball of radius `a` lying beyond a plane at
distance `u` from the centre: `π (a - u)² (2a + u) / 3`. -/
noncomputable def capVolume (a u : ℝ) : ℝ := Real.pi * (a - u) ^ 2 * (2 * a + u) / 3

/-- The cap volume as a polynomial in the depth. -/
theorem capVolume_eq (a u : ℝ) :
    capVolume a u = Real.pi * (2 * a ^ 3 - 3 * a ^ 2 * u + u ^ 3) / 3 := by
  unfold capVolume
  ring

/-- The primitive `π (2a³u - 3a²u²/2 + u⁴/4) / 3` differentiates to the cap volume. -/
theorem hasDerivAt_capPrimitive (a u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.pi * (2 * a ^ 3 * u - 3 * a ^ 2 * u ^ 2 / 2 + u ^ 4 / 4) / 3)
      (capVolume a u) u := by
  have h := (((((hasDerivAt_id' (x := u)).const_mul (2 * a ^ 3)).sub
    (((hasDerivAt_pow 2 u).const_mul (3 * a ^ 2)).div_const 2)).add
    ((hasDerivAt_pow 4 u).div_const 4)).const_mul Real.pi).div_const 3
  convert h using 1
  rw [capVolume_eq]
  norm_num
  ring

/-- The depth integral of the cap volume over `[0, a]` is `π a⁴ / 4`. -/
theorem capVolume_integral (a : ℝ) :
    ∫ u in (0:ℝ)..a, capVolume a u = Real.pi * a ^ 4 / 4 := by
  have hc : Continuous fun u : ℝ => capVolume a u := by
    unfold capVolume
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_capPrimitive a x)
    (hc.intervalIntegrable 0 a)]
  ring

/-! ### Crossing density -/

/-- Unordered crossing pairs per unit plane area and per layer, in the continuum
limit, for site density `n` and read radius `a`: the lower site at depth `u`
carries density `n`, its upper neighbours fill the cap with density `n`. -/
noncomputable def crossingDensity (n a : ℝ) : ℝ :=
  n ^ 2 * ∫ u in (0:ℝ)..a, capVolume a u

/-- The crossing density is `(π / 4) n² a⁴`. -/
theorem crossingDensity_eq (n a : ℝ) :
    crossingDensity n a = Real.pi / 4 * n ^ 2 * a ^ 4 := by
  rw [crossingDensity, capVolume_integral]
  ring

/-! ### The golden family -/

/-- Density `q³ / L³` of the golden population of `q³` sites in the cube of side `L`. -/
noncomputable def goldenDensity (q L : ℝ) : ℝ := q ^ 3 / L ^ 3

/-- Squared read radius `L² / q` of the golden family. -/
noncomputable def goldenRadiusSq (q L : ℝ) : ℝ := L ^ 2 / q

/-- `n² a⁴ = q⁴ / L²` on the golden family. -/
theorem golden_density_radius_identity (q L : ℝ) (hq : q ≠ 0) (hL : L ≠ 0) :
    goldenDensity q L ^ 2 * goldenRadiusSq q L ^ 2 = q ^ 4 / L ^ 2 := by
  unfold goldenDensity goldenRadiusSq
  field_simp

/-- Crossing pairs per layer through a full cross-section of the cube, area `L²`,
for a read radius whose square is `L² / q`: `π q⁴ / 4`. -/
theorem golden_crossing_count (q L a : ℝ) (hq : q ≠ 0) (hL : L ≠ 0)
    (ha : a ^ 2 = goldenRadiusSq q L) :
    L ^ 2 * crossingDensity (goldenDensity q L) a = Real.pi * q ^ 4 / 4 := by
  rw [crossingDensity_eq]
  have h4 : a ^ 4 = goldenRadiusSq q L ^ 2 := by
    rw [← ha]
    ring
  rw [h4]
  have hid := golden_density_radius_identity q L hq hL
  calc L ^ 2 * (Real.pi / 4 * goldenDensity q L ^ 2 * goldenRadiusSq q L ^ 2)
      = L ^ 2 * (Real.pi / 4 * (goldenDensity q L ^ 2 * goldenRadiusSq q L ^ 2)) := by ring
    _ = L ^ 2 * (Real.pi / 4 * (q ^ 4 / L ^ 2)) := by rw [hid]
    _ = Real.pi * q ^ 4 / 4 := by
        field_simp

/-! ### The Planck-area dictionary -/

/-- Reading one nat per crossing read, the cut entropy per unit area is
`(π / 4) n² a⁴`; identifying it with `1 / (4 ℓ²)` fixes `ℓ² = 1 / (π n² a⁴)`. -/
theorem planck_area_of_area_law (n a ℓ : ℝ) (hn : n ≠ 0) (ha : a ≠ 0) (hℓ : ℓ ≠ 0)
    (h : Real.pi / 4 * n ^ 2 * a ^ 4 = 1 / (4 * ℓ ^ 2)) :
    ℓ ^ 2 = 1 / (Real.pi * n ^ 2 * a ^ 4) := by
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp at h ⊢
  linear_combination h

/-- On the golden family the dictionary gives `ℓ² = L² / (π q⁴)`, that is
`ℓ = L / (√π q²)`. -/
theorem golden_planck_length_sq (q L a ℓ : ℝ) (hq : q ≠ 0) (hL : L ≠ 0) (hℓ : ℓ ≠ 0)
    (ha : a ^ 2 = goldenRadiusSq q L)
    (h : Real.pi / 4 * goldenDensity q L ^ 2 * a ^ 4 = 1 / (4 * ℓ ^ 2)) :
    ℓ ^ 2 = L ^ 2 / (Real.pi * q ^ 4) := by
  have hn : goldenDensity q L ≠ 0 := by
    unfold goldenDensity
    exact div_ne_zero (pow_ne_zero 3 hq) (pow_ne_zero 3 hL)
  have ha0 : a ≠ 0 := by
    intro h0
    have hr : goldenRadiusSq q L ≠ 0 := by
      unfold goldenRadiusSq
      exact div_ne_zero (pow_ne_zero 2 hL) hq
    apply hr
    rw [← ha, h0]
    ring
  have hℓ2 := planck_area_of_area_law (goldenDensity q L) a ℓ hn ha0 hℓ h
  have h4 : a ^ 4 = goldenRadiusSq q L ^ 2 := by
    rw [← ha]
    ring
  rw [hℓ2, h4, show Real.pi * goldenDensity q L ^ 2 * goldenRadiusSq q L ^ 2
      = Real.pi * (goldenDensity q L ^ 2 * goldenRadiusSq q L ^ 2) by ring,
    golden_density_radius_identity q L hq hL]
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp

#print axioms capVolume_integral
#print axioms crossingDensity_eq
#print axioms golden_density_radius_identity
#print axioms golden_crossing_count
#print axioms planck_area_of_area_law
#print axioms golden_planck_length_sq

end OPH.CrossingReadAreaLaw

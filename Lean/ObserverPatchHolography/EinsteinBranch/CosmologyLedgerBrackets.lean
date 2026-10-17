module
public import ObserverPatchHolography.EinsteinBranch.EdgeCenterTiltCocycle

@[expose] public section

/-!
# Cosmology ledger brackets

INPUTS.  The spectral-index display `nS P = 1 - P / 48` of
`EdgeCenterTiltCocycle` on the comparison pixel `1.630968 ≤ P ≤ 1.630973`
(`comparisonPixel`); the published central values and one-sigma widths of
the postdiction ledger rows, each a rational literal with its arXiv
identifier in the docstring of its row; the CODATA 2022 Planck length
`lP = 1.616255e-35 m` as the exact rational `1616255 / 10^41`; the exact
SI speed of light `c = 299792458 m/s`; the Planck 2018 central
`Λ = 1.0891e-52 m⁻²`; the two capacity candidates `N₁ = 3.2921e122` and
`N₂ = 3.3001e122`; the SPARC radial-acceleration calibration
`a0 = 1.1612569877e-10 m/s²` at `Υ = 0.5` with galaxy-bootstrap standard
deviation `0.0802e-10` (receipt
`code/cosmology/rar_deep_regime/receipts/sparc_full_rar_calibration.json`,
key `fits.disk_mass_to_light_0.5`); the DESI DR2 BAO + CMB retrospective
ΛCDM display `Λ lP² = 2.96770e-122 ± 0.03978e-122` and the `w0waCDM`
Gaussian moment summaries of the official DESI DR2 chains, rounded to six
significant digits (receipt
`code/cosmology/fixed_capacity_wlaw/runtime/official_desi_dr2_fz13_retrospective.json`,
keys `base_lcdm_capacity_display.combined.Lambda_lP2` and
`datasets.<combo>.combined`).  The Mathlib bounds
`3.141592 < π < 3.141593` (`Real.pi_gt_d6`, `Real.pi_lt_d6`) are the only
transcendental input.

WHAT IS PROVED.  Closed rational inequalities, each by `norm_num` or
`linarith` on the literals.  The sigma rule is the pair of definitions
`withinSigma v m s k := |v - m| < k * s` and
`outsideSigma v m s k := k * s < |v - m|`.

* Spectral index on the comparison pixel: within one sigma of Planck 2018
  (`ns_planck2018`), of SPT-3G D1 with Planck (`ns_spt3g_planck`), and of
  SPT + Planck + ACT (`ns_spt_planck_act`); outside one and within two
  sigma of ACT DR6 P-ACT (`ns_act_pact`); outside two and within three
  sigma of ACT DR6 P-ACT-LB (`ns_act_pactlb`), the tension row of the
  ledger.
* Running `dn_s / d ln k = 0`: within one sigma of Planck 2018
  (`running_planck2018`); outside one and within two sigma of ACT DR6
  P-ACT-LB (`running_act_pactlb`).
* Curvature `Ω_K = 0`: within one sigma of Planck 2018 + BAO
  (`curvature_planck_bao`); outside one and within two sigma of Planck
  2018 with lensing (`curvature_planck_lensing`); outside two and within
  three sigma of DESI DR2 + CMB (`curvature_desi_dr2_cmb`).
* Local non-Gaussianity `f_NL = 0`: within one sigma of Planck 2018
  (`fnl_planck2018`).
* Tensor ratio `r = 0` below the BK18 and PR4 bounds
  (`tensor_zero_below_bk18`, `tensor_zero_below_pr4`).
* Capacity dictionary `Λ = 3π / (N lP²)`: for both candidates the
  dictionary value is within one percent of the Planck central `Λ`
  (`lambda_capacityLow_within_percent`,
  `lambda_capacityHigh_within_percent`, through the general bracket
  `lambda_ratio_within`), and `Λ lP² = 3π / N` (`lambda_mul_lP_sq`) sits
  more than two and fewer than three posterior standard deviations below
  the DESI DR2 BAO + CMB display (`lambda_lP_sq_capacityLow_desi`,
  `lambda_lP_sq_capacityHigh_desi`, through `lambda_lP_sq_desi_bracket`).
* Horizon acceleration: `c⁴ Λ / 3` lies between `(5.4150e-10)²` and
  `(5.4155e-10)²` (`aDSsq_bracket`), the squared ratio `a0² / (c⁴ Λ / 3)`
  at the SPARC central value lies between `0.2144²` and `0.2145²`
  (`a0_ratio_sq_bracket`), and for every `a0` in the one-sigma band
  `[1.0810e-10, 1.2415e-10]` it lies between `0.199²` and `0.230²`
  (`a0_band_ratio_sq_bracket`).
* DESI DR2 `w0waCDM` moment diagnostic: for each of the four data
  combinations the squared Mahalanobis distance of the fixed-capacity
  point `(w0, wa) = (-1, 0)` from the Gaussian moment summary lies in the
  stated two-sided bracket (`mahal_bao_cmb`, `mahal_bao_cmb_pantheonplus`,
  `mahal_bao_cmb_union3`, `mahal_bao_cmb_desy5`) and exceeds `9`
  (`mahal_bao_cmb_gt_nine`, `mahal_bao_cmb_pantheonplus_gt_nine`,
  `mahal_bao_cmb_union3_gt_nine`, `mahal_bao_cmb_desy5_gt_nine`): the
  point lies outside the `Δχ² = 9` ellipse of the two-parameter Gaussian
  moment summary.

NOT CLAIMED.  Every measurement is an input literal; nothing here scores
data, and the data named are seen data, so the brackets are postdiction
displays with no evidential weight of their own.  The Mahalanobis rows are
diagnostics of a Gaussian moment summary of the official chains; the
collaboration's Δχ² and model evidence are separate quantities that these
rows do not compute.  The fixed-capacity point coincides with the ΛCDM
null, so compatibility on these rows would support nothing beyond ΛCDM,
and the rows state exclusion at the `Δχ² = 9` contour of the moment
ellipse only.  The one-percent and DESI brackets of the capacity
dictionary compare two declared candidate capacities with a Planck central
value and a retrospective display; no capacity is derived here, the
Planck-central `Λ` carries no width in these rows, and the DESI display is
a sample-level retrospective posterior summary.  The SPARC `a0` is a
calibration at a declared mass-to-light ratio; the receipt marks it as
source-independent.  The value of `P` is a pixel hypothesis of every
spectral-index row and is derived nowhere in this module.
-/

namespace OPH.EinsteinBranch.CosmologyLedger

open OPH.EinsteinBranch.EdgeCenterTilt

noncomputable section

/-! ## The sigma rule -/

/-- `value` lies within `k` standard deviations of `mean`. -/
def withinSigma (value mean sigma k : ℝ) : Prop := |value - mean| < k * sigma

/-- `value` lies more than `k` standard deviations from `mean`. -/
def outsideSigma (value mean sigma k : ℝ) : Prop := k * sigma < |value - mean|

theorem withinSigma_iff {value mean sigma k : ℝ} :
    withinSigma value mean sigma k ↔
      -(k * sigma) < value - mean ∧ value - mean < k * sigma := by
  unfold withinSigma
  exact abs_lt

theorem outsideSigma_of_below {value mean sigma k : ℝ}
    (h : k * sigma < mean - value) : outsideSigma value mean sigma k := by
  unfold outsideSigma
  exact lt_abs.mpr (Or.inr (by linarith))

theorem outsideSigma_of_above {value mean sigma k : ℝ}
    (h : k * sigma < value - mean) : outsideSigma value mean sigma k := by
  unfold outsideSigma
  exact lt_abs.mpr (Or.inl h)

/-- The comparison pixel of the edge-center row, `1.630968 ≤ P ≤ 1.630973`. -/
def comparisonPixel (P : ℝ) : Prop := 1.630968 ≤ P ∧ P ≤ 1.630973

/-! ## Spectral index rows -/

/-- Planck 2018 TT,TE,EE+lowE+lensing, `n_s = 0.9649 ± 0.0042`
(arXiv:1807.06209): within one sigma. -/
theorem ns_planck2018 {P : ℝ} (hP : comparisonPixel P) :
    withinSigma (nS P) 0.9649 0.0042 1 := by
  obtain ⟨h₁, h₂⟩ := hP
  rw [withinSigma_iff]
  unfold nS
  constructor <;> linarith

/-- SPT-3G D1 with Planck, `n_s = 0.9636 ± 0.0035` (arXiv:2506.20707):
within one sigma. -/
theorem ns_spt3g_planck {P : ℝ} (hP : comparisonPixel P) :
    withinSigma (nS P) 0.9636 0.0035 1 := by
  obtain ⟨h₁, h₂⟩ := hP
  rw [withinSigma_iff]
  unfold nS
  constructor <;> linarith

/-- SPT + Planck + ACT, `n_s = 0.9684 ± 0.0030` (arXiv:2506.20707): within
one sigma. -/
theorem ns_spt_planck_act {P : ℝ} (hP : comparisonPixel P) :
    withinSigma (nS P) 0.9684 0.0030 1 := by
  obtain ⟨h₁, h₂⟩ := hP
  rw [withinSigma_iff]
  unfold nS
  constructor <;> linarith

/-- ACT DR6 P-ACT, `n_s = 0.9709 ± 0.0038` (arXiv:2503.14454): outside one
sigma, within two. -/
theorem ns_act_pact {P : ℝ} (hP : comparisonPixel P) :
    outsideSigma (nS P) 0.9709 0.0038 1 ∧ withinSigma (nS P) 0.9709 0.0038 2 := by
  obtain ⟨h₁, h₂⟩ := hP
  refine ⟨outsideSigma_of_below ?_, ?_⟩
  · unfold nS
    linarith
  · rw [withinSigma_iff]
    unfold nS
    constructor <;> linarith

/-- ACT DR6 P-ACT-LB, `n_s = 0.9743 ± 0.0034` (arXiv:2503.14454): outside
two sigma, within three.  This is the tension row of the ledger. -/
theorem ns_act_pactlb {P : ℝ} (hP : comparisonPixel P) :
    outsideSigma (nS P) 0.9743 0.0034 2 ∧ withinSigma (nS P) 0.9743 0.0034 3 := by
  obtain ⟨h₁, h₂⟩ := hP
  refine ⟨outsideSigma_of_below ?_, ?_⟩
  · unfold nS
    linarith
  · rw [withinSigma_iff]
    unfold nS
    constructor <;> linarith

/-! ## Running, curvature, non-Gaussianity, tensors -/

/-- Running `dn_s / d ln k = 0` against Planck 2018 `-0.0045 ± 0.0067`
(arXiv:1807.06211): within one sigma. -/
theorem running_planck2018 : withinSigma 0 (-0.0045) 0.0067 1 := by
  rw [withinSigma_iff]
  constructor <;> norm_num

/-- Running `0` against ACT DR6 P-ACT-LB `0.0062 ± 0.0052`
(arXiv:2503.14454): outside one sigma, within two. -/
theorem running_act_pactlb :
    outsideSigma 0 0.0062 0.0052 1 ∧ withinSigma 0 0.0062 0.0052 2 := by
  refine ⟨outsideSigma_of_below (by norm_num), ?_⟩
  rw [withinSigma_iff]
  constructor <;> norm_num

/-- Curvature `Ω_K = 0` against Planck 2018 + BAO `0.0007 ± 0.0019`
(arXiv:1807.06209): within one sigma. -/
theorem curvature_planck_bao : withinSigma 0 0.0007 0.0019 1 := by
  rw [withinSigma_iff]
  constructor <;> norm_num

/-- Curvature `0` against Planck 2018 with lensing `-0.0106 ± 0.0065`
(arXiv:1807.06209): outside one sigma, within two. -/
theorem curvature_planck_lensing :
    outsideSigma 0 (-0.0106) 0.0065 1 ∧ withinSigma 0 (-0.0106) 0.0065 2 := by
  refine ⟨outsideSigma_of_above (by norm_num), ?_⟩
  rw [withinSigma_iff]
  constructor <;> norm_num

/-- Curvature `0` against DESI DR2 + CMB `0.0023 ± 0.0011`
(arXiv:2503.14738): outside two sigma, within three. -/
theorem curvature_desi_dr2_cmb :
    outsideSigma 0 0.0023 0.0011 2 ∧ withinSigma 0 0.0023 0.0011 3 := by
  refine ⟨outsideSigma_of_below (by norm_num), ?_⟩
  rw [withinSigma_iff]
  constructor <;> norm_num

/-- Local non-Gaussianity `f_NL = 0` against Planck 2018 `-0.9 ± 5.1`
(arXiv:1905.05697): within one sigma. -/
theorem fnl_planck2018 : withinSigma 0 (-0.9) 5.1 1 := by
  rw [withinSigma_iff]
  constructor <;> norm_num

/-- Tensor ratio `r = 0` below the BK18 bound `r < 0.036`
(BICEP/Keck 2021). -/
theorem tensor_zero_below_bk18 : (0 : ℝ) < 0.036 := by norm_num

/-- Tensor ratio `r = 0` below the Planck PR4 + BK18 bound `r < 0.032`
(Tristram et al. 2022). -/
theorem tensor_zero_below_pr4 : (0 : ℝ) < 0.032 := by norm_num

/-! ## Capacity dictionary -/

/-- CODATA 2022 Planck length in metres, `1.616255e-35`, as an exact
rational. -/
def lP : ℝ := 1616255 / 10 ^ 41

/-- The de Sitter capacity dictionary `Λ = 3π / (N lP²)`. -/
def Lambda (N : ℝ) : ℝ := 3 * Real.pi / (N * lP ^ 2)

/-- Planck 2018 central `Λ = 1.0891e-52 m⁻²`. -/
def lambdaPlanck : ℝ := 1.0891e-52

/-- Lower capacity candidate `N₁ = 3.2921e122`. -/
def capacityLow : ℝ := 3.2921e122

/-- Upper capacity candidate `N₂ = 3.3001e122`. -/
def capacityHigh : ℝ := 3.3001e122

theorem lP_pos : 0 < lP := by
  unfold lP
  norm_num

theorem lambdaPlanck_pos : 0 < lambdaPlanck := by
  unfold lambdaPlanck
  norm_num

/-- General one-percent bracket: with the rational prefactor
`K = 3 / (N lP² Λ)`, the two `π` bounds give `|Λ(N) / Λ - 1| < 0.01`
whenever `-0.01 < 3.141592 K - 1` and `3.141593 K - 1 < 0.01`. -/
theorem lambda_ratio_within {N : ℝ} (hN : 0 < N)
    (hlo : -0.01 < 3.141592 * (3 / (N * lP ^ 2 * lambdaPlanck)) - 1)
    (hhi : 3.141593 * (3 / (N * lP ^ 2 * lambdaPlanck)) - 1 < 0.01) :
    |Lambda N / lambdaPlanck - 1| < 0.01 := by
  have hK : 0 < 3 / (N * lP ^ 2 * lambdaPlanck) :=
    div_pos (by norm_num) (mul_pos (mul_pos hN (pow_pos lP_pos 2)) lambdaPlanck_pos)
  have heq : Lambda N / lambdaPlanck - 1
      = Real.pi * (3 / (N * lP ^ 2 * lambdaPlanck)) - 1 := by
    unfold Lambda
    ring
  rw [heq, abs_lt]
  have h1 := mul_lt_mul_of_pos_right Real.pi_gt_d6 hK
  have h2 := mul_lt_mul_of_pos_right Real.pi_lt_d6 hK
  constructor <;> linarith

/-- `Λ(N₁)` is within one percent of the Planck central `Λ`. -/
theorem lambda_capacityLow_within_percent :
    |Lambda capacityLow / lambdaPlanck - 1| < 0.01 :=
  lambda_ratio_within (by unfold capacityLow; norm_num)
    (by unfold capacityLow lP lambdaPlanck; norm_num)
    (by unfold capacityLow lP lambdaPlanck; norm_num)

/-- `Λ(N₂)` is within one percent of the Planck central `Λ`. -/
theorem lambda_capacityHigh_within_percent :
    |Lambda capacityHigh / lambdaPlanck - 1| < 0.01 :=
  lambda_ratio_within (by unfold capacityHigh; norm_num)
    (by unfold capacityHigh lP lambdaPlanck; norm_num)
    (by unfold capacityHigh lP lambdaPlanck; norm_num)

/-- Under the dictionary, `Λ lP² = 3π / N`. -/
theorem lambda_mul_lP_sq (N : ℝ) : Lambda N * lP ^ 2 = Real.pi * (3 / N) := by
  have h : lP ^ 2 ≠ 0 := pow_ne_zero 2 lP_pos.ne'
  unfold Lambda
  calc 3 * Real.pi / (N * lP ^ 2) * lP ^ 2
      = Real.pi * (3 / N) * (lP ^ 2 / lP ^ 2) := by ring
    _ = Real.pi * (3 / N) := by rw [div_self h, mul_one]

/-- DESI DR2 BAO + CMB retrospective ΛCDM display of `Λ lP²`: weighted
mean `2.96770e-122` (receipt key
`base_lcdm_capacity_display.combined.Lambda_lP2.weighted_mean`). -/
def desiLambdaMean : ℝ := 2.9677e-122

/-- DESI DR2 BAO + CMB retrospective ΛCDM display of `Λ lP²`: weighted
standard deviation `0.03978e-122` (receipt key
`base_lcdm_capacity_display.combined.Lambda_lP2.weighted_std`). -/
def desiLambdaStd : ℝ := 3.978e-124

/-- General DESI bracket: with the `π` bounds, `3π / N` lies more than two
and fewer than three display standard deviations below the display mean
whenever the rational hypotheses on `3 / N` hold. -/
theorem lambda_lP_sq_desi_bracket {N : ℝ} (hN : 0 < N)
    (h2 : 2 * desiLambdaStd < desiLambdaMean - 3.141593 * (3 / N))
    (h3 : desiLambdaMean - 3.141592 * (3 / N) < 3 * desiLambdaStd) :
    outsideSigma (Lambda N * lP ^ 2) desiLambdaMean desiLambdaStd 2 ∧
      withinSigma (Lambda N * lP ^ 2) desiLambdaMean desiLambdaStd 3 := by
  rw [lambda_mul_lP_sq N]
  have hK : 0 < 3 / N := div_pos (by norm_num) hN
  have hlo := mul_lt_mul_of_pos_right Real.pi_gt_d6 hK
  have hhi := mul_lt_mul_of_pos_right Real.pi_lt_d6 hK
  have hσ : 0 < desiLambdaStd := by
    unfold desiLambdaStd
    norm_num
  refine ⟨outsideSigma_of_below (by linarith), ?_⟩
  rw [withinSigma_iff]
  constructor <;> linarith

/-- `Λ(N₁) lP²` is more than two and fewer than three display standard
deviations below the DESI DR2 BAO + CMB display. -/
theorem lambda_lP_sq_capacityLow_desi :
    outsideSigma (Lambda capacityLow * lP ^ 2) desiLambdaMean desiLambdaStd 2 ∧
      withinSigma (Lambda capacityLow * lP ^ 2) desiLambdaMean desiLambdaStd 3 :=
  lambda_lP_sq_desi_bracket (by unfold capacityLow; norm_num)
    (by unfold capacityLow desiLambdaMean desiLambdaStd; norm_num)
    (by unfold capacityLow desiLambdaMean desiLambdaStd; norm_num)

/-- `Λ(N₂) lP²` is more than two and fewer than three display standard
deviations below the DESI DR2 BAO + CMB display. -/
theorem lambda_lP_sq_capacityHigh_desi :
    outsideSigma (Lambda capacityHigh * lP ^ 2) desiLambdaMean desiLambdaStd 2 ∧
      withinSigma (Lambda capacityHigh * lP ^ 2) desiLambdaMean desiLambdaStd 3 :=
  lambda_lP_sq_desi_bracket (by unfold capacityHigh; norm_num)
    (by unfold capacityHigh desiLambdaMean desiLambdaStd; norm_num)
    (by unfold capacityHigh desiLambdaMean desiLambdaStd; norm_num)

/-! ## Horizon acceleration scale -/

/-- Exact SI speed of light, `299792458 m/s`. -/
def cLight : ℝ := 299792458

/-- Squared de Sitter horizon acceleration, `c⁴ Λ / 3`, at the Planck
central `Λ`. -/
def aDSsq : ℝ := cLight ^ 4 * lambdaPlanck / 3

/-- `c⁴ Λ / 3` lies between `(5.4150e-10)²` and `(5.4155e-10)²`, so the
horizon acceleration lies in `(5.4150e-10, 5.4155e-10) m/s²`. -/
theorem aDSsq_bracket : (5.4150e-10 : ℝ) ^ 2 < aDSsq ∧ aDSsq < (5.4155e-10 : ℝ) ^ 2 := by
  unfold aDSsq cLight lambdaPlanck
  constructor <;> norm_num

/-- SPARC radial-acceleration calibration at `Υ = 0.5`,
`a0 = 1.1612569877e-10 m/s²` (receipt key
`fits.disk_mass_to_light_0.5.a0_si_m_per_s2`). -/
def a0Sparc : ℝ := 1.1612569877e-10

/-- The squared ratio `a0² / (c⁴ Λ / 3)` at the SPARC central value lies
between `0.2144²` and `0.2145²`. -/
theorem a0_ratio_sq_bracket :
    (0.2144 : ℝ) ^ 2 < a0Sparc ^ 2 / aDSsq ∧ a0Sparc ^ 2 / aDSsq < (0.2145 : ℝ) ^ 2 := by
  unfold a0Sparc aDSsq cLight lambdaPlanck
  constructor <;> norm_num

/-- Over the one-sigma band `a0 ∈ [1.0810e-10, 1.2415e-10]` (central value
plus or minus the galaxy-bootstrap standard deviation `0.0802e-10`), the
squared ratio `a0² / (c⁴ Λ / 3)` lies between `0.199²` and `0.230²`. -/
theorem a0_band_ratio_sq_bracket {a0 : ℝ} (hlo : 1.0810e-10 ≤ a0) (hhi : a0 ≤ 1.2415e-10) :
    (0.199 : ℝ) ^ 2 < a0 ^ 2 / aDSsq ∧ a0 ^ 2 / aDSsq < (0.230 : ℝ) ^ 2 := by
  have hD : 0 < aDSsq := by
    unfold aDSsq cLight lambdaPlanck
    norm_num
  have h0 : (0 : ℝ) ≤ 1.0810e-10 := by norm_num
  have ha0 : 0 ≤ a0 := le_trans h0 hlo
  have hsqlo : (1.0810e-10 : ℝ) ^ 2 ≤ a0 ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hlo hlo h0 ha0
  have hsqhi : a0 ^ 2 ≤ (1.2415e-10 : ℝ) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hhi hhi ha0 (by norm_num)
  have hDlo : (0.199 : ℝ) ^ 2 * aDSsq < (1.0810e-10 : ℝ) ^ 2 := by
    unfold aDSsq cLight lambdaPlanck
    norm_num
  have hDhi : (1.2415e-10 : ℝ) ^ 2 < (0.230 : ℝ) ^ 2 * aDSsq := by
    unfold aDSsq cLight lambdaPlanck
    norm_num
  constructor
  · rw [lt_div_iff₀ hD]
    linarith
  · rw [div_lt_iff₀ hD]
    linarith

/-! ## DESI DR2 fixed-point Gaussian moment diagnostic

The squared Mahalanobis distance of a point with offsets `(d0, da)` from a
two-parameter Gaussian with standard deviations `(s0, sa)` and correlation
`ρ`.  The rows below evaluate it at the fixed-capacity point
`(w0, wa) = (-1, 0)` against the moment summaries of the official DESI DR2
`w0waCDM` chains.  These are diagnostics of a Gaussian moment summary of
seen data; the fixed-capacity point is the ΛCDM null. -/

/-- Squared Mahalanobis distance for a bivariate Gaussian moment summary. -/
def mahal (d0 da s0 sa ρ : ℝ) : ℝ :=
  ((d0 / s0) ^ 2 - 2 * ρ * (d0 / s0) * (da / sa) + (da / sa) ^ 2) / (1 - ρ ^ 2)

/-- The diagnostic at the fixed-capacity point: `d0 = -1 - w0`, `da = 0 - wa`. -/
def fixedPointMahal (w0 wa s0 sa ρ : ℝ) : ℝ := mahal (-1 - w0) (0 - wa) s0 sa ρ

/-- DESI DR2 BAO + CMB (receipt `datasets.DESI_DR2_BAO+CMB.combined`,
`w0_mean -0.4191700669`, `wa_mean -1.7464744072`, `w0_std 0.2052816995`,
`wa_std 0.5797414940`, `w0_wa_correlation -0.9778258728`, receipt
`mahalanobis_squared 9.3835`): `9.3 < m < 9.5` at six significant digits. -/
theorem mahal_bao_cmb :
    9.3 < fixedPointMahal (-0.419170) (-1.74647) 0.205282 0.579741 (-0.977826) ∧
      fixedPointMahal (-0.419170) (-1.74647) 0.205282 0.579741 (-0.977826) < 9.5 := by
  unfold fixedPointMahal mahal
  constructor <;> norm_num

/-- DESI DR2 BAO + CMB + Pantheon+ (receipt
`datasets.DESI_DR2_BAO+CMB+PantheonPlus.combined`, `w0_mean -0.8379581981`,
`wa_mean -0.6176883263`, `w0_std 0.0548921202`, `wa_std 0.2068079740`,
`w0_wa_correlation -0.8927674701`, receipt `mahalanobis_squared 9.3224`):
`9.2 < m < 9.4`. -/
theorem mahal_bao_cmb_pantheonplus :
    9.2 < fixedPointMahal (-0.837958) (-0.617688) 0.0548921 0.206808 (-0.892767) ∧
      fixedPointMahal (-0.837958) (-0.617688) 0.0548921 0.206808 (-0.892767) < 9.4 := by
  unfold fixedPointMahal mahal
  constructor <;> norm_num

/-- DESI DR2 BAO + CMB + Union3 (receipt
`datasets.DESI_DR2_BAO+CMB+Union3.combined`, `w0_mean -0.6656627619`,
`wa_mean -1.0891890177`, `w0_std 0.0886834888`, `wa_std 0.2943212861`,
`w0_wa_correlation -0.9335612030`, receipt `mahalanobis_squared 14.4684`):
`14.3 < m < 14.6`. -/
theorem mahal_bao_cmb_union3 :
    14.3 < fixedPointMahal (-0.665663) (-1.08919) 0.0886835 0.294321 (-0.933561) ∧
      fixedPointMahal (-0.665663) (-1.08919) 0.0886835 0.294321 (-0.933561) < 14.6 := by
  unfold fixedPointMahal mahal
  constructor <;> norm_num

/-- DESI DR2 BAO + CMB + DESY5 (receipt
`datasets.DESI_DR2_BAO+CMB+DESY5.combined`, `w0_mean -0.7523480182`,
`wa_mean -0.8612751004`, `w0_std 0.0572774799`, `wa_std 0.2221688374`,
`w0_wa_correlation -0.9071818940`, receipt `mahalanobis_squared 18.7064`):
`18.5 < m < 18.9`. -/
theorem mahal_bao_cmb_desy5 :
    18.5 < fixedPointMahal (-0.752348) (-0.861275) 0.0572775 0.222169 (-0.907182) ∧
      fixedPointMahal (-0.752348) (-0.861275) 0.0572775 0.222169 (-0.907182) < 18.9 := by
  unfold fixedPointMahal mahal
  constructor <;> norm_num

/-- BAO + CMB: the fixed-capacity point lies outside the `Δχ² = 9` moment
ellipse. -/
theorem mahal_bao_cmb_gt_nine :
    9 < fixedPointMahal (-0.419170) (-1.74647) 0.205282 0.579741 (-0.977826) :=
  lt_trans (by norm_num) mahal_bao_cmb.1

/-- BAO + CMB + Pantheon+: outside the `Δχ² = 9` moment ellipse. -/
theorem mahal_bao_cmb_pantheonplus_gt_nine :
    9 < fixedPointMahal (-0.837958) (-0.617688) 0.0548921 0.206808 (-0.892767) :=
  lt_trans (by norm_num) mahal_bao_cmb_pantheonplus.1

/-- BAO + CMB + Union3: outside the `Δχ² = 9` moment ellipse. -/
theorem mahal_bao_cmb_union3_gt_nine :
    9 < fixedPointMahal (-0.665663) (-1.08919) 0.0886835 0.294321 (-0.933561) :=
  lt_trans (by norm_num) mahal_bao_cmb_union3.1

/-- BAO + CMB + DESY5: outside the `Δχ² = 9` moment ellipse. -/
theorem mahal_bao_cmb_desy5_gt_nine :
    9 < fixedPointMahal (-0.752348) (-0.861275) 0.0572775 0.222169 (-0.907182) :=
  lt_trans (by norm_num) mahal_bao_cmb_desy5.1

/-! ## Per-theorem axiom audit -/

#print axioms ns_planck2018
#print axioms ns_act_pactlb
#print axioms curvature_desi_dr2_cmb
#print axioms lambda_capacityLow_within_percent
#print axioms lambda_lP_sq_capacityLow_desi
#print axioms aDSsq_bracket
#print axioms a0_ratio_sq_bracket
#print axioms a0_band_ratio_sq_bracket
#print axioms mahal_bao_cmb
#print axioms mahal_bao_cmb_gt_nine

end

end OPH.EinsteinBranch.CosmologyLedger

module
public import Mathlib

@[expose] public section

/-!
# Edge-center tilt from the survival cocycle

INPUTS.  A positive continuous multiplicative cocycle `u : ℝ → ℝ` on the
logarithmic refinement thickness, `u (s + t) = u s * u t`, packaged as
`SurvivalCocycle` (the scalar-conditioned covariance-survival factor of the
screen-spectrum package, theorems "refinement-semigroup tilt" and
"edge-center tilt and repair-clock reconciliation" of
`paper/tex_fragments/SCREEN_SPECTRUM_THEOREMS.tex`).  For the tilt receipt,
the value of the derivative of `u` at `0`.  For the edge-center row, the
source-facing half-collar generator density `-u' 0 = P / 48`, the coarea
half of the full-collar density `P / 24` (`half_of_full`).  The constant
`P` is a real parameter of every statement; the comparison pixel
`1.630968 ≤ P ≤ 1.630973` enters only the numeric corollary.

WHAT IS PROVED.  Every survival cocycle is an exponential: with the tilt
`θ = -log (u 1)`, `u s = exp (-(θ * s))` for all `s`
(`SurvivalCocycle.u_eq_exp`, `SurvivalCocycle.exists_exp`), the exponent
is unique (`SurvivalCocycle.exp_unique`), and `u 0 = 1`
(`SurvivalCocycle.u_zero`).  The route is the continuous Cauchy equation:
`log ∘ u` is an additive continuous map `ℝ →+ ℝ`, hence real linear by
`AddMonoidHom.toRealLinearMap`, hence equal to `s * log (u 1)`
(`SurvivalCocycle.log_u_eq`).  The cocycle is differentiable at `0` with
derivative `-θ` (`SurvivalCocycle.hasDerivAt_zero`), so a derivative `d`
of `u` at `0` fixes the exponent to `θ = -d`
(`SurvivalCocycle.tilt_eq_of_hasDerivAt`,
`SurvivalCocycle.tilt_of_hasDerivAt`, through `HasDerivAt.unique`).  With
the half-collar density `-u' 0 = P / 48` the cocycle is
`u s = exp (-(P / 48 * s))` and the spectral index `nS P = 1 - P / 48`
equals `1 - θ` (`edgeCenter_tilt`).  The refinement-semigroup form: a
function `lam` positive and continuous on `(0, ∞)` with
`lam (b₁ * b₂) = lam b₁ * lam b₂` there is a power `lam b = b ^ (-θ)` for
all `b > 0` (`refinementSemigroup_tilt`), with `θ` unique
(`refinementSemigroup_tilt_unique`), by transport along `t ↦ exp t`.
Numeric corollary: on the comparison pixel,
`0.9660213 < nS P < 0.9660216` (`nS_at_comparison_pixel`).

NOT CLAIMED.  The cocycle law, its continuity, and the generator density
`P / 48` are inputs; nothing here derives them from the screen dynamics or
from a value of `P`.  No comparison to a measured spectral index is made in
this module (the ledger brackets live in `CosmologyLedgerBrackets`), and
`nS` is a definition, the display `1 - P / 48`, with no claim about the
scalar covariance mode it labels.  The repair-clock coordinate
`κ_rep^edge = P / (48 (P - φ))` of the same theorem is an algebraic
relabeling and is not formalized here.
-/

namespace OPH.EinsteinBranch.EdgeCenterTilt

noncomputable section

/-! ## The survival cocycle -/

/-- A positive continuous multiplicative cocycle on the logarithmic
refinement thickness: the scalar-conditioned covariance-survival factor
across a collar of thickness `s`.  The cocycle law composes collars;
positivity and continuity are the receipt's regularity inputs. -/
structure SurvivalCocycle where
  /-- Survival factor across a collar of logarithmic thickness `s`. -/
  u : ℝ → ℝ
  /-- Positivity of the survival factor. -/
  pos : ∀ s, 0 < u s
  /-- The cocycle law: collars compose multiplicatively. -/
  mul : ∀ s t, u (s + t) = u s * u t
  /-- Continuity in the thickness. -/
  cont : Continuous u

namespace SurvivalCocycle

variable (S : SurvivalCocycle)

/-- The empty collar has unit survival. -/
theorem u_zero : S.u 0 = 1 := by
  have h : S.u 0 * S.u 0 = S.u 0 * 1 := by
    rw [mul_one, ← S.mul, add_zero]
  exact mul_left_cancel₀ (S.pos 0).ne' h

/-- The logarithm of the cocycle as an additive map `ℝ →+ ℝ`. -/
def logHom : ℝ →+ ℝ :=
  AddMonoidHom.mk' (fun s => Real.log (S.u s)) fun s t => by
    show Real.log (S.u (s + t)) = Real.log (S.u s) + Real.log (S.u t)
    rw [S.mul s t, Real.log_mul (S.pos s).ne' (S.pos t).ne']

theorem logHom_apply (s : ℝ) : S.logHom s = Real.log (S.u s) := rfl

theorem logHom_continuous : Continuous S.logHom := by
  have h : (⇑S.logHom : ℝ → ℝ) = fun s => Real.log (S.u s) := rfl
  rw [h]
  exact S.cont.log fun s => (S.pos s).ne'

/-- The continuous Cauchy equation: the log-cocycle is real linear,
`log (u s) = s * log (u 1)`. -/
theorem log_u_eq (s : ℝ) : Real.log (S.u s) = s * Real.log (S.u 1) := by
  let L : ℝ →L[ℝ] ℝ := S.logHom.toRealLinearMap S.logHom_continuous
  have hL : ∀ x, L x = Real.log (S.u x) := fun x =>
    congrFun (AddMonoidHom.coe_toRealLinearMap S.logHom S.logHom_continuous) x
  have hs : L (s • (1 : ℝ)) = s • L 1 := map_smul L s (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at hs
  rw [hL, hL] at hs
  exact hs

/-- The tilt of the cocycle, `θ = -log (u 1)`. -/
def tilt : ℝ := -Real.log (S.u 1)

/-- Every survival cocycle is the exponential of its tilt,
`u s = exp (-(θ * s))`. -/
theorem u_eq_exp (s : ℝ) : S.u s = Real.exp (-(S.tilt * s)) := by
  rw [← Real.exp_log (S.pos s), S.log_u_eq s]
  unfold tilt
  congr 1
  ring

/-- Existence of the exponent. -/
theorem exists_exp : ∃ θ : ℝ, ∀ s, S.u s = Real.exp (-(θ * s)) :=
  ⟨S.tilt, S.u_eq_exp⟩

/-- Uniqueness of the exponent, by comparison at `s = 1` and injectivity
of `exp`. -/
theorem exp_unique {θ₁ θ₂ : ℝ} (h₁ : ∀ s, S.u s = Real.exp (-(θ₁ * s)))
    (h₂ : ∀ s, S.u s = Real.exp (-(θ₂ * s))) : θ₁ = θ₂ := by
  have h := Real.exp_injective ((h₁ 1).symm.trans (h₂ 1))
  linarith

/-- Any exponent representing the cocycle is its tilt. -/
theorem tilt_eq_of_exp {θ : ℝ} (h : ∀ s, S.u s = Real.exp (-(θ * s))) :
    S.tilt = θ :=
  S.exp_unique S.u_eq_exp h

/-- The cocycle is differentiable at `0` with derivative `-θ`. -/
theorem hasDerivAt_zero : HasDerivAt S.u (-S.tilt) 0 := by
  have hfun : S.u = fun s => Real.exp (-(S.tilt * s)) := funext S.u_eq_exp
  have h1 : HasDerivAt (fun s : ℝ => -(S.tilt * s)) (-S.tilt) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_mul S.tilt).neg
    convert h using 1
    · funext s
      rfl
    · simp
  have h2 := h1.exp
  rw [hfun]
  simpa using h2

/-- A derivative `d` of the cocycle at `0` fixes the tilt to `-d`. -/
theorem tilt_eq_of_hasDerivAt {d : ℝ} (hd : HasDerivAt S.u d 0) :
    S.tilt = -d := by
  have h := hd.unique S.hasDerivAt_zero
  linarith

/-- Tilt from the generator: if `u' 0 = d` then `u s = exp (-(-d * s))`
for every `s`. -/
theorem tilt_of_hasDerivAt {d : ℝ} (hd : HasDerivAt S.u d 0) :
    ∀ s, S.u s = Real.exp (-(-d * s)) := by
  intro s
  rw [S.u_eq_exp s, S.tilt_eq_of_hasDerivAt hd]

end SurvivalCocycle

/-! ## The edge-center row -/

/-- The spectral-index display of the edge-center row, `n_s = 1 - P / 48`. -/
def nS (P : ℝ) : ℝ := 1 - P / 48

/-- Orientation-reversal coarea identity: the source-facing half-collar
generator density is half the full-collar density `P / 24`. -/
theorem half_of_full (P : ℝ) : -(P / 24) / 2 = -(P / 48) := by ring

/-- Edge-center tilt: with the half-collar generator density
`-u' 0 = P / 48`, the cocycle is `u s = exp (-(P / 48 * s))` and the
spectral index `nS P = 1 - P / 48` equals `1 - θ` for the tilt `θ`. -/
theorem edgeCenter_tilt (S : SurvivalCocycle) (P : ℝ)
    (hd : HasDerivAt S.u (-(P / 48)) 0) :
    (∀ s, S.u s = Real.exp (-(P / 48 * s))) ∧ nS P = 1 - S.tilt := by
  have ht : S.tilt = P / 48 := by
    have h := S.tilt_eq_of_hasDerivAt hd
    linarith
  exact ⟨fun s => by rw [S.u_eq_exp s, ht], by unfold nS; rw [ht]⟩

/-! ## The refinement-semigroup form -/

/-- The survival cocycle transported from a multiplicative refinement
eigenvalue along `t ↦ exp t`. -/
def SurvivalCocycle.ofRefinement (lam : ℝ → ℝ) (hpos : ∀ b, 0 < b → 0 < lam b)
    (hmul : ∀ b₁ b₂, 0 < b₁ → 0 < b₂ → lam (b₁ * b₂) = lam b₁ * lam b₂)
    (hcont : ContinuousOn lam (Set.Ioi 0)) : SurvivalCocycle where
  u t := lam (Real.exp t)
  pos t := hpos _ (Real.exp_pos t)
  mul s t := by
    show lam (Real.exp (s + t)) = lam (Real.exp s) * lam (Real.exp t)
    rw [Real.exp_add]
    exact hmul _ _ (Real.exp_pos s) (Real.exp_pos t)
  cont := hcont.comp_continuous Real.continuous_exp fun t =>
    Set.mem_Ioi.mpr (Real.exp_pos t)

/-- Refinement-semigroup tilt: a function positive and continuous on
`(0, ∞)` and multiplicative there is a power, `lam b = b ^ (-θ)` for all
`b > 0`. -/
theorem refinementSemigroup_tilt (lam : ℝ → ℝ) (hpos : ∀ b, 0 < b → 0 < lam b)
    (hmul : ∀ b₁ b₂, 0 < b₁ → 0 < b₂ → lam (b₁ * b₂) = lam b₁ * lam b₂)
    (hcont : ContinuousOn lam (Set.Ioi 0)) :
    ∃ θ : ℝ, ∀ b, 0 < b → lam b = b ^ (-θ) := by
  refine ⟨(SurvivalCocycle.ofRefinement lam hpos hmul hcont).tilt, fun b hb => ?_⟩
  have h := (SurvivalCocycle.ofRefinement lam hpos hmul hcont).u_eq_exp (Real.log b)
  have hu : (SurvivalCocycle.ofRefinement lam hpos hmul hcont).u (Real.log b) = lam b := by
    show lam (Real.exp (Real.log b)) = lam b
    rw [Real.exp_log hb]
  rw [hu] at h
  rw [h, Real.rpow_def_of_pos hb]
  congr 1
  ring

/-- The power exponent is unique: comparison at `b = exp 1`. -/
theorem refinementSemigroup_tilt_unique (lam : ℝ → ℝ) {θ₁ θ₂ : ℝ}
    (h₁ : ∀ b, 0 < b → lam b = b ^ (-θ₁))
    (h₂ : ∀ b, 0 < b → lam b = b ^ (-θ₂)) : θ₁ = θ₂ := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h := (h₁ _ he).symm.trans (h₂ _ he)
  rw [Real.rpow_def_of_pos he, Real.rpow_def_of_pos he, Real.log_exp] at h
  have h' := Real.exp_injective h
  linarith

/-! ## Numeric corollary on the comparison pixel -/

/-- On the comparison pixel `1.630968 ≤ P ≤ 1.630973`,
`0.9660213 < nS P < 0.9660216`. -/
theorem nS_at_comparison_pixel {P : ℝ} (h₁ : 1.630968 ≤ P) (h₂ : P ≤ 1.630973) :
    0.9660213 < nS P ∧ nS P < 0.9660216 := by
  unfold nS
  constructor <;> linarith

/-! ## Per-theorem axiom audit -/

#print axioms SurvivalCocycle.u_zero
#print axioms SurvivalCocycle.log_u_eq
#print axioms SurvivalCocycle.u_eq_exp
#print axioms SurvivalCocycle.exists_exp
#print axioms SurvivalCocycle.exp_unique
#print axioms SurvivalCocycle.hasDerivAt_zero
#print axioms SurvivalCocycle.tilt_of_hasDerivAt
#print axioms edgeCenter_tilt
#print axioms refinementSemigroup_tilt
#print axioms refinementSemigroup_tilt_unique
#print axioms nS_at_comparison_pixel

end

end OPH.EinsteinBranch.EdgeCenterTilt

module
public import WhitneyNormalModeConstruction
public import ConeCochainBridge
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

set_option autoImplicit false

namespace OPH.WhitneyConeModes

open OPH.ConeCochainBridge
open OPH.WhitneyNormalModes
open OPH.WhitneyQuantumBridge
open OPH.DiscreteCoulombGreen
open OPH.PositionSpaceMaxwellAction
open OPH.LocalFaceMaxwellAction

noncomputable section

/-- The upstream cone gradient, exposed as the linear map consumed by the
spectral construction. -/
def coneGradientLinear : ConeZero →ₗ[ℝ] ConeOne where
  toFun := coneGradient
  map_add' x y := by
    apply Prod.ext
    · funext p
      simp [coneGradient]
      ring
    · simp [coneGradient, map_add]
  map_smul' r x := by
    apply Prod.ext
    · funext p
      simp [coneGradient]
      ring
    · simp [coneGradient, map_smul]

/-- The upstream cone curl, exposed as a linear map without changing its
component definitions. -/
def coneCurlLinear : ConeOne →ₗ[ℝ] ConeTwo where
  toFun := coneCurl
  map_add' x y := by
    apply Prod.ext
    · funext e
      simp [coneCurl, map_add]
      ring
    · simp [coneCurl, map_add]
  map_smul' r x := by
    apply Prod.ext
    · funext e
      simp [coneCurl, map_smul]
      ring
    · simp [coneCurl, map_smul]

@[simp] theorem coneGradientLinear_apply (u : ConeZero) :
    coneGradientLinear u = coneGradient u := rfl

@[simp] theorem coneCurlLinear_apply (a : ConeOne) :
    coneCurlLinear a = coneCurl a := rfl

/-- Exactness at the actual 42-edge cone: curl-free one-cochains are exactly
the gradients of the 13 scalar registers. -/
theorem cone_exact :
    LinearMap.ker coneCurlLinear = LinearMap.range coneGradientLinear := by
  apply le_antisymm
  · intro a ha
    have hcurl : coneCurl a = 0 := LinearMap.mem_ker.mp ha
    have hradial := congrArg Prod.fst hcurl
    have hboundary : a.2 = realCoboundary a.1 := by
      exact sub_eq_zero.mp (by simpa [coneCurl] using hradial)
    refine ⟨((0 : ℝ), a.1), ?_⟩
    apply Prod.ext
    · funext p
      simp [coneGradient]
    · simpa [coneGradient] using hboundary.symm
  · intro a ha
    obtain ⟨u, rfl⟩ := ha
    exact LinearMap.mem_ker.mpr (coneCurl_gradient u)

/-- Evaluation at the cone apex classifies a zero-gradient scalar field. -/
def coneGradientKernelApex : LinearMap.ker coneGradientLinear →ₗ[ℝ] ℝ where
  toFun u := u.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coneGradientKernelApex_bijective :
    Function.Bijective coneGradientKernelApex := by
  constructor
  · intro x y hxy
    dsimp [coneGradientKernelApex] at hxy
    apply Subtype.ext
    apply Prod.ext
    · exact hxy
    · funext p
      have hx0 : coneGradient (x : ConeZero) = 0 := LinearMap.mem_ker.mp x.2
      have hy0 : coneGradient (y : ConeZero) = 0 := LinearMap.mem_ker.mp y.2
      have hx : (x : ConeZero).2 p - (x : ConeZero).1 = 0 := by
        simpa [coneGradient] using congrFun (congrArg Prod.fst hx0) p
      have hy : (y : ConeZero).2 p - (y : ConeZero).1 = 0 := by
        simpa [coneGradient] using congrFun (congrArg Prod.fst hy0) p
      linarith [hxy]
  · intro c
    let u : ConeZero := (c, fun _ => c)
    have hu : coneGradientLinear u = 0 := by
      apply Prod.ext
      · funext p
        simp [coneGradientLinear, coneGradient, u]
      · exact realCoboundary_eq_zero_iff (fun _ => c) |>.mpr ⟨c, rfl⟩
    exact ⟨⟨u, LinearMap.mem_ker.mpr hu⟩, rfl⟩

def coneGradientKernelEquiv : LinearMap.ker coneGradientLinear ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective coneGradientKernelApex coneGradientKernelApex_bijective

theorem coneGradient_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker coneGradientLinear) = 1 := by
  rw [coneGradientKernelEquiv.finrank_eq]
  exact Module.finrank_self ℝ

theorem coneGradient_range_finrank :
    Module.finrank ℝ (LinearMap.range coneGradientLinear) = 12 := by
  have hrank := coneGradientLinear.finrank_range_add_finrank_ker
  rw [coneGradient_kernel_finrank] at hrank
  norm_num [ConeZero] at hrank
  omega

theorem coneCurl_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker coneCurlLinear) = 12 := by
  rw [cone_exact]
  exact coneGradient_range_finrank

/-- Euclidean mass-coordinate carriers for the source cone. The coordinate
equivalences below retain the upstream component definitions byte-for-byte. -/
abbrev ConeZeroL2 := EuclideanSpace ℝ (Unit ⊕ Fin 12)
abbrev ConeOneL2 := EuclideanSpace ℝ (Fin 12 ⊕ Fin 30)
abbrev ConeTwoL2 := EuclideanSpace ℝ (Fin 30 ⊕ Fin 20)

def euclideanSumCoordinates {i k : Type*} [Fintype i] [Fintype k] :
    EuclideanSpace ℝ (i ⊕ k) ≃ₗ[ℝ] ((i → ℝ) × (k → ℝ)) :=
  EuclideanSpace.sumEquivProd.toLinearEquiv |>.trans
    ((WithLp.linearEquiv 2 ℝ (i → ℝ)).prodCongr
      (WithLp.linearEquiv 2 ℝ (k → ℝ)))

def coneZeroCoordinates : ConeZeroL2 ≃ₗ[ℝ] ConeZero :=
  euclideanSumCoordinates.trans
    ((LinearEquiv.funUnique Unit ℝ ℝ).prodCongr
      (LinearEquiv.refl ℝ (Fin 12 → ℝ)))

def coneOneCoordinates : ConeOneL2 ≃ₗ[ℝ] ConeOne :=
  euclideanSumCoordinates

def coneTwoCoordinates : ConeTwoL2 ≃ₗ[ℝ] ConeTwo :=
  euclideanSumCoordinates

def coneGradientL2 : ConeZeroL2 →ₗ[ℝ] ConeOneL2 :=
  coneOneCoordinates.symm.toLinearMap.comp
    (coneGradientLinear.comp coneZeroCoordinates.toLinearMap)

def coneCurlL2 : ConeOneL2 →ₗ[ℝ] ConeTwoL2 :=
  coneTwoCoordinates.symm.toLinearMap.comp
    (coneCurlLinear.comp coneOneCoordinates.toLinearMap)

/-- The transported gradient on a vector. -/
theorem coneGradientL2_apply (x : ConeZeroL2) :
    coneGradientL2 x = coneOneCoordinates.symm (coneGradientLinear (coneZeroCoordinates x)) := rfl

/-- The transported curl on a vector. -/
theorem coneCurlL2_apply (x : ConeOneL2) :
    coneCurlL2 x = coneTwoCoordinates.symm (coneCurlLinear (coneOneCoordinates x)) := rfl

theorem cone_exact_l2 :
    LinearMap.ker coneCurlL2 = LinearMap.range coneGradientL2 := by
  apply le_antisymm
  · intro x hx
    have hraw : coneCurlLinear (coneOneCoordinates x) = 0 := by
      have h := congrArg coneTwoCoordinates (LinearMap.mem_ker.mp hx)
      simpa only [coneCurlL2_apply, LinearEquiv.apply_symm_apply, map_zero] using h
    have hrange : coneOneCoordinates x ∈ LinearMap.range coneGradientLinear := by
      rw [← cone_exact]
      exact LinearMap.mem_ker.mpr hraw
    obtain ⟨u, hu⟩ := hrange
    refine ⟨coneZeroCoordinates.symm u, ?_⟩
    apply coneOneCoordinates.injective
    simpa only [coneGradientL2_apply, LinearEquiv.apply_symm_apply] using hu
  · intro x hx
    obtain ⟨u, rfl⟩ := hx
    apply LinearMap.mem_ker.mpr
    apply coneTwoCoordinates.injective
    simp [coneCurlL2, coneGradientL2, coneCurl_gradient]

def coneGradientKernelToRaw :
    LinearMap.ker coneGradientL2 →ₗ[ℝ] LinearMap.ker coneGradientLinear where
  toFun x := ⟨coneZeroCoordinates x, by
    apply LinearMap.mem_ker.mpr
    have h := LinearMap.mem_ker.mp x.2
    rw [coneGradientL2_apply] at h
    have h' := congrArg coneOneCoordinates h
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using h' ⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simpa only [RingHom.id_apply, Submodule.coe_smul] using coneZeroCoordinates.map_smul r (x : ConeZeroL2)

/-- The underlying raw coordinate of the restricted kernel map. -/
theorem coneGradientKernelToRaw_apply (x : LinearMap.ker coneGradientL2) :
    (coneGradientKernelToRaw x : ConeZero) = coneZeroCoordinates (x : ConeZeroL2) := rfl

theorem coneGradientKernelToRaw_bijective :
    Function.Bijective coneGradientKernelToRaw := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply coneZeroCoordinates.injective
    have h := congrArg Subtype.val hxy
    simpa only [coneGradientKernelToRaw_apply] using h
  · intro u
    let x : ConeZeroL2 := coneZeroCoordinates.symm u
    have hx : coneGradientL2 x = 0 := by
      apply coneOneCoordinates.injective
      simp [coneGradientL2, x, LinearMap.mem_ker.mp u.2]
    refine ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, ?_⟩
    apply Subtype.ext
    simp only [coneGradientKernelToRaw_apply, x, LinearEquiv.apply_symm_apply]

def coneGradientKernelL2EquivRaw :
    LinearMap.ker coneGradientL2 ≃ₗ[ℝ] LinearMap.ker coneGradientLinear :=
  LinearEquiv.ofBijective coneGradientKernelToRaw coneGradientKernelToRaw_bijective

theorem coneGradientL2_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker coneGradientL2) = 1 := by
  rw [coneGradientKernelL2EquivRaw.finrank_eq]
  exact coneGradient_kernel_finrank

theorem coneGradientL2_range_finrank :
    Module.finrank ℝ (LinearMap.range coneGradientL2) = 12 := by
  have hrank := coneGradientL2.finrank_range_add_finrank_ker
  rw [coneGradientL2_kernel_finrank] at hrank
  norm_num [ConeZeroL2] at hrank
  omega

/-- The Gauss constraint is the mass adjoint of the source cone gradient. -/
def coneConstraint : ConeOneL2 →ₗ[ℝ] ConeZeroL2 := coneGradientL2.adjoint

/-- Curl energy with positive Euclidean mass forms on the physical edge and
face coordinate carriers. -/
def coneStiffness : LinearMap.BilinForm ℝ ConeOneL2 :=
  LinearMap.mk₂ ℝ
    (fun x y => inner ℝ (coneCurlL2 x) (coneCurlL2 y))
    (by intros; simp [map_add, inner_add_left])
    (by intros; simp [map_smul, real_inner_smul_left])
    (by intros; simp [map_add, inner_add_right])
    (by intros; simp [map_smul, real_inner_smul_right])

theorem coneStiffness_symm : coneStiffness.IsSymm :=
  ⟨fun x y => by
    change inner ℝ (coneCurlL2 x) (coneCurlL2 y) =
      inner ℝ (coneCurlL2 y) (coneCurlL2 x)
    exact real_inner_comm _ _⟩

theorem coneConstraint_kernel_finrank :
    Module.finrank ℝ (LinearMap.ker coneConstraint) = 30 := by
  have hadj : Module.finrank ℝ (LinearMap.range coneConstraint) = 12 := by
    change Module.finrank ℝ (LinearMap.range coneGradientL2.adjoint) = 12
    rw [LinearMap.finrank_range_adjoint, coneGradientL2_range_finrank]
  have hrank := coneConstraint.finrank_range_add_finrank_ker
  rw [hadj] at hrank
  norm_num [ConeOneL2] at hrank
  omega

theorem coneCurl_nonzero_on_constraint
    (x : ConeOneL2) (hx : coneConstraint x = 0) (hne : x ≠ 0) :
    coneCurlL2 x ≠ 0 := by
  intro hcurl
  have hxRange : x ∈ LinearMap.range coneGradientL2 := by
    rw [← cone_exact_l2]
    exact LinearMap.mem_ker.mpr hcurl
  have hxOrthogonal : x ∈ (LinearMap.range coneGradientL2).orthogonal := by
    rw [coneGradientL2.orthogonal_range]
    simpa [coneConstraint] using LinearMap.mem_ker.mpr hx
  have hxInf : x ∈ LinearMap.range coneGradientL2 ⊓
      (LinearMap.range coneGradientL2).orthogonal := ⟨hxRange, hxOrthogonal⟩
  rw [Submodule.inf_orthogonal_eq_bot] at hxInf
  exact hne (by simpa only [Submodule.mem_bot] using hxInf)

theorem coneStiffness_pos_on_constraint
    (x : ConeOneL2) (hx : coneConstraint x = 0) (hne : x ≠ 0) :
    0 < coneStiffness x x := by
  change 0 < inner ℝ (coneCurlL2 x) (coneCurlL2 x)
  exact real_inner_self_pos.mpr (coneCurl_nonzero_on_constraint x hx hne)

theorem coneStiffness_preserves_constraint
    (x : ConeOneL2) (_hx : coneConstraint x = 0) :
    coneConstraint (ambientStiffnessOperator coneStiffness x) = 0 := by
  apply LinearMap.mem_ker.mp
  have horth : ambientStiffnessOperator coneStiffness x ∈
      (LinearMap.range coneGradientL2).orthogonal := by
    apply ((LinearMap.range coneGradientL2).mem_orthogonal _).mpr
    intro u hu
    obtain ⟨p, rfl⟩ := hu
    rw [real_inner_comm, ambientStiffnessOperator_pairing]
    change inner ℝ (coneCurlL2 x) (coneCurlL2 (coneGradientL2 p)) = 0
    rw [show coneCurlL2 (coneGradientL2 p) = 0 by
      apply coneTwoCoordinates.injective
      simp [coneCurlL2, coneGradientL2, coneCurl_gradient]]
    exact inner_zero_right _
  have hker : ambientStiffnessOperator coneStiffness x ∈
      LinearMap.ker coneGradientL2.adjoint := by
    rw [← coneGradientL2.orthogonal_range]
    exact horth
  simpa [coneConstraint] using hker

/-- Thirty complete positive radiative modes for the source-defined cone. -/
def conePositiveNormalFrame :
    PositiveNormalFrame (ι := Fin 30) (innerₗ ConeOneL2)
      coneStiffness coneConstraint :=
  positiveNormalFrameOfSpectral coneStiffness coneConstraint
    coneStiffness_symm coneStiffness_preserves_constraint
    coneStiffness_pos_on_constraint coneConstraint_kernel_finrank

set_option maxRecDepth 4000 in
theorem cone_same_action_normal_modes (q velocity : Fin 30 → ℝ) :
    (inner ℝ (reconstruct conePositiveNormalFrame.vector velocity)
        (reconstruct conePositiveNormalFrame.vector velocity) -
      coneStiffness (reconstruct conePositiveNormalFrame.vector q)
        (reconstruct conePositiveNormalFrame.vector q)) / 2 =
      ∑ i, (velocity i ^ 2 - conePositiveNormalFrame.omega i ^ 2 * q i ^ 2) / 2 :=
  same_action_normal_modes conePositiveNormalFrame q velocity

set_option maxRecDepth 4000 in
theorem cone_same_modes_quantized_energy
    (hbar : ℝ) (hh : 0 < hbar) (p : ParticlePolynomial (Fin 30)) :
    (∑ i, (1 / 2 : ℂ) •
      (momentumOperator i (conePositiveNormalFrame.omega i)
        (positionScale hbar (conePositiveNormalFrame.omega i))
        (momentumOperator i (conePositiveNormalFrame.omega i)
          (positionScale hbar (conePositiveNormalFrame.omega i)) p) +
      ((conePositiveNormalFrame.omega i ^ 2 : ℝ) : ℂ) •
        positionOperator i (positionScale hbar (conePositiveNormalFrame.omega i))
          (positionOperator i (positionScale hbar (conePositiveNormalFrame.omega i)) p))) =
      quantumHamiltonian hbar conePositiveNormalFrame.omega p :=
  same_modes_quantized_energy conePositiveNormalFrame hbar hh p

#print axioms cone_exact
#print axioms coneGradient_range_finrank
#print axioms coneCurl_kernel_finrank
#print axioms coneConstraint_kernel_finrank
#print axioms coneStiffness_pos_on_constraint
#print axioms conePositiveNormalFrame
#print axioms cone_same_action_normal_modes
#print axioms cone_same_modes_quantized_energy

end


end OPH.WhitneyConeModes

#print axioms OPH.WhitneyConeModes.coneGradientL2_apply

#print axioms OPH.WhitneyConeModes.coneCurlL2_apply

#print axioms OPH.WhitneyConeModes.coneGradientKernelToRaw_apply

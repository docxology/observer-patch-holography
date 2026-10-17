module
public import WhitneyConeModes
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace OPH.WhitneyConeMass

open OPH.ConeCochainBridge
open OPH.WhitneyQuantumBridge
open OPH.WhitneyNormalModes
open OPH.WhitneyConeModes

noncomputable section

/-- The source Gauss functional `x ↦ (p ↦ M₁(Dp,x))`, i.e. `Dᵀ M₁`. -/
def coneConstraintWithMass (mass₁ : LinearMap.BilinForm ℝ ConeOne) :
    ConeOne →ₗ[ℝ] Module.Dual ℝ ConeZero where
  toFun x :=
    { toFun := fun p => mass₁ (coneGradientLinear p) x
      map_add' := by intros; simp only [map_add, LinearMap.add_apply]
      map_smul' := by intros; simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  map_add' x y := by
    apply LinearMap.ext
    intro p
    exact map_add (mass₁ (coneGradientLinear p)) x y
  map_smul' r x := by
    apply LinearMap.ext
    intro p
    exact map_smul (mass₁ (coneGradientLinear p)) r x

/-- The source curl energy `K(x,y)=M₂(Cx,Cy)`, i.e. `Cᵀ M₂ C`. -/
def coneStiffnessWithMass (mass₂ : LinearMap.BilinForm ℝ ConeTwo) :
    LinearMap.BilinForm ℝ ConeOne :=
  LinearMap.mk₂ ℝ
    (fun x y => mass₂ (coneCurlLinear x) (coneCurlLinear y))
    (by intros; simp [map_add])
    (by intros; simp [map_smul])
    (by intros; simp [map_add])
    (by intros; simp [map_smul])

theorem coneStiffnessWithMass_symm
    (mass₂ : LinearMap.BilinForm ℝ ConeTwo) (mass₂_symm : mass₂.IsSymm) :
    (coneStiffnessWithMass mass₂).IsSymm := by
  constructor
  intro x y
  exact mass₂_symm.eq _ _

theorem coneConstraintWithMass_kernel
    (mass₁ : LinearMap.BilinForm ℝ ConeOne) :
    LinearMap.ker (coneConstraintWithMass mass₁) =
      mass₁.orthogonal (LinearMap.range coneGradientLinear) := by
  ext x
  constructor
  · intro hx y hy
    obtain ⟨p, rfl⟩ := hy
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) p
  · intro hx
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro p
    exact hx (coneGradientLinear p) ⟨p, rfl⟩

theorem coneConstraintWithMass_kernel_finrank
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x) :
    Module.finrank ℝ (LinearMap.ker (coneConstraintWithMass mass₁)) = 30 := by
  rw [coneConstraintWithMass_kernel]
  rw [LinearMap.BilinForm.finrank_orthogonal (mass_nondegenerate mass₁ mass₁_pos)]
  rw [coneGradient_range_finrank]
  norm_num [ConeOne]

theorem coneCurl_nonzero_with_mass
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x)
    (x : ConeOne) (hx : coneConstraintWithMass mass₁ x = 0) (hne : x ≠ 0) :
    coneCurlLinear x ≠ 0 := by
  intro hcurl
  have hxRange : x ∈ LinearMap.range coneGradientLinear := by
    rw [← cone_exact]
    exact LinearMap.mem_ker.mpr hcurl
  have hxOrthogonal : x ∈ mass₁.orthogonal (LinearMap.range coneGradientLinear) := by
    rw [← coneConstraintWithMass_kernel]
    exact LinearMap.mem_ker.mpr hx
  exact (ne_of_gt (mass₁_pos x hne)) (hxOrthogonal x hxRange)

theorem coneStiffnessWithMass_pos
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₂ : LinearMap.BilinForm ℝ ConeTwo)
    (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x)
    (mass₂_pos : ∀ x : ConeTwo, x ≠ 0 → 0 < mass₂ x x)
    (x : ConeOne) (hx : coneConstraintWithMass mass₁ x = 0) (hne : x ≠ 0) :
    0 < coneStiffnessWithMass mass₂ x x := by
  exact mass₂_pos (coneCurlLinear x)
    (coneCurl_nonzero_with_mass mass₁ mass₁_pos x hx hne)

/-- Sharp positivity boundary: curl energy is positive on every nonzero
constrained field exactly when no nonzero harmonic field lies in both kernels. -/
theorem coneStiffnessWithMass_positive_iff_no_harmonic
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₂ : LinearMap.BilinForm ℝ ConeTwo)
    (mass₂_pos : ∀ x : ConeTwo, x ≠ 0 → 0 < mass₂ x x) :
    (∀ x : ConeOne, coneConstraintWithMass mass₁ x = 0 → x ≠ 0 →
      0 < coneStiffnessWithMass mass₂ x x) ↔
      LinearMap.ker coneCurlLinear ⊓
        LinearMap.ker (coneConstraintWithMass mass₁) = ⊥ := by
  constructor
  · intro hpositive
    rw [eq_bot_iff]
    intro x hx
    by_contra hne
    have hp := hpositive x (LinearMap.mem_ker.mp hx.2) hne
    have hcurl := LinearMap.mem_ker.mp hx.1
    change 0 < mass₂ (coneCurlLinear x) (coneCurlLinear x) at hp
    rw [hcurl] at hp
    simp at hp
  · intro hno x hx hne
    apply mass₂_pos (coneCurlLinear x)
    intro hcurl
    have hinf : x ∈ LinearMap.ker coneCurlLinear ⊓
        LinearMap.ker (coneConstraintWithMass mass₁) :=
      ⟨LinearMap.mem_ker.mpr hcurl, LinearMap.mem_ker.mpr hx⟩
    rw [hno] at hinf
    exact hne (by simpa only [Submodule.mem_bot] using hinf)

theorem coneStiffnessWithMass_preserves_constraint
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₂ : LinearMap.BilinForm ℝ ConeTwo)
    (mass₁_symm : mass₁.IsSymm)
    (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x)
    (mass₂_symm : mass₂.IsSymm)
    (x : ConeOne) (_hx : coneConstraintWithMass mass₁ x = 0) :
    coneConstraintWithMass mass₁
        (bilinearStiffnessOperator mass₁ (coneStiffnessWithMass mass₂)
          mass₁_pos x) = 0 := by
  apply LinearMap.ext
  intro p
  change mass₁ (coneGradientLinear p)
    (bilinearStiffnessOperator mass₁ (coneStiffnessWithMass mass₂)
      mass₁_pos x) = 0
  calc
    _ = mass₁
        (bilinearStiffnessOperator mass₁ (coneStiffnessWithMass mass₂)
          mass₁_pos x) (coneGradientLinear p) := mass₁_symm.eq _ _
    _ = coneStiffnessWithMass mass₂ x (coneGradientLinear p) :=
      bilinearStiffnessOperator_pairing mass₁ (coneStiffnessWithMass mass₂)
        mass₁_pos (coneGradientLinear p) x
    _ = coneStiffnessWithMass mass₂ (coneGradientLinear p) x :=
      (coneStiffnessWithMass_symm mass₂ mass₂_symm).eq _ _
    _ = 0 := by
      change mass₂ (coneCurlLinear (coneGradientLinear p)) (coneCurlLinear x) = 0
      rw [show coneCurlLinear (coneGradientLinear p) = 0 by
        exact coneCurl_gradient p]
      simp

/-- Complete positive modes for the actual cone incidence with arbitrary
source-supplied symmetric positive-definite Whitney mass forms `M₁` and `M₂`. -/
def conePositiveNormalFrameWithMass
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₂ : LinearMap.BilinForm ℝ ConeTwo)
    (mass₁_symm : mass₁.IsSymm) (mass₂_symm : mass₂.IsSymm)
    (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x)
    (mass₂_pos : ∀ x : ConeTwo, x ≠ 0 → 0 < mass₂ x x) :
    PositiveNormalFrame (ι := Fin 30) mass₁ (coneStiffnessWithMass mass₂)
      (coneConstraintWithMass mass₁) :=
  positiveNormalFrameOfBilinearSpectral mass₁ (coneStiffnessWithMass mass₂)
    (coneConstraintWithMass mass₁) mass₁_symm mass₁_pos
    (coneStiffnessWithMass_symm mass₂ mass₂_symm)
    (coneStiffnessWithMass_preserves_constraint mass₁ mass₂
      mass₁_symm mass₁_pos mass₂_symm)
    (coneStiffnessWithMass_pos mass₁ mass₂ mass₁_pos mass₂_pos)
    (coneConstraintWithMass_kernel_finrank mass₁ mass₁_pos)

theorem cone_same_action_with_mass
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₂ : LinearMap.BilinForm ℝ ConeTwo)
    (mass₁_symm : mass₁.IsSymm) (mass₂_symm : mass₂.IsSymm)
    (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x)
    (mass₂_pos : ∀ x : ConeTwo, x ≠ 0 → 0 < mass₂ x x)
    (q velocity : Fin 30 → ℝ) :
    (mass₁
        (reconstruct (conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm
          mass₂_symm mass₁_pos mass₂_pos).vector velocity)
        (reconstruct (conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm
          mass₂_symm mass₁_pos mass₂_pos).vector velocity) -
      coneStiffnessWithMass mass₂
        (reconstruct (conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm
          mass₂_symm mass₁_pos mass₂_pos).vector q)
        (reconstruct (conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm
          mass₂_symm mass₁_pos mass₂_pos).vector q)) / 2 =
      ∑ x, (velocity x ^ 2 -
        (conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm mass₂_symm
          mass₁_pos mass₂_pos).omega x ^ 2 * q x ^ 2) / 2 :=
  same_action_normal_modes
    (conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm mass₂_symm
      mass₁_pos mass₂_pos) q velocity

theorem cone_same_quantized_energy_with_mass
    (mass₁ : LinearMap.BilinForm ℝ ConeOne)
    (mass₂ : LinearMap.BilinForm ℝ ConeTwo)
    (mass₁_symm : mass₁.IsSymm) (mass₂_symm : mass₂.IsSymm)
    (mass₁_pos : ∀ x : ConeOne, x ≠ 0 → 0 < mass₁ x x)
    (mass₂_pos : ∀ x : ConeTwo, x ≠ 0 → 0 < mass₂ x x)
    (hbar : ℝ) (hh : 0 < hbar) (p : ParticlePolynomial (Fin 30)) :
    let F := conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm mass₂_symm
      mass₁_pos mass₂_pos
    (∑ x, (1 / 2 : ℂ) •
      (momentumOperator x (F.omega x) (positionScale hbar (F.omega x))
        (momentumOperator x (F.omega x) (positionScale hbar (F.omega x)) p) +
      ((F.omega x ^ 2 : ℝ) : ℂ) •
        positionOperator x (positionScale hbar (F.omega x))
          (positionOperator x (positionScale hbar (F.omega x)) p))) =
      quantumHamiltonian hbar F.omega p := by
  dsimp
  exact same_modes_quantized_energy
    (conePositiveNormalFrameWithMass mass₁ mass₂ mass₁_symm mass₂_symm
      mass₁_pos mass₂_pos) hbar hh p

#print axioms coneConstraintWithMass_kernel_finrank
#print axioms coneStiffnessWithMass_pos
#print axioms coneStiffnessWithMass_positive_iff_no_harmonic
#print axioms conePositiveNormalFrameWithMass
#print axioms cone_same_action_with_mass
#print axioms cone_same_quantized_energy_with_mass

end
end OPH.WhitneyConeMass

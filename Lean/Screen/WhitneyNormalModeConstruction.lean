module
public import WhitneyQuantumBridge
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section

set_option autoImplicit false

namespace OPH.WhitneyNormalModes

open OPH.WhitneyQuantumBridge

noncomputable section

section AbstractMass

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A symmetric positive-definite real bilinear form supplies the inner-product
core used by the finite-dimensional spectral theorem. -/
@[reducible] def massInnerProductCore (mass : LinearMap.BilinForm ℝ E)
    (mass_symm : mass.IsSymm)
    (mass_pos : ∀ x : E, x ≠ 0 → 0 < mass x x) :
    InnerProductSpace.Core ℝ E where
  inner := fun x y => mass x y
  conj_inner_symm x y := by
    simp only [conj_trivial]
    exact (mass_symm.eq x y).symm
  re_inner_nonneg x := by
    change 0 ≤ mass x x
    by_cases hx : x = 0
    · subst x
      simp
    · exact (mass_pos x hx).le
  add_left x y z := by
    simp
  smul_left x y r := by
    simp only [conj_trivial]
    simp
  definite x hx := by
    by_contra hne
    exact (ne_of_gt (mass_pos x hne)) hx

theorem mass_nondegenerate [FiniteDimensional ℝ E]
    (mass : LinearMap.BilinForm ℝ E)
    (mass_pos : ∀ x : E, x ≠ 0 → 0 < mass x x) :
    mass.Nondegenerate := by
  constructor
  · intro x hx
    by_contra hne
    exact (ne_of_gt (mass_pos x hne)) (hx x)
  · intro x hx
    by_contra hne
    exact (ne_of_gt (mass_pos x hne)) (hx x)

end AbstractMass

section InnerSpectral

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [AddCommGroup V] [Module ℝ V]

/-- The mass-Riesz representative of stiffness on the exact constrained
sector. Here the ambient real inner product is the supplied mass pairing. -/
def sectorStiffnessOperator (stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V) :
    LinearMap.ker constraint →ₗ[ℝ] LinearMap.ker constraint :=
  (stiffness.restrict (LinearMap.ker constraint)).symmCompOfNondegenerate
    (innerₗ (LinearMap.ker constraint)) <| by
      apply mass_nondegenerate
      intro x hx
      exact real_inner_self_pos.mpr (by
        intro hzero
        apply hx
        exact Subtype.ext hzero)

theorem sectorStiffnessOperator_pairing
    (stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V)
    (x y : LinearMap.ker constraint) :
    inner ℝ (sectorStiffnessOperator stiffness constraint y) x =
      stiffness y x := by
  exact LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
    (stiffness.restrict (LinearMap.ker constraint))
    (mass_nondegenerate (innerₗ (LinearMap.ker constraint))
      (fun x hx => real_inner_self_pos.mpr (by
        intro hzero
        apply hx
        exact Subtype.ext hzero))) x y

theorem sectorStiffnessOperator_isSymmetric
    (stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V)
    (stiffness_symm : stiffness.IsSymm) :
    LinearMap.IsSymmetric (sectorStiffnessOperator stiffness constraint) := by
  intro x y
  calc
    inner ℝ (sectorStiffnessOperator stiffness constraint x) y =
        stiffness x y := sectorStiffnessOperator_pairing stiffness constraint y x
    _ = stiffness y x := stiffness_symm.eq x y
    _ = inner ℝ (sectorStiffnessOperator stiffness constraint y) x :=
      (sectorStiffnessOperator_pairing stiffness constraint x y).symm
    _ = inner ℝ x (sectorStiffnessOperator stiffness constraint y) :=
      real_inner_comm x _

/-- Ambient mass-Riesz representative of the stiffness form. -/
def ambientStiffnessOperator (stiffness : LinearMap.BilinForm ℝ E) : E →ₗ[ℝ] E :=
  stiffness.symmCompOfNondegenerate (innerₗ E) <| by
    apply mass_nondegenerate
    intro x hx
    exact real_inner_self_pos.mpr hx

theorem ambientStiffnessOperator_pairing
    (stiffness : LinearMap.BilinForm ℝ E) (x y : E) :
    inner ℝ (ambientStiffnessOperator stiffness y) x = stiffness y x := by
  exact LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
    stiffness
    (mass_nondegenerate (innerₗ E) (fun x hx => real_inner_self_pos.mpr hx)) x y

theorem ambientStiffnessOperator_isSymmetric
    (stiffness : LinearMap.BilinForm ℝ E)
    (stiffness_symm : stiffness.IsSymm) :
    LinearMap.IsSymmetric (ambientStiffnessOperator stiffness) := by
  intro x y
  calc
    inner ℝ (ambientStiffnessOperator stiffness x) y =
        stiffness x y := ambientStiffnessOperator_pairing stiffness y x
    _ = stiffness y x := stiffness_symm.eq x y
    _ = inner ℝ (ambientStiffnessOperator stiffness y) x :=
      (ambientStiffnessOperator_pairing stiffness x y).symm
    _ = inner ℝ x (ambientStiffnessOperator stiffness y) :=
      real_inner_comm x _

/-- Restriction of the ambient stiffness operator to an invariant constrained
sector. Keeping the ambient operator is what later recovers the source
interface's equation against every ambient test vector. -/
def constrainedStiffnessOperator
    (stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V)
    (invariant : ∀ x, constraint x = 0 →
      constraint (ambientStiffnessOperator stiffness x) = 0) :
    LinearMap.ker constraint →ₗ[ℝ] LinearMap.ker constraint :=
  (ambientStiffnessOperator stiffness).restrict fun x hx =>
    LinearMap.mem_ker.mpr (invariant x (LinearMap.mem_ker.mp hx))

theorem constrainedStiffnessOperator_coe
    (stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V)
    (invariant : ∀ x, constraint x = 0 →
      constraint (ambientStiffnessOperator stiffness x) = 0)
    (x : LinearMap.ker constraint) :
    (constrainedStiffnessOperator stiffness constraint invariant x : E) =
      ambientStiffnessOperator stiffness x := rfl

theorem constrainedStiffnessOperator_isSymmetric
    (stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V)
    (invariant : ∀ x, constraint x = 0 →
      constraint (ambientStiffnessOperator stiffness x) = 0)
    (stiffness_symm : stiffness.IsSymm) :
    LinearMap.IsSymmetric
      (constrainedStiffnessOperator stiffness constraint invariant) := by
  intro x y
  exact ambientStiffnessOperator_isSymmetric stiffness stiffness_symm x y

omit [FiniteDimensional ℝ E] in
theorem span_coe_orthonormalBasis
    {n : ℕ} (S : Submodule ℝ E) (b : OrthonormalBasis (Fin n) ℝ S) :
    Submodule.span ℝ (Set.range fun i => ((b i : S) : E)) = S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  · intro x hx
    obtain ⟨c, hsum⟩ := b.toBasis.mem_submodule_iff'.mp hx
    rw [hsum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i))

/-- A complete positive frame generated by the finite-dimensional spectral
theorem from an invariant, strictly positive constrained sector. -/
def positiveNormalFrameOfSpectral
    {n : ℕ}
    (stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V)
    (stiffness_symm : stiffness.IsSymm)
    (invariant : ∀ x, constraint x = 0 →
      constraint (ambientStiffnessOperator stiffness x) = 0)
    (stiffness_pos : ∀ x : E, constraint x = 0 → x ≠ 0 → 0 < stiffness x x)
    (sector_finrank : Module.finrank ℝ (LinearMap.ker constraint) = n) :
    PositiveNormalFrame (ι := Fin n) (innerₗ E) stiffness constraint := by
  let A := constrainedStiffnessOperator stiffness constraint invariant
  have hA : A.IsSymmetric :=
    constrainedStiffnessOperator_isSymmetric stiffness constraint invariant stiffness_symm
  let b : OrthonormalBasis (Fin n) ℝ (LinearMap.ker constraint) :=
    hA.eigenvectorBasis sector_finrank
  let eigenvalue : Fin n → ℝ := hA.eigenvalues sector_finrank
  have eigenvalue_pos : ∀ i, 0 < eigenvalue i := by
    intro i
    have hvec_ne : ((b i : LinearMap.ker constraint) : E) ≠ 0 := by
      intro hzero
      exact b.toBasis.ne_zero i (Subtype.ext hzero)
    have hpositive : 0 < stiffness (b i : E) (b i : E) :=
      stiffness_pos (b i : E) (LinearMap.mem_ker.mp (b i).2) hvec_ne
    have heigen_sub := hA.apply_eigenvectorBasis sector_finrank i
    have heigen : ambientStiffnessOperator stiffness (b i : E) =
        eigenvalue i • (b i : E) := by
      exact congrArg Subtype.val heigen_sub
    have hdiag : stiffness (b i : E) (b i : E) = eigenvalue i := by
      calc
        stiffness (b i : E) (b i : E) =
            inner ℝ (ambientStiffnessOperator stiffness (b i : E)) (b i : E) :=
          (ambientStiffnessOperator_pairing stiffness (b i : E) (b i : E)).symm
        _ = inner ℝ (eigenvalue i • (b i : E)) (b i : E) := by rw [heigen]
        _ = eigenvalue i := by
          rw [real_inner_smul_left]
          change eigenvalue i * inner ℝ (b i) (b i) = eigenvalue i
          rw [b.inner_eq_one]
          ring
    rwa [hdiag] at hpositive
  refine
    { vector := fun i => (b i : E)
      omega := fun i => Real.sqrt (eigenvalue i)
      positive := fun i => Real.sqrt_pos.2 (eigenvalue_pos i)
      mass_orthonormal := ?_
      eigenmode := ?_
      complete := ?_ }
  · intro i j
    exact b.inner_eq_ite i j
  · intro i x
    have heigen_sub := hA.apply_eigenvectorBasis sector_finrank i
    have heigen : ambientStiffnessOperator stiffness (b i : E) =
        eigenvalue i • (b i : E) := by
      exact congrArg Subtype.val heigen_sub
    calc
      stiffness x (b i : E) = stiffness (b i : E) x := stiffness_symm.eq x (b i : E)
      _ = inner ℝ (ambientStiffnessOperator stiffness (b i : E)) x :=
        (ambientStiffnessOperator_pairing stiffness x (b i : E)).symm
      _ = inner ℝ (eigenvalue i • (b i : E)) x := by rw [heigen]
      _ = eigenvalue i * inner ℝ (b i : E) x := by
        rw [real_inner_smul_left]
      _ = eigenvalue i * inner ℝ x (b i : E) := by rw [real_inner_comm]
      _ = Real.sqrt (eigenvalue i) ^ 2 * inner ℝ x (b i : E) := by
        rw [Real.sq_sqrt (eigenvalue_pos i).le]
  · exact span_coe_orthonormalBasis (LinearMap.ker constraint) b

end InnerSpectral

section BilinearMassSpectral

variable {E V : Type*} [AddCommGroup E] [Module ℝ E]
  [FiniteDimensional ℝ E]
  [AddCommGroup V] [Module ℝ V]

/-- The generalized stiffness operator `M⁻¹K` defined without choosing
background Euclidean coordinates. -/
def bilinearStiffnessOperator
    (mass stiffness : LinearMap.BilinForm ℝ E)
    (mass_pos : ∀ x : E, x ≠ 0 → 0 < mass x x) : E →ₗ[ℝ] E :=
  stiffness.symmCompOfNondegenerate mass (mass_nondegenerate mass mass_pos)

theorem bilinearStiffnessOperator_pairing
    (mass stiffness : LinearMap.BilinForm ℝ E)
    (mass_pos : ∀ x : E, x ≠ 0 → 0 < mass x x)
    (x y : E) :
    mass (bilinearStiffnessOperator mass stiffness mass_pos y) x =
      stiffness y x :=
  LinearMap.BilinForm.symmCompOfNondegenerate_left_apply stiffness
    (mass_nondegenerate mass mass_pos) x y

/-- Generalized finite-dimensional spectral construction for an arbitrary
symmetric positive-definite mass form. -/
def positiveNormalFrameOfBilinearSpectral {n : ℕ}
    (mass stiffness : LinearMap.BilinForm ℝ E)
    (constraint : E →ₗ[ℝ] V)
    (mass_symm : mass.IsSymm)
    (mass_pos : ∀ x : E, x ≠ 0 → 0 < mass x x)
    (stiffness_symm : stiffness.IsSymm)
    (invariant : ∀ x, constraint x = 0 →
      constraint (bilinearStiffnessOperator mass stiffness mass_pos x) = 0)
    (stiffness_pos : ∀ x : E, constraint x = 0 → x ≠ 0 → 0 < stiffness x x)
    (sector_finrank : Module.finrank ℝ (LinearMap.ker constraint) = n) :
    PositiveNormalFrame (ι := Fin n) mass stiffness constraint := by
  let core := massInnerProductCore mass mass_symm mass_pos
  letI : InnerProductSpace.Core ℝ E := core
  letI : NormedAddCommGroup E := core.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E :=
    InnerProductSpace.ofCore (show PreInnerProductSpace.Core ℝ E from inferInstance)
  exact positiveNormalFrameOfSpectral stiffness constraint stiffness_symm invariant
    stiffness_pos sector_finrank

end BilinearMassSpectral

#print axioms mass_nondegenerate
#print axioms sectorStiffnessOperator_isSymmetric
#print axioms positiveNormalFrameOfSpectral
#print axioms positiveNormalFrameOfBilinearSpectral

end

end OPH.WhitneyNormalModes

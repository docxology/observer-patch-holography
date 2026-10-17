module
public import WhitneyConeModes
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace OPH.WhitneyFrameNaturality

open OPH.WhitneyQuantumBridge

noncomputable section

variable {i j k : Type*} [Fintype i] [DecidableEq i]
  [Fintype j] [DecidableEq j] [Fintype k] [DecidableEq k]
variable {E V : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup V] [Module ℝ V]
variable {mass stiffness : LinearMap.BilinForm ℝ E}
  {constraint : E →ₗ[ℝ] V}

/-- The overlap matrix of two complete positive frames, computed from the
source mass pairing rather than supplied as extra transition data. -/
def frameOverlap
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (b : j) (a : i) : ℝ :=
  mass (G.vector b) (F.vector a)

/-- Coordinate transport induced by the source mass overlap. -/
def frameTransition
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint) :
    (i → ℝ) →ₗ[ℝ] (j → ℝ) where
  toFun q b := ∑ a, frameOverlap F G b a * q a
  map_add' q r := by
    funext b
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c q := by
    funext b
    simp only [Pi.smul_apply, smul_eq_mul]
    change (∑ x, frameOverlap F G b x * (c * q x)) =
      c * ∑ x, frameOverlap F G b x * q x
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem mass_vector_reconstruct
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (_mass_symm : mass.IsSymm) (a : i) (q : i → ℝ) :
    mass (F.vector a) (reconstruct F.vector q) = q a := by
  simp only [reconstruct, map_sum,
    map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · rw [F.mass_orthonormal]
    simp
  · intro b _ hba
    rw [F.mass_orthonormal]
    simp [Ne.symm hba]
  · simp

theorem frame_linearIndependent
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint) :
    LinearIndependent ℝ F.vector := by
  rw [Fintype.linearIndependent_iff]
  intro q hsum x
  have h := congrArg (mass (F.vector x)) hsum
  simpa [map_sum, map_smul, F.mass_orthonormal] using h

/-- Completeness and mass orthonormality force every admissible frame to
have exactly the constrained-sector dimension. -/
theorem frame_card_eq_sector_finrank
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint) :
    Fintype.card i = Module.finrank ℝ (LinearMap.ker constraint) := by
  have h := linearIndependent_iff_card_eq_finrank_span.mp (frame_linearIndependent F)
  unfold Set.finrank at h
  rwa [F.complete] at h

omit [Fintype j] in
theorem frameTransition_apply
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (q : i → ℝ) (b : j) :
    frameTransition F G q b = mass (G.vector b) (reconstruct F.vector q) := by
  simp only [frameTransition, frameOverlap, reconstruct, map_sum,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A complete target frame reconstructs exactly the same constrained field
after overlap-coordinate transport. -/
theorem reconstruct_frameTransition
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (q : i → ℝ) :
    reconstruct G.vector (frameTransition F G q) = reconstruct F.vector q := by
  let z := reconstruct G.vector (frameTransition F G q) - reconstruct F.vector q
  have hzConstraint : constraint z = 0 := by
    simp only [z, map_sub, reconstruct_constrained F q,
      reconstruct_constrained G (frameTransition F G q), sub_self]
  obtain ⟨r, hr⟩ := reconstruct_surjective G z hzConstraint
  have hrzero : r = 0 := by
    funext b
    change r b = 0
    have hcoefficient := mass_vector_reconstruct G mass_symm b r
    rw [hr] at hcoefficient
    have hleft := mass_vector_reconstruct G mass_symm b (frameTransition F G q)
    rw [frameTransition_apply] at hleft
    dsimp [z] at hcoefficient
    rw [map_sub] at hcoefficient
    rw [hleft] at hcoefficient
    linarith
  have hz : z = 0 := by
    rw [← hr, hrzero]
    simp [reconstruct]
  exact sub_eq_zero.mp hz

theorem frameTransition_self
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (mass_symm : mass.IsSymm) :
    frameTransition F F = LinearMap.id := by
  apply LinearMap.ext
  intro q
  funext a
  rw [frameTransition_apply]
  exact mass_vector_reconstruct F mass_symm a q

omit [Fintype k] in
theorem frameTransition_comp
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (H : PositiveNormalFrame (ι := k) mass stiffness constraint)
    (mass_symm : mass.IsSymm) :
    (frameTransition G H).comp (frameTransition F G) = frameTransition F H := by
  apply LinearMap.ext
  intro q
  funext c
  simp only [LinearMap.comp_apply]
  rw [frameTransition_apply, frameTransition_apply]
  rw [reconstruct_frameTransition F G mass_symm]

theorem frameTransition_leftInverse
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) :
    Function.LeftInverse (frameTransition G F) (frameTransition F G) := by
  intro q
  have h := congrArg (fun L : (i → ℝ) →ₗ[ℝ] (i → ℝ) => L q)
    (frameTransition_comp F G F mass_symm)
  simpa [frameTransition_self F mass_symm] using h

theorem frameTransition_rightInverse
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) :
    Function.RightInverse (frameTransition G F) (frameTransition F G) := by
  intro q
  have h := congrArg (fun L : (j → ℝ) →ₗ[ℝ] (j → ℝ) => L q)
    (frameTransition_comp G F G mass_symm)
  simpa [frameTransition_self G mass_symm] using h

omit [Fintype i] [Fintype j] in
theorem frameOverlap_frequency_sq
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (stiffness_symm : stiffness.IsSymm)
    (b : j) (a : i) :
    G.omega b ^ 2 * frameOverlap F G b a =
      F.omega a ^ 2 * frameOverlap F G b a := by
  unfold frameOverlap
  calc
    G.omega b ^ 2 * mass (G.vector b) (F.vector a) =
        stiffness (F.vector a) (G.vector b) := by
      rw [G.eigenmode]
      rw [mass_symm.eq]
    _ = stiffness (G.vector b) (F.vector a) := stiffness_symm.eq _ _
    _ = F.omega a ^ 2 * mass (G.vector b) (F.vector a) := by
      rw [F.eigenmode]

omit [Fintype i] [Fintype j] in
theorem frameOverlap_frequency
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (stiffness_symm : stiffness.IsSymm)
    (b : j) (a : i) :
    G.omega b * frameOverlap F G b a =
      F.omega a * frameOverlap F G b a := by
  by_cases hR : frameOverlap F G b a = 0
  · simp [hR]
  · have hsquare := frameOverlap_frequency_sq F G mass_symm stiffness_symm b a
    have heq : G.omega b ^ 2 = F.omega a ^ 2 := by
      exact mul_right_cancel₀ hR hsquare
    have hsum : 0 < G.omega b + F.omega a := add_pos (G.positive b) (F.positive a)
    have hfactor : (G.omega b - F.omega a) * (G.omega b + F.omega a) = 0 := by
      nlinarith
    have homega : G.omega b = F.omega a := by
      rcases mul_eq_zero.mp hfactor with h | h
      · linarith
      · exact False.elim (ne_of_gt hsum h)
    rw [homega]

omit [Fintype i] [Fintype j] in
theorem frameOverlap_eq_zero_of_frequency_ne
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (stiffness_symm : stiffness.IsSymm)
    (b : j) (a : i) (hne : G.omega b ≠ F.omega a) :
    frameOverlap F G b a = 0 := by
  by_contra hnonzero
  have hfreq := frameOverlap_frequency F G mass_symm stiffness_symm b a
  apply hne
  exact mul_right_cancel₀ hnonzero hfreq

omit [Fintype i] in
theorem no_frame_fixed_by_neg [Nonempty i]
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint) :
    ¬ ∀ x, -F.vector x = F.vector x := by
  intro hfixed
  let x : i := Classical.choice inferInstance
  have hzero : F.vector x = 0 := by
    have htwo : (2 : ℝ) • F.vector x = 0 := by
      calc
        (2 : ℝ) • F.vector x = F.vector x + F.vector x := two_smul ℝ (F.vector x)
        _ = -F.vector x + F.vector x :=
          congrArg (fun z => z + F.vector x) (hfixed x).symm
        _ = 0 := neg_add_cancel (F.vector x)
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hnorm := F.mass_orthonormal x x
  simp [hzero] at hnorm

/-- Reversing every mode orientation gives a second admissible frame. -/
def signFlipFrame
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint) :
    PositiveNormalFrame (ι := i) mass stiffness constraint where
  vector x := -F.vector x
  omega := F.omega
  positive := F.positive
  mass_orthonormal x y := by
    simp [F.mass_orthonormal]
  eigenmode x y := by
    simp [F.eigenmode]
  complete := by
    rw [← F.complete]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact Submodule.neg_mem _
        (Submodule.subset_span (Set.mem_range_self x))
    · apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      have hneg : -F.vector y ∈
          Submodule.span ℝ (Set.range fun z => -F.vector z) :=
        Submodule.subset_span (Set.mem_range_self y)
      simpa using Submodule.neg_mem _ hneg

omit [Fintype i] in
theorem signFlipFrame_ne [Nonempty i]
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint) :
    signFlipFrame F ≠ F := by
  intro h
  apply no_frame_fixed_by_neg F
  intro x
  exact congrArg (fun G => G.vector x) h

/-- Pure relabeling preserves every frame obligation. -/
def reindexFrame
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint) (e : j ≃ i) :
    PositiveNormalFrame (ι := j) mass stiffness constraint where
  vector x := F.vector (e x)
  omega x := F.omega (e x)
  positive x := F.positive (e x)
  mass_orthonormal x y := by
    rw [F.mass_orthonormal]
    simp only [e.injective.eq_iff]
  eigenmode x y := F.eigenmode (e x) y
  complete := by
    rw [← F.complete]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self (e x))
    · apply Submodule.span_le.mpr
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact Submodule.subset_span ⟨e.symm y, by simp⟩

omit [Fintype k] in
theorem frameOverlap_comp
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (H : PositiveNormalFrame (ι := k) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (c : k) (a : i) :
    (∑ b, frameOverlap G H c b * frameOverlap F G b a) =
      frameOverlap F H c a := by
  let q : i → ℝ := fun x => if x = a then 1 else 0
  have h := congrArg (fun L : (i → ℝ) →ₗ[ℝ] (k → ℝ) => L q)
    (frameTransition_comp F G H mass_symm)
  have hc := congrFun h c
  simpa [LinearMap.comp_apply, frameTransition, q] using hc

/-- Linear substitution of polynomial mode variables induced by the same
source-derived frame transition. -/
def linearVariable
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (a : i) : ParticlePolynomial j :=
  ∑ b, MvPolynomial.C (frameOverlap F G b a : ℂ) * MvPolynomial.X b

def polynomialTransport
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint) :
    ParticlePolynomial i →ₐ[ℂ] ParticlePolynomial j :=
  MvPolynomial.bind₁ (linearVariable F G)

theorem linearVariable_self
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (a : i) : linearVariable F F a = MvPolynomial.X a := by
  simp only [linearVariable, frameOverlap]
  rw [Finset.sum_eq_single a]
  · rw [F.mass_orthonormal]
    simp
  · intro b _ hba
    rw [F.mass_orthonormal]
    simp [hba]
  · simp

theorem polynomialTransport_self
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint) :
    polynomialTransport F F = AlgHom.id ℂ (ParticlePolynomial i) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [polynomialTransport, linearVariable_self]

theorem polynomialTransport_linearVariable
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (H : PositiveNormalFrame (ι := k) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (a : i) :
    polynomialTransport G H (linearVariable F G a) = linearVariable F H a := by
  unfold polynomialTransport linearVariable
  simp only [map_sum, map_mul, MvPolynomial.bind₁_C_right,
    MvPolynomial.bind₁_X_right]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul]
  congr 1
  rw [← map_sum]
  congr 1
  have hreal : (∑ b, frameOverlap F G b a * frameOverlap G H c b) =
      frameOverlap F H c a := by
    calc
      (∑ b, frameOverlap F G b a * frameOverlap G H c b) =
          ∑ b, frameOverlap G H c b * frameOverlap F G b a := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = frameOverlap F H c a := frameOverlap_comp F G H mass_symm c a
  exact_mod_cast hreal

theorem polynomialTransport_comp
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (H : PositiveNormalFrame (ι := k) mass stiffness constraint)
    (mass_symm : mass.IsSymm) :
    (polynomialTransport G H).comp (polynomialTransport F G) =
      polynomialTransport F H := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, polynomialTransport,
    MvPolynomial.bind₁_X_right]
  exact polynomialTransport_linearVariable F G H mass_symm a

/-- The non-vacuum part of the published polynomial Hamiltonian. -/
def weightedNumberOperator {a : Type*} [Fintype a]
    (omega : a → ℝ) (p : ParticlePolynomial a) : ParticlePolynomial a :=
  ∑ x, ((omega x : ℝ) : ℂ) • numberOperator x p

theorem weightedNumberOperator_add {a : Type*} [Fintype a]
    (omega : a → ℝ) (p q : ParticlePolynomial a) :
    weightedNumberOperator omega (p + q) =
      weightedNumberOperator omega p + weightedNumberOperator omega q := by
  unfold weightedNumberOperator numberOperator creation annihilation
  simp only [map_add, mul_add, smul_add, Finset.sum_add_distrib]

theorem weightedNumberOperator_smul {a : Type*} [Fintype a]
    (omega : a → ℝ) (c : ℂ) (p : ParticlePolynomial a) :
    weightedNumberOperator omega (c • p) = c • weightedNumberOperator omega p := by
  unfold weightedNumberOperator numberOperator creation annihilation
  simp only [Derivation.map_smul, mul_smul_comm, smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  module

theorem weightedNumberOperator_mul {a : Type*} [Fintype a]
    (omega : a → ℝ) (p q : ParticlePolynomial a) :
    weightedNumberOperator omega (p * q) =
      weightedNumberOperator omega p * q + p * weightedNumberOperator omega q := by
  unfold weightedNumberOperator numberOperator creation annihilation
  simp_rw [MvPolynomial.pderiv_mul, mul_add, smul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  apply congrArg₂ (.+.)
  · apply Finset.sum_congr rfl
    intro x _
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  · apply Finset.sum_congr rfl
    intro x _
    simp only [MvPolynomial.smul_eq_C_mul]
    ring

theorem weightedNumberOperator_X {a : Type*} [Fintype a] [DecidableEq a]
    (omega : a → ℝ) (x : a) :
    weightedNumberOperator omega (MvPolynomial.X x) =
      ((omega x : ℝ) : ℂ) • MvPolynomial.X x := by
  unfold weightedNumberOperator numberOperator creation annihilation
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hy)]
    simp
  · simp

theorem weightedNumberOperator_zero {a : Type*} [Fintype a]
    (omega : a → ℝ) :
    weightedNumberOperator omega (0 : ParticlePolynomial a) = 0 := by
  unfold weightedNumberOperator numberOperator creation annihilation
  simp

theorem weightedNumberOperator_sum {a b : Type*} [Fintype a] [DecidableEq b]
    (omega : a → ℝ) (s : Finset b) (f : b → ParticlePolynomial a) :
    weightedNumberOperator omega (∑ x ∈ s, f x) =
      ∑ x ∈ s, weightedNumberOperator omega (f x) := by
  induction s using Finset.induction_on with
  | empty => simp [weightedNumberOperator_zero]
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx, weightedNumberOperator_add, ih]

omit [Fintype i] in
theorem weightedNumberOperator_linearVariable
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (stiffness_symm : stiffness.IsSymm) (a : i) :
    weightedNumberOperator G.omega (linearVariable F G a) =
      ((F.omega a : ℝ) : ℂ) • linearVariable F G a := by
  unfold linearVariable
  rw [weightedNumberOperator_sum]
  simp_rw [MvPolynomial.C_mul', weightedNumberOperator_smul,
    weightedNumberOperator_X, smul_smul]
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
  apply Finset.sum_congr rfl
  intro b _
  have hreal : frameOverlap F G b a * G.omega b =
      F.omega a * frameOverlap F G b a := by
    calc
      frameOverlap F G b a * G.omega b =
          G.omega b * frameOverlap F G b a := by ring
      _ = F.omega a * frameOverlap F G b a :=
        frameOverlap_frequency F G mass_symm stiffness_symm b a
  have hcomplex : (frameOverlap F G b a : ℂ) * (G.omega b : ℂ) =
      (F.omega a : ℂ) * (frameOverlap F G b a : ℂ) := by
    exact_mod_cast hreal
  rw [hcomplex]

theorem weightedNumberOperator_polynomialTransport
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (stiffness_symm : stiffness.IsSymm)
    (p : ParticlePolynomial i) :
    weightedNumberOperator G.omega (polynomialTransport F G p) =
      polynomialTransport F G (weightedNumberOperator F.omega p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp [polynomialTransport, weightedNumberOperator, numberOperator,
        creation, annihilation]
  | add p q hp hq =>
      rw [map_add, weightedNumberOperator_add, weightedNumberOperator_add, hp, hq, map_add]
  | mul_X p a hp =>
      rw [map_mul]
      have hX : polynomialTransport F G (MvPolynomial.X a) = linearVariable F G a := by
        simp [polynomialTransport]
      rw [hX]
      change weightedNumberOperator G.omega
        (polynomialTransport F G p * linearVariable F G a) = _
      rw [weightedNumberOperator_mul, hp,
        weightedNumberOperator_linearVariable F G mass_symm stiffness_symm]
      rw [weightedNumberOperator_mul, weightedNumberOperator_X]
      simp only [map_add, map_mul, map_smul]
      rw [hX]

theorem frameOverlap_column_sq
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (a : i) :
    (∑ b, frameOverlap F G b a ^ 2) = 1 := by
  let q : i → ℝ := fun x => if x = a then 1 else 0
  have h := frameTransition_leftInverse F G mass_symm q
  have ha := congrFun h a
  simpa [frameTransition, frameOverlap, q, pow_two, mass_symm.eq] using ha

theorem frameOverlap_row_sq
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (b : j) :
    (∑ a, frameOverlap F G b a ^ 2) = 1 := by
  let q : j → ℝ := fun x => if x = b then 1 else 0
  have h := frameTransition_rightInverse F G mass_symm q
  have hb := congrFun h b
  simpa [frameTransition, frameOverlap, q, pow_two, mass_symm.eq] using hb

theorem frame_frequency_sum_eq
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (stiffness_symm : stiffness.IsSymm) :
    (∑ a, F.omega a) = ∑ b, G.omega b := by
  have hcolumn (a : i) : F.omega a =
      ∑ b, frameOverlap F G b a ^ 2 * G.omega b := by
    calc
      F.omega a = (∑ b, frameOverlap F G b a ^ 2) * F.omega a := by
        rw [frameOverlap_column_sq F G mass_symm, one_mul]
      _ = ∑ b, frameOverlap F G b a ^ 2 * F.omega a := by
        rw [Finset.sum_mul]
      _ = ∑ b, frameOverlap F G b a ^ 2 * G.omega b := by
        apply Finset.sum_congr rfl
        intro b _
        have hfreq := frameOverlap_frequency F G mass_symm stiffness_symm b a
        calc
          frameOverlap F G b a ^ 2 * F.omega a =
              frameOverlap F G b a *
                (F.omega a * frameOverlap F G b a) := by ring
          _ = frameOverlap F G b a *
                (G.omega b * frameOverlap F G b a) := by rw [hfreq]
          _ = frameOverlap F G b a ^ 2 * G.omega b := by ring
  calc
    (∑ a, F.omega a) = ∑ a, ∑ b, frameOverlap F G b a ^ 2 * G.omega b := by
      apply Finset.sum_congr rfl
      intro a _
      exact hcolumn a
    _ = ∑ b, ∑ a, frameOverlap F G b a ^ 2 * G.omega b :=
      Finset.sum_comm
    _ = ∑ b, G.omega b := by
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_mul, frameOverlap_row_sq F G mass_symm, one_mul]

theorem quantumHamiltonian_eq_weightedNumber {a : Type*} [Fintype a]
    (hbar : ℝ) (omega : a → ℝ) (p : ParticlePolynomial a) :
    quantumHamiltonian hbar omega p =
      (hbar : ℂ) • weightedNumberOperator omega p +
        ((hbar * (∑ x, omega x) / 2 : ℝ) : ℂ) • p := by
  unfold quantumHamiltonian weightedNumberOperator
  simp_rw [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  apply congrArg₂ (.+.)
  · apply Finset.sum_congr rfl
    intro x _
    push_cast
    congr 1
  · rw [← Finset.sum_smul]
    congr 1
    push_cast
    simp only [div_eq_mul_inv, one_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem quantumHamiltonian_polynomialTransport
    (F : PositiveNormalFrame (ι := i) mass stiffness constraint)
    (G : PositiveNormalFrame (ι := j) mass stiffness constraint)
    (mass_symm : mass.IsSymm) (stiffness_symm : stiffness.IsSymm)
    (hbar : ℝ) (p : ParticlePolynomial i) :
    quantumHamiltonian hbar G.omega (polynomialTransport F G p) =
      polynomialTransport F G (quantumHamiltonian hbar F.omega p) := by
  rw [quantumHamiltonian_eq_weightedNumber,
    quantumHamiltonian_eq_weightedNumber]
  rw [weightedNumberOperator_polynomialTransport F G mass_symm stiffness_symm]
  rw [frame_frequency_sum_eq F G mass_symm stiffness_symm]
  simp only [map_add, map_smul]

#print axioms reconstruct_frameTransition
#print axioms frame_card_eq_sector_finrank
#print axioms frameTransition_self
#print axioms frameTransition_comp
#print axioms frameOverlap_frequency
#print axioms frameOverlap_eq_zero_of_frequency_ne
#print axioms no_frame_fixed_by_neg
#print axioms signFlipFrame_ne
#print axioms reindexFrame
#print axioms polynomialTransport_self
#print axioms polynomialTransport_comp
#print axioms weightedNumberOperator_polynomialTransport
#print axioms frame_frequency_sum_eq
#print axioms quantumHamiltonian_polynomialTransport

end


end OPH.WhitneyFrameNaturality

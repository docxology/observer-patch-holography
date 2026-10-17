module
public import WhitneyFrameNaturality

@[expose] public section

set_option autoImplicit false

namespace OPH.WhitneyFrameMorphism

open OPH.WhitneyQuantumBridge
open OPH.WhitneyFrameNaturality

noncomputable section

variable {a b c : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
variable {E₁ E₂ E₃ V₁ V₂ V₃ : Type*}
  [AddCommGroup E₁] [Module ℝ E₁]
  [AddCommGroup E₂] [Module ℝ E₂]
  [AddCommGroup E₃] [Module ℝ E₃]
  [AddCommGroup V₁] [Module ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂]
  [AddCommGroup V₃] [Module ℝ V₃]
variable {mass₁ stiffness₁ : LinearMap.BilinForm ℝ E₁}
  {mass₂ stiffness₂ : LinearMap.BilinForm ℝ E₂}
  {mass₃ stiffness₃ : LinearMap.BilinForm ℝ E₃}
  {constraint₁ : E₁ →ₗ[ℝ] V₁} {constraint₂ : E₂ →ₗ[ℝ] V₂}
  {constraint₃ : E₃ →ₗ[ℝ] V₃}

/-- A physical-sector isomorphism. The mass, stiffness, and exact constrained
sector are the only structures used by normal-mode naturality. -/
structure FrameIsometry
    (mass₁ : LinearMap.BilinForm ℝ E₁)
    (stiffness₁ : LinearMap.BilinForm ℝ E₁)
    (constraint₁ : E₁ →ₗ[ℝ] V₁)
    (mass₂ : LinearMap.BilinForm ℝ E₂)
    (stiffness₂ : LinearMap.BilinForm ℝ E₂)
    (constraint₂ : E₂ →ₗ[ℝ] V₂) where
  toLinearEquiv : E₁ ≃ₗ[ℝ] E₂
  mass_preserving : ∀ x y, mass₂ (toLinearEquiv x) (toLinearEquiv y) = mass₁ x y
  stiffness_preserving : ∀ x y,
    stiffness₂ (toLinearEquiv x) (toLinearEquiv y) = stiffness₁ x y
  constrained_iff : ∀ x, constraint₂ (toLinearEquiv x) = 0 ↔ constraint₁ x = 0

namespace FrameIsometry

instance : CoeFun (FrameIsometry mass₁ stiffness₁ constraint₁
    mass₂ stiffness₂ constraint₂) (fun _ => E₁ → E₂) where
  coe T := T.toLinearEquiv

def refl : FrameIsometry mass₁ stiffness₁ constraint₁
    mass₁ stiffness₁ constraint₁ where
  toLinearEquiv := LinearEquiv.refl ℝ E₁
  mass_preserving _ _ := rfl
  stiffness_preserving _ _ := rfl
  constrained_iff _ := Iff.rfl

def trans
    (T₁ : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (T₂ : FrameIsometry mass₂ stiffness₂ constraint₂
      mass₃ stiffness₃ constraint₃) :
    FrameIsometry mass₁ stiffness₁ constraint₁
      mass₃ stiffness₃ constraint₃ where
  toLinearEquiv := T₁.toLinearEquiv.trans T₂.toLinearEquiv
  mass_preserving x y := by
    change mass₃ (T₂ (T₁ x)) (T₂ (T₁ y)) = mass₁ x y
    rw [T₂.mass_preserving, T₁.mass_preserving]
  stiffness_preserving x y := by
    change stiffness₃ (T₂ (T₁ x)) (T₂ (T₁ y)) = stiffness₁ x y
    rw [T₂.stiffness_preserving, T₁.stiffness_preserving]
  constrained_iff x := T₂.constrained_iff _ |>.trans (T₁.constrained_iff x)

/-- Push a complete frame through a physical-sector isomorphism. -/
def mapFrame
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁) :
    PositiveNormalFrame (ι := a) mass₂ stiffness₂ constraint₂ where
  vector x := T (F.vector x)
  omega := F.omega
  positive := F.positive
  mass_orthonormal x y := by
    rw [T.mass_preserving]
    exact F.mass_orthonormal x y
  eigenmode x y := by
    let z := T.toLinearEquiv.symm y
    have hy : T z = y := T.toLinearEquiv.apply_symm_apply y
    rw [← hy, T.stiffness_preserving, F.eigenmode, T.mass_preserving]
  complete := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply (T.constrained_iff (F.vector x)).mpr
      apply LinearMap.mem_ker.mp
      rw [← F.complete]
      exact Submodule.subset_span (Set.mem_range_self x)
    · intro y hy
      let x := T.toLinearEquiv.symm y
      have hx : constraint₁ x = 0 := by
        apply (T.constrained_iff x).mp
        simpa [x] using LinearMap.mem_ker.mp hy
      obtain ⟨q, hq⟩ := reconstruct_surjective F x hx
      have hreconstruct : reconstruct (fun z => T (F.vector z)) q = y := by
        calc
          reconstruct (fun z => T (F.vector z)) q =
              T (reconstruct F.vector q) := by
            simp [reconstruct, map_sum, map_smul]
          _ = T x := by rw [hq]
          _ = y := T.toLinearEquiv.apply_symm_apply y
      rw [← hreconstruct]
      apply Submodule.sum_mem
      intro z _
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self z))

theorem reconstruct_mapFrame
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (q : a → ℝ) :
    reconstruct (mapFrame T F).vector q = T (reconstruct F.vector q) := by
  simp [reconstruct, mapFrame, map_sum, map_smul]

/-- The two-object transition matrix `R_{ba}=M₂(G_b,T F_a)` and its
coordinate map are obtained by reusing the same-space overlap after pushforward. -/
def transition
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂) :
    (a → ℝ) →ₗ[ℝ] (b → ℝ) :=
  frameTransition (mapFrame T F) G

omit [Fintype b] in
theorem transition_apply
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂)
    (q : a → ℝ) (y : b) :
    transition T F G q y = mass₂ (G.vector y) (T (reconstruct F.vector q)) := by
  rw [transition, frameTransition_apply, reconstruct_mapFrame]

theorem reconstruct_transition
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂)
    (mass₂_symm : mass₂.IsSymm) (q : a → ℝ) :
    reconstruct G.vector (transition T F G q) = T (reconstruct F.vector q) := by
  rw [transition, reconstruct_frameTransition]
  exact reconstruct_mapFrame T F q
  exact mass₂_symm

theorem classicalAction_naturality
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂)
    (mass₂_symm : mass₂.IsSymm) (q velocity : a → ℝ) :
    (∑ x, (velocity x ^ 2 - F.omega x ^ 2 * q x ^ 2) / 2) =
      ∑ y, ((transition T F G velocity y) ^ 2 -
        G.omega y ^ 2 * (transition T F G q y) ^ 2) / 2 := by
  rw [← same_action_normal_modes F q velocity,
    ← same_action_normal_modes G (transition T F G q) (transition T F G velocity)]
  rw [reconstruct_transition T F G mass₂_symm q,
    reconstruct_transition T F G mass₂_symm velocity]
  rw [T.mass_preserving, T.stiffness_preserving]

def polynomialMap
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂) :
    ParticlePolynomial a →ₐ[ℂ] ParticlePolynomial b :=
  polynomialTransport (mapFrame T F) G

theorem quantumHamiltonian_naturality
    (T : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂)
    (mass₂_symm : mass₂.IsSymm) (stiffness₂_symm : stiffness₂.IsSymm)
    (hbar : ℝ) (p : ParticlePolynomial a) :
    quantumHamiltonian hbar G.omega (polynomialMap T F G p) =
      polynomialMap T F G (quantumHamiltonian hbar F.omega p) :=
  quantumHamiltonian_polynomialTransport (mapFrame T F) G
    mass₂_symm stiffness₂_symm hbar p

theorem transition_refl
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (mass₁_symm : mass₁.IsSymm) :
    transition (refl (mass₁ := mass₁) (stiffness₁ := stiffness₁)
      (constraint₁ := constraint₁)) F F = LinearMap.id := by
  apply LinearMap.ext
  intro q
  funext x
  rw [transition_apply]
  change mass₁ (F.vector x) (reconstruct F.vector q) = q x
  exact mass_vector_reconstruct F mass₁_symm x q

omit [Fintype c] in
theorem transition_trans
    (T₁ : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (T₂ : FrameIsometry mass₂ stiffness₂ constraint₂
      mass₃ stiffness₃ constraint₃)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂)
    (H : PositiveNormalFrame (ι := c) mass₃ stiffness₃ constraint₃)
    (mass₂_symm : mass₂.IsSymm) :
    (transition T₂ G H).comp (transition T₁ F G) =
      transition (trans T₁ T₂) F H := by
  apply LinearMap.ext
  intro q
  funext z
  simp only [LinearMap.comp_apply]
  rw [transition_apply]
  have hreconstruct := reconstruct_transition T₁ F G mass₂_symm q
  rw [hreconstruct]
  rw [transition_apply]
  rfl

theorem polynomialMap_refl
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁) :
    polynomialMap (refl (mass₁ := mass₁) (stiffness₁ := stiffness₁)
      (constraint₁ := constraint₁)) F F =
      AlgHom.id ℂ (ParticlePolynomial a) := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [polynomialMap, polynomialTransport,
    MvPolynomial.bind₁_X_right, linearVariable, mapFrame, frameOverlap,
    refl, LinearEquiv.refl_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single x]
  · rw [F.mass_orthonormal]
    simp
  · intro y _ hy
    rw [F.mass_orthonormal]
    simp [hy]
  · simp

theorem polynomialMap_trans
    (T₁ : FrameIsometry mass₁ stiffness₁ constraint₁
      mass₂ stiffness₂ constraint₂)
    (T₂ : FrameIsometry mass₂ stiffness₂ constraint₂
      mass₃ stiffness₃ constraint₃)
    (F : PositiveNormalFrame (ι := a) mass₁ stiffness₁ constraint₁)
    (G : PositiveNormalFrame (ι := b) mass₂ stiffness₂ constraint₂)
    (H : PositiveNormalFrame (ι := c) mass₃ stiffness₃ constraint₃)
    (mass₂_symm : mass₂.IsSymm) (_mass₃_symm : mass₃.IsSymm) :
    (polynomialMap T₂ G H).comp (polynomialMap T₁ F G) =
      polynomialMap (trans T₁ T₂) F H := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [AlgHom.comp_apply, polynomialMap, polynomialTransport,
    MvPolynomial.bind₁_X_right]
  unfold linearVariable
  simp only [map_sum, map_mul, MvPolynomial.bind₁_C_right,
    MvPolynomial.bind₁_X_right]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.sum_mul, ← map_sum]
  congr 2
  have htransition := transition_trans T₁ T₂ F G H mass₂_symm
  have h := congrArg
    (fun L : (a → ℝ) →ₗ[ℝ] (c → ℝ) => L (fun y => if y = x then 1 else 0))
    htransition
  have hz := congrFun h z
  have hzreal : (∑ y,
      mass₂ (G.vector y) (T₁ (F.vector x)) *
        mass₃ (H.vector z) (T₂ (G.vector y))) =
      mass₃ (H.vector z) ((trans T₁ T₂) (F.vector x)) := by
    calc
      _ = ∑ y,
          mass₃ (H.vector z) (T₂ (G.vector y)) *
            mass₂ (G.vector y) (T₁ (F.vector x)) := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by simpa [transition, frameTransition, frameOverlap, mapFrame] using hz
  exact_mod_cast hzreal

#print axioms reconstruct_transition
#print axioms classicalAction_naturality
#print axioms quantumHamiltonian_naturality
#print axioms transition_refl
#print axioms transition_trans
#print axioms polynomialMap_refl
#print axioms polynomialMap_trans

end FrameIsometry

end

end OPH.WhitneyFrameMorphism

module
public import QFT.TripleCarrierJoin

@[expose] public section

/-!
# Operator embeddings on the same three-observer carrier

The two committed pair algebras embed into `TripleCarrier` by adjoining the
identity of the unused observer. These are injective unital star homomorphisms,
unlike the opposite-direction partial-trace channels. Their intersection is
the full observer-86 matrix algebra, and together they generate the full triple
matrix algebra. The embeddings intertwine the 31 actual source-row transitions.

The tensor assembly and path-read transpositions remain declared operations.
The empirical diagonal state is not the independently supplied uniform state
of either constant tower. No physical region, clock, quantum outcome, continuum
limit, source-selected tensor factorization or universal algebraic pushout is
claimed. In particular, the two overlapping pair algebras do not commute.
-/

set_option autoImplicit false
set_option maxRecDepth 65536

namespace OPH.QFT

open Matrix
open Kronecker

noncomputable section

/-- Include the 86/88 pair with observer 247 as an identity spectator. -/
def operatorJoin88 :
    Matrix PairIndex PairIndex ℂ →⋆ₐ[ℂ] Matrix TripleCarrier TripleCarrier ℂ :=
  slotLeft (Fin 13)

/-- The existing middle-trace coordinate equivalence as a star equivalence. -/
def operatorJoinReindex :
    Matrix (PairIndex247 × Fin 14) (PairIndex247 × Fin 14) ℂ ≃⋆ₐ[ℂ]
      Matrix TripleCarrier TripleCarrier ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ middleTraceIndexEquiv)
    (fun M => by
      simp only [Matrix.coe_reindexAlgEquiv, Matrix.star_eq_conjTranspose]
      exact reindex_conjTranspose middleTraceIndexEquiv M)

/-- Include the 86/247 pair with observer 88 as an identity spectator. -/
def operatorJoin247 :
    Matrix PairIndex247 PairIndex247 ℂ →⋆ₐ[ℂ]
      Matrix TripleCarrier TripleCarrier ℂ :=
  (operatorJoinReindex).toStarAlgHom.comp (slotLeft (Fin 14))

/-- The common full observer-86 factor, including off-diagonal operators. -/
def operatorJoin86 :
    Matrix (Fin 13) (Fin 13) ℂ →⋆ₐ[ℂ]
      Matrix TripleCarrier TripleCarrier ℂ :=
  operatorJoin88.comp (slotLeft (Fin 14))

@[simp] theorem operatorJoin88_apply (A : Matrix PairIndex PairIndex ℂ)
    (q r : TripleCarrier) :
    operatorJoin88 A q r = A q.1 r.1 * if q.2 = r.2 then 1 else 0 := by
  simp [operatorJoin88, slotLeft, Matrix.kroneckerMap_apply, Matrix.one_apply]

@[simp] theorem operatorJoin247_apply (A : Matrix PairIndex247 PairIndex247 ℂ)
    (q r : TripleCarrier) :
    operatorJoin247 A q r = A (q.1.1, q.2) (r.1.1, r.2) *
      if q.1.2 = r.1.2 then 1 else 0 := by
  simp [operatorJoin247, operatorJoinReindex, slotLeft,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    middleTraceIndexEquiv, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem operatorJoin88_injective : Function.Injective operatorJoin88 :=
  slotLeft_injective

theorem operatorJoin247_injective : Function.Injective operatorJoin247 := by
  intro A B h
  exact slotLeft_injective (operatorJoinReindex.injective h)

theorem operatorJoin86_injective : Function.Injective operatorJoin86 :=
  operatorJoin88_injective.comp slotLeft_injective

/-- Both observable embeddings have exactly the same full hinge. -/
theorem operatorJoin_hinge (A : Matrix (Fin 13) (Fin 13) ℂ) :
    operatorJoin247 (slotLeft (Fin 13) A) = operatorJoin86 A := by
  ext q r
  simp [operatorJoin86, operatorJoin88_apply, operatorJoin247_apply,
    slotLeft, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_comm]

/-- Equality in the two pair images forces a full-matrix hinge representative. -/
theorem operatorJoin_equal_iff (A : Matrix PairIndex PairIndex ℂ)
    (B : Matrix PairIndex247 PairIndex247 ℂ) :
    operatorJoin88 A = operatorJoin247 B ↔
      ∃ H : Matrix (Fin 13) (Fin 13) ℂ,
        A = slotLeft (Fin 14) H ∧ B = slotLeft (Fin 13) H := by
  constructor
  · intro h
    let H : Matrix (Fin 13) (Fin 13) ℂ := fun a a' => B (a, 0) (a', 0)
    have ha : A = slotLeft (Fin 14) H := by
      ext p p'
      have he := congrFun (congrFun h (p, 0)) (p', 0)
      change A p p' = H p.1 p'.1 * (1 : Matrix (Fin 14) (Fin 14) ℂ) p.2 p'.2
      simpa only [operatorJoin88_apply, operatorJoin247_apply, H,
        Matrix.one_apply, ite_true, mul_one, mul_ite, mul_zero] using he
    refine ⟨H, ha, ?_⟩
    apply operatorJoin247_injective
    rw [operatorJoin_hinge, ← h, ha]
    rfl
  · rintro ⟨H, rfl, rfl⟩
    exact (operatorJoin_hinge H).symm

/-- Exact noncommutative intersection of the two pair images. -/
theorem operatorJoin_intersection :
    operatorJoin88.range ⊓ operatorJoin247.range = operatorJoin86.range := by
  ext M
  constructor
  · rintro ⟨⟨A, ha⟩, ⟨B, hb⟩⟩
    obtain ⟨H, hA, _⟩ := (operatorJoin_equal_iff A B).mp (ha.trans hb.symm)
    exact ⟨H, by rw [← ha, hA]; rfl⟩
  · rintro ⟨H, rfl⟩
    exact ⟨⟨slotLeft (Fin 14) H, rfl⟩,
      ⟨slotLeft (Fin 13) H, operatorJoin_hinge H⟩⟩

/-- An operator acting only on observer 247 has the same representation
through either the two-slot or three-slot association. -/
theorem operatorJoin247_right (B : Matrix (Fin 13) (Fin 13) ℂ) :
    operatorJoin247 (slotRight (Fin 13) B) = slotRight PairIndex B := by
  ext q r
  simp [operatorJoin247_apply, slotRight, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- The two proper overlapping pair algebras generate the whole common algebra. -/
theorem operatorJoin_generate_top :
    StarAlgebra.adjoin ℂ
      ((operatorJoin88.range : Set (Matrix TripleCarrier TripleCarrier ℂ)) ∪
        (operatorJoin247.range : Set (Matrix TripleCarrier TripleCarrier ℂ))) = ⊤ := by
  apply top_unique
  rw [← slot_ranges_generate_top (α := PairIndex) (β := Fin 13)]
  apply StarAlgebra.adjoin_mono
  rintro M (h | ⟨B, rfl⟩)
  · exact Or.inl h
  · exact Or.inr ⟨slotRight (Fin 13) B, operatorJoin247_right B⟩

/-- The exclusive observer-88 and observer-247 factors commute. -/
theorem operatorJoin_spectator_locality
    (B : Matrix (Fin 14) (Fin 14) ℂ) (C : Matrix (Fin 13) (Fin 13) ℂ) :
    Commute (operatorJoin88 (slotRight (Fin 13) B))
      (operatorJoin247 (slotRight (Fin 13) C)) := by
  rw [operatorJoin247_right]
  exact slot_commute ⟨slotRight (Fin 13) B, rfl⟩ ⟨C, rfl⟩

/-- The shared hinge contains a noncommuting pair. Overlapping pair algebras
therefore cannot be treated as disjoint regions. -/
theorem operatorJoin_hinge_noncommuting :
    ¬ Commute (operatorJoin86 (Matrix.single 0 1 1))
      (operatorJoin86 (Matrix.single 1 0 1)) := by
  intro h
  have he : operatorJoin86
      (Matrix.single 0 1 1 * Matrix.single 1 0 1) =
      operatorJoin86 (Matrix.single 1 0 1 * Matrix.single 0 1 1) := by
    simpa only [map_mul] using h.eq
  have he' := operatorJoin86_injective he
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at he'
  have hc := congrFun (congrFun he' 0) 0
  norm_num [Matrix.single] at hc

/-- The observable retraction uses normalized partial trace. The state
marginal, in contrast, uses the unnormalized partial trace. -/
theorem operatorJoin88_retraction (A : Matrix PairIndex PairIndex ℂ) :
    (13 : ℂ)⁻¹ • ptraceSnd (operatorJoin88 A) = A := by
  change (13 : ℂ)⁻¹ • ptraceSnd (A ⊗ₖ (1 : Matrix (Fin 13) (Fin 13) ℂ)) = A
  rw [ptraceSnd_slotLeft, smul_smul]
  norm_num

theorem operatorJoin247_retraction (A : Matrix PairIndex247 PairIndex247 ℂ) :
    (14 : ℂ)⁻¹ • ptraceMiddle (operatorJoin247 A) = A := by
  ext p p'
  simp [ptraceMiddle, Matrix.smul_apply, smul_eq_mul]

/-- The existing empirical triple state restricts to the counted 86/88
state through the new observable inclusion. -/
theorem operatorJoin88_counted_readout (A : Matrix PairIndex PairIndex ℂ) :
    (tripleCorrelationState * operatorJoin88 A).trace =
      (correlationState88 * A).trace := by
  simp only [tripleCorrelationState, correlationState88, Matrix.trace,
    Matrix.diag, Matrix.diagonal_mul, operatorJoin88_apply, ite_eq_left, mul_one]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  simp only
  rw [← Finset.sum_mul, ← Finset.sum_div]
  congr 2
  exact_mod_cast tripleCount_marginal_88 p

/-- The existing empirical triple state restricts to the counted 86/247
state. This is not an equality with either uniform tower state. -/
theorem operatorJoin247_counted_readout (A : Matrix PairIndex247 PairIndex247 ℂ) :
    (tripleCorrelationState * operatorJoin247 A).trace =
      (correlationState * A).trace := by
  simp only [tripleCorrelationState, correlationState, Matrix.trace,
    Matrix.diag, Matrix.diagonal_mul, operatorJoin247_apply, ite_eq_left, mul_one]
  rw [← Equiv.sum_comp middleTraceIndexEquiv]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  change (∑ j : Fin 14, (tripleCount ((p.1, j), p.2) : ℂ) / 32 * A p p) = _
  rw [← Finset.sum_mul, ← Finset.sum_div]
  congr 2
  exact_mod_cast tripleCount_marginal_247 p

/-- Observable inclusion intertwines each actual 86/88 transition. -/
theorem operatorJoin88_evolve (t : Fin 31) (A : Matrix PairIndex PairIndex ℂ) :
    tripleStepEvolve t (operatorJoin88 A) = operatorJoin88 (pair88StepEvolve t A) := by
  ext q r
  simp [tripleStepEvolve, pair88StepEvolve,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    tripleStepEquiv, Equiv.prodCongr_symm]

/-- Observable inclusion intertwines each actual 86/247 transition. -/
theorem operatorJoin247_evolve (t : Fin 31)
    (A : Matrix PairIndex247 PairIndex247 ℂ) :
    tripleStepEvolve t (operatorJoin247 A) =
      operatorJoin247 (stepEvolve t.castSucc A) := by
  ext q r
  simp [tripleStepEvolve, stepEvolve,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    tripleStepEquiv, walkStepEquiv88, walkStepEquiv, Equiv.prodCongr_symm]

/-- Generation is preserved when two source-generated factors are assembled
by the declared tensor embeddings. -/
theorem operatorJoin_pair_generation {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (S : Set (Matrix α α ℂ)) (T : Set (Matrix β β ℂ))
    (hS : StarAlgebra.adjoin ℂ S = ⊤) (hT : StarAlgebra.adjoin ℂ T = ⊤) :
    StarAlgebra.adjoin ℂ ((slotLeft β '' S) ∪ (slotRight α '' T)) = ⊤ := by
  apply top_unique
  rw [← slot_ranges_generate_top (α := α) (β := β)]
  apply StarAlgebra.adjoin_le
  intro X hX
  rcases hX with hX | hX
  · have hle : (slotLeft β (α := α)).range ≤
        StarAlgebra.adjoin ℂ ((slotLeft β '' S) ∪ (slotRight α '' T)) := by
      rw [StarAlgHom.range_eq_map_top, ← hS, StarAlgHom.map_adjoin]
      exact StarAlgebra.adjoin_mono Set.subset_union_left
    exact hle hX
  · have hle : (slotRight α (β := β)).range ≤
        StarAlgebra.adjoin ℂ ((slotLeft β '' S) ∪ (slotRight α '' T)) := by
      rw [StarAlgHom.range_eq_map_top, ← hT, StarAlgHom.map_adjoin]
      exact StarAlgebra.adjoin_mono Set.subset_union_right
    exact hle hX

def operatorJoinSource88 : Set (Matrix PairIndex PairIndex ℂ) :=
  (slotLeft (Fin 14) '' obs86.generators) ∪
    (slotRight (Fin 13) '' obs88.generators)

def operatorJoinSource247 : Set (Matrix PairIndex247 PairIndex247 ℂ) :=
  (slotLeft (Fin 13) '' obs86.generators) ∪
    (slotRight (Fin 13) '' obs247.generators)

theorem operatorJoinSource88_generates :
    StarAlgebra.adjoin ℂ operatorJoinSource88 = ⊤ :=
  operatorJoin_pair_generation _ _ obs86_sourceAlgebra_eq_top obs88_sourceAlgebra_eq_top

theorem operatorJoinSource247_generates :
    StarAlgebra.adjoin ℂ operatorJoinSource247 = ⊤ :=
  operatorJoin_pair_generation _ _ obs86_sourceAlgebra_eq_top obs247_sourceAlgebra_eq_top

/-- The admitted family consists of the actual source transition operators
and field projectors, transported through both pair embeddings. -/
def operatorJoinAdmitted : Set (Matrix TripleCarrier TripleCarrier ℂ) :=
  (operatorJoin88 '' operatorJoinSource88) ∪
    (operatorJoin247 '' operatorJoinSource247)

theorem operatorJoinAdmitted_generates :
    StarAlgebra.adjoin ℂ operatorJoinAdmitted = ⊤ := by
  apply top_unique
  rw [← operatorJoin_generate_top]
  apply StarAlgebra.adjoin_le
  intro X hX
  rcases hX with hX | hX
  · have hle : operatorJoin88.range ≤ StarAlgebra.adjoin ℂ operatorJoinAdmitted := by
      rw [StarAlgHom.range_eq_map_top, ← operatorJoinSource88_generates,
        StarAlgHom.map_adjoin]
      exact StarAlgebra.adjoin_mono Set.subset_union_left
    exact hle hX
  · have hle : operatorJoin247.range ≤ StarAlgebra.adjoin ℂ operatorJoinAdmitted := by
      rw [StarAlgHom.range_eq_map_top, ← operatorJoinSource247_generates,
        StarAlgHom.map_adjoin]
      exact StarAlgebra.adjoin_mono Set.subset_union_right
    exact hle hX

/-- Evolved source generators generate the full joint operator algebra.
This is a finite algebraic statement, not a Cauchy-surface interpretation. -/
theorem operatorJoinAdmitted_evolved (t : Fin 31) :
    StarAlgebra.adjoin ℂ
      ((tripleStepEvolve t).toStarAlgHom '' operatorJoinAdmitted) = ⊤ := by
  rw [← StarAlgHom.map_adjoin, operatorJoinAdmitted_generates,
    ← StarAlgHom.range_eq_map_top]
  rw [StarSubalgebra.eq_top_iff]
  intro X
  exact ⟨(tripleStepEvolve t).symm X, (tripleStepEvolve t).apply_symm_apply X⟩

end
end OPH.QFT

#print axioms OPH.QFT.operatorJoin_intersection
#print axioms OPH.QFT.operatorJoin_generate_top
#print axioms OPH.QFT.operatorJoin_spectator_locality
#print axioms OPH.QFT.operatorJoin88_evolve
#print axioms OPH.QFT.operatorJoin247_evolve
#print axioms OPH.QFT.operatorJoin_hinge_noncommuting
#print axioms OPH.QFT.operatorJoin88_counted_readout
#print axioms OPH.QFT.operatorJoin247_counted_readout
#print axioms OPH.QFT.operatorJoinAdmitted_evolved

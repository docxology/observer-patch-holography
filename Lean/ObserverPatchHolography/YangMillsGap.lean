module
public import Mathlib
public import ObserverPatchHolography.YangMillsLemma72
public import ObserverPatchHolography.YangMillsProp81

@[expose] public section

/-!
# Yang–Mills finite repair-gap: the commuting-projection branch

This module carries one conditional result of B. Müller, *Explaining the
Yang–Mills Mass Gap with Observer-Patch Repair Dynamics*: a finite-gap
assembly for a family of pairwise commuting orthogonal projections.  It is
**not** a formalisation of the paper's noncommuting finite-stage theorem,
whose collar conditional expectations need not commute and whose gap argument
uses a Dobrushin/approximate-tensorisation hypothesis instead.

## Scope (read this first)

This module proves an **implication**, nothing more:

> IF the repair generator on a finite collar family has the special structural
> form assumed here, with each collar acting by an orthogonal projection
> `E_C`, the collars **mutually commuting**, their joint fixed space
> represented by `P₀`, and **finitely many** active collar types each carrying
> a **strictly positive** relaxation rate `c_C` (supplied directly to the
> theorem below), THEN the finite generator `L_r^rep = ∑_C c_C · (I − E_C)`
> dominates `c_* · (I − P₀)` with `c_* = min_C c_C > 0` (Proposition 8.1): a
> strictly positive finite-stage spectral gap.

Everything to the left of `THEN` is a **hypothesis** here.  In particular,
pairwise commutation is not derived from the Yang–Mills construction and is
discharged **nowhere** in Lean.  This file proves only the special
implication `commuting structure ⇒ finite gap`.

The result must not be substituted for, or described as, the paper's
noncommuting Dobrushin finite-stage theorem.  Nor can it be composed into the
continuum receipt merely because both conclusions are called a finite gap:
doing so would require a separate source-level proof that the collar
expectations commute and that this commuting branch satisfies the continuum
certificate's compatibility hypotheses.  No such bridge is present here.

One thing is deliberately **NOT** proved and **NOT** claimed:

* `Δ_YM = Δ_rep`. This is Müller's **Assumption 9.2**, the continuum
  certificate (Schwinger-function convergence, reflection positivity,
  Osterwalder–Schrader reconstruction, non-triviality). It is the genuine open
  problem and is **untouched**. The deliverable here is `Δ_rep`, the
  finite-stage *representation* gap, and **not** the physical Yang–Mills mass
  gap.

Two ingredients are proved in sibling modules and **imported** here, and they
carry different status in this API:

* `lemma_7_2`: scalar relaxation on one uniform hidden fiber, proved in
  `ObserverPatchHolography.YangMillsLemma72`.  It is re-exported here as a
  separate conditional theorem, and as `collar_rate_unique` in the sharper
  unique-scalar form, while no theorem in this module bridges its matrix `D`
  and coefficient `c_F` to the Hilbert-space collar projections and `rate`
  argument of `thm_7_3_finite_gap`;
* `prop_8_1`: the commuting-color finite-stage gap (`commuting ⇒ gap`), proved
  in `ObserverPatchHolography.YangMillsProp81`.

This file is the **setup plus the Theorem 7.3 / Lemma 7.4 assembly**.
`thm_7_3_finite_gap` assembles the directly assumed positive rates with the
uniform floor and `prop_8_1`; it carries zero `sorry`s and no project-level
axioms.  It does **not** consume `lemma_7_2`.  A source theorem connecting the
uniform-fiber relaxation data to the collar-rate argument is a separate bridge
obligation.  The conditional continuum chain lives in the sibling
`ObserverPatchHolography.RepairGapChain`.

SCOPE: machine-checked only on the special pairwise-commuting branch: the
finite representation-gap implication `Δ_rep ≥ c_* > 0` from directly
assumed positive collar rates (Lemma 7.4 / Prop 8.1 / Thm 7.3 assembly), plus
the separate conditional Lemma 7.2 and its unique-scalar sharpening.  No
composition from Lemma 7.2 into the rate premise is formalized.  This is
neither the paper's noncommuting finite-stage theorem nor a proof of any
continuum-certificate premise.
-/

namespace ObserverPatchHolography.YangMillsGap

/-! ## §7.2 keystone: the imported statement (uniform hidden fiber) -/

/-- `E_F`, the expectation onto the constants of a uniform hidden fiber `F`,
    realised as the matrix `|F|⁻¹ · J` where `J` is the all-ones matrix. -/
noncomputable def EF (F : Type*) [Fintype F] : Matrix F F ℝ :=
  (Fintype.card F : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))

/-- **Lemma 7.2 (imported keystone).** A positive-semidefinite relaxation `D` on
    a uniform hidden fiber `F` with `|F| ≥ 2`, commuting with the full symmetric
    group `S_F` (every permutation matrix) and with kernel exactly the constants,
    is a *strictly positive scalar* multiple of `I − E_F`.

    Proved in the sibling keystone module `YangMillsLemma72` via the commutant
    of the permutation representation (`commutant_perm_two_valued` + Schur on
    the standard rep); discharged here by direct import, since this file is the
    assembly rather than the keystone. (The two `EF` definitions are token-identical,
    hence definitionally equal.) -/
theorem lemma_7_2 {F : Type*} [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (D : Matrix F F ℝ)
    (hPSD : D.PosSemidef)
    (hComm : ∀ σ : Equiv.Perm F, Commute (σ.permMatrix ℝ) D)
    (hKer : ∀ v : F → ℝ, D.mulVec v = 0 ↔ ∃ c : ℝ, v = fun _ => c) :
    ∃ cF : ℝ, 0 < cF ∧ D = cF • ((1 : Matrix F F ℝ) - EF F) :=
  ObserverPatchHolography.YangMillsLemma72.lemma_7_2 hF D hPSD hComm hKer

/-- **Lemma 7.2, unique-scalar form.** Under the hypotheses of the imported
    keystone the relaxation rate is more than available: it is the *only*
    positive scalar with `D = cF • (I − E_F)`.

    Existence is `lemma_7_2`.  Uniqueness consumes `|F| ≥ 2`: that hypothesis
    supplies a pair `a ≠ b` of fiber points, and at such a pair the off-diagonal
    entry `(I − E_F) a b = −|F|⁻¹` is nonzero, so two scalars agreeing on
    `cF • (I − E_F)` agree at that entry and hence agree.  On a one-point fiber
    `I − E_F` vanishes and every positive scalar satisfies the equation, which is
    exactly what `|F| ≥ 2` excludes. -/
theorem collar_rate_unique {F : Type*} [Fintype F] [DecidableEq F]
    (hF : 2 ≤ Fintype.card F) (D : Matrix F F ℝ)
    (hPSD : D.PosSemidef)
    (hComm : ∀ σ : Equiv.Perm F, Commute (σ.permMatrix ℝ) D)
    (hKer : ∀ v : F → ℝ, D.mulVec v = 0 ↔ ∃ c : ℝ, v = fun _ => c) :
    ∃! cF : ℝ, 0 < cF ∧ D = cF • ((1 : Matrix F F ℝ) - EF F) := by
  obtain ⟨cF, hcF_pos, hcF_eq⟩ := lemma_7_2 hF D hPSD hComm hKer
  -- `|F| ≥ 2` supplies two distinct fiber points.
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card F)
  have hcard_pos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have h : 0 < Fintype.card F := by omega
    exact_mod_cast h
  have hEF : EF F a b = ((Fintype.card F : ℝ))⁻¹ := by
    simp [EF]
  -- The off-diagonal entry of `I − E_F` is `−|F|⁻¹`, hence nonzero.
  have hMab : ((1 : Matrix F F ℝ) - EF F) a b ≠ 0 := by
    rw [Matrix.sub_apply, Matrix.one_apply_ne hab, hEF, zero_sub, neg_ne_zero]
    exact inv_ne_zero hcard_pos.ne'
  refine ⟨cF, ⟨hcF_pos, hcF_eq⟩, ?_⟩
  rintro c ⟨-, hc⟩
  have hsub : (c - cF) • ((1 : Matrix F F ℝ) - EF F) = 0 := by
    rw [sub_smul, ← hc, ← hcF_eq, sub_self]
  have hentry := congrFun (congrFun hsub a) b
  rw [Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hentry
  have hzero := (mul_eq_zero.mp hentry).resolve_right hMab
  linarith

/-! ## Operator setup: a real Hilbert space

(The paper's application is finite-dimensional, whence complete; only
completeness is consumed by the Loewner/positivity machinery, so we
hypothesize exactly that, and the finite-dimensional case is an instance.) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **The repair generator** `L_r^rep = ∑_{C ∈ s} c_C · (I − E_C)` over a finite
    active-collar index set `s`, with per-collar orthogonal projections `Ec` and
    relaxation rates `rate`. -/
noncomputable def repairGenerator {ι : Type*} (s : Finset ι)
    (Ec : ι → (E →L[ℝ] E)) (rate : ι → ℝ) : E →L[ℝ] E :=
  ∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a)

/-! ## §8.1 gap engine: the imported commuting-projection statement -/

/-- **Proposition 8.1 (imported).** For a finite family of **mutually commuting**
    orthogonal (star) projections `Ec` whose non-commutative product equals the
    joint projection `P₀`, the constant-rate generator
    `∑ c_* · (I − E_C)` dominates `c_* · (I − P₀)`.  The signature does not
    identify the joint fixed range with a physical constants sector.

    Proved in the sibling gap module `YangMillsProp81` via `1 − ∏ Eₐ ≤ ∑ (1 − Eₐ)`
    for a commuting family of star projections; discharged here by direct
    import. -/
theorem prop_8_1 {ι : Type*} (s : Finset ι) (Ec : ι → (E →L[ℝ] E)) (P0 : E →L[ℝ] E)
    (hE : ∀ a ∈ s, IsStarProjection (Ec a))
    (hc : (↑s : Set ι).Pairwise (Function.onFun Commute Ec))
    (hprod : s.noncommProd Ec hc = P0)
    {cstar : ℝ} (hcpos : 0 < cstar) :
    cstar • ((1 : E →L[ℝ] E) - P0) ≤ ∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a) :=
  ObserverPatchHolography.YangMillsProp81.prop_8_1 s Ec P0 hE hc hprod hcpos

/-! ## §7.4 uniform floor -/

/-- **Lemma 7.4 (uniform floor).** Finitely many strictly positive relaxation
    rates over a nonempty active-collar set have a strictly positive minimum
    `c_*` that bounds them all from below. -/
theorem uniform_floor {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (rate : ι → ℝ)
    (hpos : ∀ a ∈ s, 0 < rate a) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ a ∈ s, cstar ≤ rate a := by
  obtain ⟨a₀, ha₀, hmin⟩ := s.exists_min_image rate hne
  exact ⟨rate a₀, hpos a₀ ha₀, hmin⟩

/-! ## §7.3 assembly: the special commuting finite-gap deliverable -/

/-- **Theorem 7.3 / 7.4 (commuting finite representation gap).** Assume
    each collar rate satisfies `rate a > 0`, then combine Proposition 8.1
    (commuting colors ⇒ constant-rate gap) with the uniform floor (Lemma 7.4):
    the repair generator dominates `c_* · (I − P₀)` with `c_* > 0`.

    The positive-rate premise is an explicit theorem argument.  Although the
    separate `lemma_7_2` can produce a positive scalar for one uniform-fiber
    matrix relaxation, this theorem contains no bridge from that matrix datum
    to `Ec` or `rate` and does not consume `lemma_7_2`.

    This is `Δ_rep ≥ c_* > 0` only on the special pairwise-commuting branch.
    It is not the paper's noncommuting Dobrushin theorem and supplies no
    premise of the continuum receipt without an additional compatibility
    proof.  It says nothing about `Δ_YM`; the continuum bridge
    is not stated, assumed, or proved here.

    Proof shape: `c_* · (I − P₀) ≤ ∑ c_* · (I − E_C) ≤ ∑ c_C · (I − E_C)`, where
    the first `≤` is Prop 8.1 and the second is rate-monotonicity: each summand
    grows because `c_C ≥ c_*` (uniform floor) and `I − E_C ⪰ 0` (star
    projection), so the difference is a sum of positive operators. -/
theorem thm_7_3_finite_gap {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (Ec : ι → (E →L[ℝ] E)) (P0 : E →L[ℝ] E)
    (hE : ∀ a ∈ s, IsStarProjection (Ec a))
    (hc : (↑s : Set ι).Pairwise (Function.onFun Commute Ec))
    (hprod : s.noncommProd Ec hc = P0)
    (rate : ι → ℝ) (hrate : ∀ a ∈ s, 0 < rate a) :
    ∃ cstar : ℝ, 0 < cstar ∧
      cstar • ((1 : E →L[ℝ] E) - P0) ≤ repairGenerator s Ec rate := by
  -- Lemma 7.4: a strictly positive uniform floor c_* = min_C c_C.
  obtain ⟨cstar, hcstar_pos, hfloor⟩ := uniform_floor s hne rate hrate
  refine ⟨cstar, hcstar_pos, ?_⟩
  -- Step 1 (Prop 8.1): the constant-rate gap  c_* (I − P₀) ≤ ∑ c_* (I − E_C).
  have step1 :
      cstar • ((1 : E →L[ℝ] E) - P0) ≤ ∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a) :=
    prop_8_1 s Ec P0 hE hc hprod hcstar_pos
  -- Step 2: actual rates dominate the floor rate collar-by-collar.
  have step2 :
      (∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a))
        ≤ ∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a) := by
    have hdiff :
        (∑ a ∈ s, (rate a - cstar) • ((1 : E →L[ℝ] E) - Ec a))
          = (∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a))
              - ∑ a ∈ s, cstar • ((1 : E →L[ℝ] E) - Ec a) := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    refine ContinuousLinearMap.le_def.mpr ?_
    rw [← hdiff]
    refine ContinuousLinearMap.isPositive_sum s (fun a ha => ?_)
    exact ContinuousLinearMap.IsPositive.smul_of_nonneg
      (ContinuousLinearMap.IsPositive.of_isStarProjection (hE a ha).one_sub)
      (sub_nonneg.mpr (hfloor a ha))
  -- Assemble: c_* (I − P₀) ≤ ∑ c_* (I − E_C) ≤ ∑ c_C (I − E_C) = L_r^rep.
  show cstar • ((1 : E →L[ℝ] E) - P0) ≤ ∑ a ∈ s, rate a • ((1 : E →L[ℝ] E) - Ec a)
  exact le_trans step1 step2

/-! ## Axiom self-audit (build-log visible)

Expected report for every theorem below: exactly
`[propext, Classical.choice, Quot.sound]`, the three standard Mathlib axioms:
no `sorryAx`, no project-level axiom. -/

#print axioms lemma_7_2
#print axioms collar_rate_unique
#print axioms prop_8_1
#print axioms uniform_floor
#print axioms thm_7_3_finite_gap

end ObserverPatchHolography.YangMillsGap

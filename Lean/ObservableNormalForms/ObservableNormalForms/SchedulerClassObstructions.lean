module
public import ObservableNormalForms.Examples.ProtectedObstructions

@[expose] public section

/-!
# Declared admissible scheduler class and capacity-split obstruction bounds

This module declares one typed admissible scheduler class on the committed
two-register repair carrier `TwoBitRepair.State` and proves the first
scheduler-quantified obstruction bounds for it.

Claim. On the carrier `Bool x Bool`, with the first register read as the
shared network-facing record (the protected observation of the committed
two-bit repair system) and the second register read as the private local
defect flag, the class `AdmissibleScheduler` collects every finite Markov
scheduler whose supported steps do not increase the declared defect mismatch,
write at most one register, and spend at most one unit of expected capacity
per step.  Inside the class the self-update-only sub-class fixes the shared
register on every supported step and the network-update-only sub-class fixes
the private register.  The module proves: both sub-classes are inhabited by
schedulers built from committed fixture kernels; the defective fiber is
unreachable from every consistent state under every scheduler in the class;
the cross fiber (shared register flipped) is unreachable under every
self-update-only scheduler yet is hit with probability one by an explicit
network-update-only scheduler, so any in-class scheduler with a positive
cross hit spends shared capacity on some supported step; the almost-sure
hitting hypothesis of the committed fine fixture is discharged by the
committed repair kernel and refuted by an explicit in-class counterexample
scheduler.

On the committed coarse fixture, whose target admits both shared values from
two declared sources, the module proves the endpoint-uniqueness cut at class
strength: no self-update-only scheduler places the coarse behavior in layer
3, no network-update-only scheduler hits the coarse target from a raised
flag, an explicit merge-then-clear class member outside both sub-classes
places the coarse behavior in layer 3, and every in-class scheduler that
does so spends both shared and private capacity on supported steps.  On the
fine fixture layer 2 equals layer 3 under every scheduler in the class.

Hypotheses.  The class constraints (mismatch non-increase, single-register
locality, unit expected capacity) and the capacity-split reading of the two
registers are architecture declarations, stated as separate named clauses of
one structure.  Every theorem is quantified exactly as written:
all-schedulers-in-class, all-schedulers-in-sub-class, or this-scheduler.

Falsifier.  Any of: an in-class scheduler with a positive defect hit from a
consistent state; a self-update-only scheduler with a positive cross hit; a
proof that the explicit network-update-only scheduler misses the cross fiber;
an in-class scheduler with positive cross hit and zero shared cost on every
supported step; failure of the committed repair kernel to satisfy the class
constraints; a self-update-only scheduler placing the coarse behavior in
layer 3; a network-update-only scheduler with a positive coarse hit from a
raised flag; failure of the merge-then-clear scheduler to satisfy the class
constraints or to place the coarse behavior in layer 3; an in-class
scheduler placing the coarse behavior in layer 3 with zero shared cost or
zero private cost on every supported step.

Nonclaims.  No physical scheduler is selected; the class is a declaration,
not a derivation.  No biological, cognitive, or behavioral claim is made.
All results are on the finite fixtures of the committed development.  The
mismatch, locality, and capacity clauses coincide extensionally with simple
register conditions on this two-register carrier; no generality beyond the
declared carrier is claimed.
-/

namespace ObservableNormalForms.ProtectedObstructions.SchedulerClass

open scoped BigOperators
open ObservableNormalForms
open ObservableNormalForms.ProtectedObstructions
open ObservableNormalForms.ProtectedObstructions.NonidentityExactness
open ObservableNormalForms.ProtectedObstructions.PublicAdapter
open ObservableNormalForms.ProtectedObstructions.PublicAdapter.NativeTwoBitC4

noncomputable section

/-- The committed two-register repair carrier.  The first register is the
shared network-facing record (the protected observation of
`TwoBitRepair.observe`); the second register is the private local defect
flag.  This reading is the declared capacity split, not a derived fact. -/
abbrev State := TwoBitRepair.State

/-- Declared defect mismatch: one unit per raised private defect flag. -/
def mismatch (q : State) : ℝ := if q.2 = true then 1 else 0

theorem mismatch_nonneg (q : State) : 0 ≤ mismatch q := by
  unfold mismatch
  split <;> norm_num

/-- Private capacity cost of one step: one unit per private-register write.
A self-update spends exactly this cost. -/
def privateCost (q r : State) : ℝ := if r.2 = q.2 then 0 else 1

/-- Shared capacity cost of one step: one unit per shared-register write.
A network update spends exactly this cost. -/
def sharedCost (q r : State) : ℝ := if r.1 = q.1 then 0 else 1

/-- Total declared capacity cost of one step. -/
def stepCost (q r : State) : ℝ := privateCost q r + sharedCost q r

/-- Declared local move grammar: one step writes at most one register. -/
def LocalMove (q r : State) : Prop := r.1 = q.1 ∨ r.2 = q.2

/-- The declared admissible scheduler class.  A scheduler is a committed
finite Markov kernel on the two-register carrier; the three defining
constraints are separate named clauses.  `mismatch_nonincrease` forbids
supported steps that raise the defect mismatch, `locality` restricts
supported steps to the declared single-register move grammar, and
`capacity_bound` caps the expected declared capacity spend of every step at
one unit. -/
structure AdmissibleScheduler where
  kernel : FiniteMarkovKernel State
  mismatch_nonincrease : ∀ q r : State,
    SupportStep kernel q r → mismatch r ≤ mismatch q
  locality : ∀ q r : State, SupportStep kernel q r → LocalMove q r
  capacity_bound : ∀ q : State,
    (∑ r : State, kernel.probability q r * stepCost q r) ≤ 1

/-- Self-update-only sub-class: every supported step fixes the shared
register, so the observer moves only its private state. -/
def SelfUpdateOnly (A : AdmissibleScheduler) : Prop :=
  ∀ q r : State, SupportStep A.kernel q r → r.1 = q.1

/-- Network-update-only sub-class: every supported step fixes the private
register, so all motion is spent into the shared record. -/
def NetworkUpdateOnly (A : AdmissibleScheduler) : Prop :=
  ∀ q r : State, SupportStep A.kernel q r → r.2 = q.2

/-- The self-update-only sub-class is exactly the zero-shared-spend locus. -/
theorem selfUpdateOnly_iff_no_shared_spend (A : AdmissibleScheduler) :
    SelfUpdateOnly A ↔
      ∀ q r : State, SupportStep A.kernel q r → sharedCost q r = 0 := by
  constructor
  · intro h q r hqr
    simp [sharedCost, h q r hqr]
  · intro h q r hqr
    have hzero := h q r hqr
    by_contra hne
    norm_num [sharedCost, hne] at hzero

/-- The network-update-only sub-class is exactly the zero-private-spend
locus. -/
theorem networkUpdateOnly_iff_no_private_spend (A : AdmissibleScheduler) :
    NetworkUpdateOnly A ↔
      ∀ q r : State, SupportStep A.kernel q r → privateCost q r = 0 := by
  constructor
  · intro h q r hqr
    simp [privateCost, h q r hqr]
  · intro h q r hqr
    have hzero := h q r hqr
    by_contra hne
    norm_num [privateCost, hne] at hzero

/-- Self-update-only supported steps preserve the committed protected
observation, connecting the sub-class to the committed exact-rewriting
interface. -/
theorem selfUpdateOnly_support_observationPreserving (A : AdmissibleScheduler)
    (hA : SelfUpdateOnly A) :
    ObservableNormalForms.ObservationPreserving
      (fun q r : State => SupportStep A.kernel q r) TwoBitRepair.observe := by
  intro q r hqr
  exact (hA q r hqr).symm

/-! ## Support characterizations of the three witness kernels -/

theorem repairKernel_support {q r : State}
    (h : SupportStep TwoBit.kernel q r) : r = (q.1, false) := by
  by_contra hne
  simp [SupportStep, TwoBit.kernel, hne] at h

/-- Deterministic shared-register swap: the network record flips toward the
opposite consensus value while the private register is untouched. -/
def networkSwapKernel : FiniteMarkovKernel State where
  probability q r := if r = (!q.1, q.2) then 1 else 0
  probability_nonneg := by
    intro q r
    split <;> norm_num
  probability_sum_one := by
    intro q
    simp

theorem networkSwapKernel_support {q r : State}
    (h : SupportStep networkSwapKernel q r) : r = (!q.1, q.2) := by
  by_contra hne
  simp [SupportStep, networkSwapKernel, hne] at h

/-- The committed identity kernel on the two-register carrier, reused from
the committed strict-reversal fixture. -/
def stutterKernel : FiniteMarkovKernel State :=
  PublicAdapter.GenericCompletion.StrictReversal.identityKernel

theorem stutterKernel_support {q r : State}
    (h : SupportStep stutterKernel q r) : r = q := by
  by_contra hne
  simp [SupportStep, stutterKernel,
    PublicAdapter.GenericCompletion.StrictReversal.identityKernel, hne] at h

/-! ## Nonvacuity: explicit class members from committed fixture kernels -/

/-- The committed two-bit repair kernel as a class member.  Its supported
steps clear the private defect flag and fix the shared register. -/
def repairScheduler : AdmissibleScheduler where
  kernel := TwoBit.kernel
  mismatch_nonincrease := by
    intro q r hqr
    rw [repairKernel_support hqr]
    have hzero : mismatch (q.1, false) = 0 := by simp [mismatch]
    rw [hzero]
    exact mismatch_nonneg q
  locality := by
    intro q r hqr
    exact Or.inl (by rw [repairKernel_support hqr])
  capacity_bound := by
    intro q
    rw [Finset.sum_eq_single ((q.1, false) : State)]
    · rcases q with ⟨b, d⟩
      cases d <;> norm_num [TwoBit.kernel, stepCost, privateCost, sharedCost]
    · intro r _ hr
      simp [TwoBit.kernel, hr]
    · simp

/-- The shared-register swap as a class member. -/
def networkSwapScheduler : AdmissibleScheduler where
  kernel := networkSwapKernel
  mismatch_nonincrease := by
    intro q r hqr
    rw [networkSwapKernel_support hqr]
    simp [mismatch]
  locality := by
    intro q r hqr
    exact Or.inr (by rw [networkSwapKernel_support hqr])
  capacity_bound := by
    intro q
    rw [Finset.sum_eq_single (((!q.1, q.2)) : State)]
    · rcases q with ⟨b, d⟩
      cases b <;> norm_num [networkSwapKernel, stepCost, privateCost, sharedCost]
    · intro r _ hr
      simp [networkSwapKernel, hr]
    · simp

/-- The committed identity kernel as a class member. -/
def stutterScheduler : AdmissibleScheduler where
  kernel := stutterKernel
  mismatch_nonincrease := by
    intro q r hqr
    rw [stutterKernel_support hqr]
  locality := by
    intro q r hqr
    exact Or.inl (by rw [stutterKernel_support hqr])
  capacity_bound := by
    intro q
    rw [Finset.sum_eq_single (q : State)]
    · norm_num [stutterKernel,
        PublicAdapter.GenericCompletion.StrictReversal.identityKernel,
        stepCost, privateCost, sharedCost]
    · intro r _ hr
      simp [stutterKernel,
        PublicAdapter.GenericCompletion.StrictReversal.identityKernel, hr]
    · simp

/-- Sub-class nonvacuity, self-update side: the committed repair kernel is a
self-update-only class member. -/
theorem repairScheduler_selfUpdateOnly : SelfUpdateOnly repairScheduler := by
  intro q r hqr
  rw [repairKernel_support hqr]

/-- Sub-class nonvacuity, network side: the shared-register swap is a
network-update-only class member. -/
theorem networkSwapScheduler_networkUpdateOnly :
    NetworkUpdateOnly networkSwapScheduler := by
  intro q r hqr
  rw [networkSwapKernel_support hqr]

/-- The two sub-classes are distinct on their witnesses: the swap scheduler
spends shared capacity on a supported step. -/
theorem networkSwapScheduler_not_selfUpdateOnly :
    ¬ SelfUpdateOnly networkSwapScheduler := by
  intro h
  have hstep : SupportStep networkSwapKernel ((false, false) : State)
      ((true, false) : State) := by
    norm_num [SupportStep, networkSwapKernel]
  have := h (false, false) (true, false) hstep
  simp at this

/-! ## All-scheduler obstruction: the defect fiber is protected by the class -/

/-- Target fiber of the defective states. -/
def DefectTarget (q : State) : Prop := q.2 = true

instance : DecidablePred DefectTarget :=
  fun q => inferInstanceAs (Decidable (q.2 = true))

/-- All-scheduler obstruction cut.  From every consistent state (private
defect flag cleared) the defective fiber has hit probability zero under
every scheduler in the declared class.  Only the `mismatch_nonincrease`
clause is consumed. -/
theorem all_scheduler_defect_cut (A : AdmissibleScheduler) :
    ∀ q : State, q.2 = false →
      hitProbability A.kernel DefectTarget q = 0 := by
  intro q hq
  apply hitProbability_eq_zero_on_closed A.kernel DefectTarget
    {r : State | r.2 = false}
  · intro u hu ht
    rw [Set.mem_ofPred_eq] at hu
    have ht' : u.2 = true := ht
    rw [hu] at ht'
    exact Bool.false_ne_true ht'
  · intro u hu v huv
    rw [Set.mem_ofPred_eq] at hu ⊢
    have hm := A.mismatch_nonincrease u v huv
    by_contra hv
    have hv' : v.2 = true := by simpa using hv
    have h1 : mismatch v = 1 := by simp [mismatch, hv']
    have h0 : mismatch u = 0 := by simp [mismatch, hu]
    rw [h1, h0] at hm
    norm_num at hm
  · exact hq

/-- Escape control outside the class: a defect-injecting kernel violates the
mismatch clause and hits the defective fiber with probability one, so the
all-scheduler cut is enforced by the declared class and not by the carrier. -/
def defectInjectionKernel : FiniteMarkovKernel State where
  probability q r := if r = (q.1, true) then 1 else 0
  probability_nonneg := by
    intro q r
    split <;> norm_num
  probability_sum_one := by
    intro q
    simp

theorem defectInjectionKernel_violates_mismatch :
    ¬ ∀ q r : State, SupportStep defectInjectionKernel q r →
      mismatch r ≤ mismatch q := by
  intro h
  have hstep : SupportStep defectInjectionKernel ((false, false) : State)
      ((false, true) : State) := by
    norm_num [SupportStep, defectInjectionKernel]
  have := h (false, false) (false, true) hstep
  norm_num [mismatch] at this

theorem defectInjectionKernel_defect_hitBy (q : State) (hq : q.2 = false) :
    hitBy defectInjectionKernel DefectTarget 1 q = 1 := by
  rw [hitBy_succ_recurrence, ite_eq_right (by simp [DefectTarget, hq])]
  rw [Finset.sum_eq_single ((q.1, true) : State)]
  · rw [hitBy_zero, ite_eq_left (show DefectTarget (q.1, true) from rfl), mul_one]
    simp [defectInjectionKernel]
  · intro r _ hr
    simp [defectInjectionKernel, hr]
  · simp

theorem defectInjectionKernel_defect_hit (q : State) (hq : q.2 = false) :
    hitProbability defectInjectionKernel DefectTarget q = 1 := by
  apply le_antisymm (hitProbability_le_one defectInjectionKernel DefectTarget q)
  calc (1 : ℝ) = hitBy defectInjectionKernel DefectTarget 1 q :=
        (defectInjectionKernel_defect_hitBy q hq).symm
    _ ≤ hitProbability defectInjectionKernel DefectTarget q :=
        hitBy_le_hitProbability defectInjectionKernel DefectTarget 1 q

/-! ## Sub-class separation: the cross fiber prices shared capacity -/

/-- Target fiber of the states whose shared register reads `b`. -/
def CrossTarget (b : Bool) (q : State) : Prop := q.1 = b

instance (b : Bool) : DecidablePred (CrossTarget b) :=
  fun q => inferInstanceAs (Decidable (q.1 = b))

/-- Sub-class obstruction: every self-update-only scheduler misses the cross
fiber from every state whose shared register reads the opposite value. -/
theorem selfUpdateOnly_cross_cut (A : AdmissibleScheduler)
    (hA : SelfUpdateOnly A) (b : Bool) :
    ∀ q : State, q.1 = !b →
      hitProbability A.kernel (CrossTarget b) q = 0 := by
  intro q hq
  apply hitProbability_eq_zero_on_closed A.kernel (CrossTarget b)
    {r : State | r.1 = !b}
  · intro u hu ht
    rw [Set.mem_ofPred_eq] at hu
    have ht' : u.1 = b := ht
    rw [hu] at ht'
    cases b <;> simp at ht'
  · intro u hu v huv
    rw [Set.mem_ofPred_eq] at hu ⊢
    rw [hA u v huv, hu]
  · exact hq

theorem networkSwap_cross_hitBy (b : Bool) :
    hitBy networkSwapKernel (CrossTarget b) 1 ((!b, false) : State) = 1 := by
  rw [hitBy_succ_recurrence,
    ite_eq_right (show ¬ CrossTarget b ((!b, false) : State) by
      cases b <;> simp [CrossTarget])]
  rw [Finset.sum_eq_single (((b, false)) : State)]
  · rw [hitBy_zero, ite_eq_left (show CrossTarget b ((b, false) : State) from rfl),
      mul_one]
    simp [networkSwapKernel]
  · intro r _ hr
    simp only [networkSwapKernel, Bool.not_not]
    rw [ite_eq_right hr, zero_mul]
  · simp

/-- Full-class reachability witness: the network-update-only swap scheduler
hits the cross fiber with probability one. -/
theorem networkSwap_cross_hit (b : Bool) :
    hitProbability networkSwapKernel (CrossTarget b)
      ((!b, false) : State) = 1 := by
  apply le_antisymm
    (hitProbability_le_one networkSwapKernel (CrossTarget b) (!b, false))
  calc (1 : ℝ) = hitBy networkSwapKernel (CrossTarget b) 1 (!b, false) :=
        (networkSwap_cross_hitBy b).symm
    _ ≤ hitProbability networkSwapKernel (CrossTarget b) (!b, false) :=
        hitBy_le_hitProbability networkSwapKernel (CrossTarget b) 1 (!b, false)

/-- Capacity-split separation on the cross fiber: unreachable for every
self-update-only scheduler, hit with probability one by an explicit
network-update-only class member. -/
theorem capacity_split_separation (b : Bool) :
    (∀ A : AdmissibleScheduler, SelfUpdateOnly A →
      hitProbability A.kernel (CrossTarget b) ((!b, false) : State) = 0) ∧
    (∃ A : AdmissibleScheduler, NetworkUpdateOnly A ∧
      hitProbability A.kernel (CrossTarget b) ((!b, false) : State) = 1) := by
  constructor
  · intro A hA
    exact selfUpdateOnly_cross_cut A hA b (!b, false) rfl
  · exact ⟨networkSwapScheduler, networkSwapScheduler_networkUpdateOnly,
      networkSwap_cross_hit b⟩

/-- Pricing corollary: any in-class scheduler with a positive cross hit from
the opposite shared value spends shared capacity on some supported step. -/
theorem cross_hit_requires_shared_spend (A : AdmissibleScheduler) (b : Bool)
    (hpos : 0 < hitProbability A.kernel (CrossTarget b)
      ((!b, false) : State)) :
    ∃ q r : State, SupportStep A.kernel q r ∧ sharedCost q r = 1 := by
  by_contra hnone
  push Not at hnone
  have hself : SelfUpdateOnly A := by
    intro q r hqr
    have hne := hnone q r hqr
    by_contra hne1
    exact hne (by simp [sharedCost, hne1])
  have hzero := selfUpdateOnly_cross_cut A hself b (!b, false) rfl
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-! ## Hypothesis discharge and in-class counterexample -/

/-- The committed fine fixture with the declared scheduler substituted. -/
def fineModelOf (A : AdmissibleScheduler) :
    FixedBehaviorModel Bool State :=
  { TwoBit.fineCore with kernel := A.kernel }

/-- Identity-kernel non-hitting on the two-register carrier, from the
committed closed-set theorem. -/
theorem stutter_unhit (target : State → Prop) [DecidablePred target]
    (q : State) (h : ¬ target q) :
    hitProbability stutterKernel target q = 0 := by
  apply hitProbability_eq_zero_on_closed stutterKernel target
    ({q} : Set State)
  · intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact h
  · intro u hu v huv
    rw [Set.mem_singleton_iff] at hu
    subst hu
    rw [Set.mem_singleton_iff]
    exact stutterKernel_support huv
  · exact rfl

/-- Discharge from the repair dynamics: the committed repair kernel forces
the almost-sure hitting hypothesis of the fine fixture. -/
theorem repairScheduler_discharges_almostSure (b : Bool) :
    (fineModelOf repairScheduler).AlmostSure b := by
  intro x hx
  have hx' : x = (b, true) := by
    simpa [fineModelOf, TwoBit.fineCore] using hx
  subst hx'
  exact TwoBit.fine_hit_one b

/-- In-class counterexample: the class constraints do not force the
almost-sure hitting hypothesis; the identity scheduler satisfies all three
clauses and misses the fine target from its declared active source. -/
theorem class_does_not_force_almostSure :
    ∃ A : AdmissibleScheduler, ¬ (fineModelOf A).AlmostSure true := by
  refine ⟨stutterScheduler, ?_⟩
  intro hAS
  have hmem : ((true, true) : State) ∈
      (fineModelOf stutterScheduler).initial true := by
    simp [fineModelOf, TwoBit.fineCore]
  have hone := hAS (true, true) hmem
  have hnt : ¬ (fineModelOf stutterScheduler).IsTarget true (true, true) := by
    simp [fineModelOf, TwoBit.fineCore, TwoBit.fineTarget,
      TwoBit.FineTargetPred, FixedBehaviorModel.IsTarget]
  have hzero := stutter_unhit
    ((fineModelOf stutterScheduler).IsTarget true) (true, true) hnt
  have hone' : hitProbability stutterKernel
      ((fineModelOf stutterScheduler).IsTarget true) (true, true) = 1 := hone
  rw [hone'] at hzero
  norm_num at hzero

/-! ## Endpoint-uniqueness cut: the coarse fixture prices both capacities -/

/-- The committed coarse fixture with the declared scheduler substituted. -/
def coarseModelOf (A : AdmissibleScheduler) :
    FixedBehaviorModel Unit State :=
  { TwoBit.coarseCore with kernel := A.kernel }

/-- The committed fine profile with the declared scheduler substituted.  The
static observation and rewrite data are unchanged; only the stochastic core
moves. -/
def fineProfileOf (A : AdmissibleScheduler) : Profile Bool State where
  core := fineModelOf A
  protected_nonempty := ⟨false, by simp [fineModelOf, TwoBit.fineCore]⟩
  observe := TwoBitRepair.observe
  consistent := fun q => q ∈ TwoBitRepair.consistent
  target_iff := by
    intro b q
    simp [fineModelOf, TwoBit.fineCore, TwoBit.fineTarget, TwoBit.FineTargetPred,
      FixedBehaviorModel.IsTarget, TwoBitRepair.consistent, TwoBitRepair.observe,
      and_comm]
  initial_observe := by
    intro b q hb hq
    have hq' : q = (b, true) := by
      simpa [fineModelOf, TwoBit.fineCore] using hq
    subst q
    rfl
  rewrite := TwoBitRepair.step
  rewrite_observe := TwoBitRepair.step_observationPreserving
  normal_iff_consistent := TwoBitRepair.step_completeFor_consistent

/-- The committed coarse profile with the declared scheduler substituted. -/
def coarseProfileOf (A : AdmissibleScheduler) : Profile Unit State where
  core := coarseModelOf A
  protected_nonempty := ⟨(), by simp [coarseModelOf, TwoBit.coarseCore]⟩
  observe := TwoBitRepair.coarseObserve
  consistent := fun q => q ∈ TwoBitRepair.consistent
  target_iff := by
    intro b q
    cases b
    cases q with
    | mk q1 q2 => cases q2 <;> simp [coarseModelOf, TwoBit.coarseCore, TwoBit.coarseTarget,
      TwoBit.CoarseTargetPred, FixedBehaviorModel.IsTarget,
      TwoBitRepair.consistent, TwoBitRepair.coarseObserve]
  initial_observe := by
    intro b q hb hq
    cases b
    rfl
  rewrite := TwoBitRepair.step
  rewrite_observe := by
    intro q r hqr
    rfl
  normal_iff_consistent := TwoBitRepair.step_completeFor_consistent

/-- A step-closed set absorbs every chain that starts inside it. -/
theorem reflTransGen_mem_of_closed {R : State → State → Prop} (U : Set State)
    (hclosed : ∀ u ∈ U, ∀ v, R u v → v ∈ U) {x y : State}
    (h : Relation.ReflTransGen R x y) (hx : x ∈ U) : y ∈ U := by
  induction h with
  | refl => exact hx
  | tail _ hstep ih => exact hclosed _ ih _ hstep

/-- Cut 3 collapses on the fine fixture for every scheduler in the class:
the target fiber is a singleton and the silent equivalence is equality, so
layer 2 and layer 3 coincide whatever the kernel. -/
theorem fine_layer2_eq_layer3_of_class (A : AdmissibleScheduler) :
    (fineProfileOf A).layer2 = (fineProfileOf A).layer3 := by
  apply (fineProfileOf A).t5_observableDetermination_collapse
  intro b c d hc hd
  have hc' : c.2 = false ∧ c.1 = b := by
    simp only [fineProfileOf, fineModelOf, TwoBit.fineCore, TwoBit.fineTarget,
      TwoBit.FineTargetPred, FixedBehaviorModel.IsTarget] at hc
    exact @of_decide_eq_true _ _ hc
  have hd' : d.2 = false ∧ d.1 = b := by
    simp only [fineProfileOf, fineModelOf, TwoBit.fineCore, TwoBit.fineTarget,
      TwoBit.FineTargetPred, FixedBehaviorModel.IsTarget] at hd
    exact @of_decide_eq_true _ _ hd
  change c = d
  apply Prod.ext
  · exact hc'.2.trans hd'.2.symm
  · exact hc'.1.trans hd'.1.symm

/-- Under a self-update-only scheduler every positive coarse endpoint keeps
the shared register of its source. -/
theorem selfUpdateOnly_coarse_endpoint_shared (A : AdmissibleScheduler)
    (hA : SelfUpdateOnly A) {x c : State}
    (hpos : 0 < (coarseProfileOf A).core.endpointMass () x c) : c.1 = x.1 := by
  rcases ((coarseProfileOf A).endpoint_pos_iff_path x () c).mp hpos
    with ⟨n, p, _, hend, hsupp⟩
  have hchain := (coarseProfileOf A).supportedFinPath_reflTransGen hsupp
  rw [hend] at hchain
  refine reflTransGen_mem_of_closed {r : State | r.1 = x.1} ?_ hchain rfl
  intro u hu v huv
  rw [Set.mem_ofPred_eq] at hu ⊢
  rw [hA u v huv, hu]

/-- Endpoint-uniqueness obstruction for the whole self-update-only sub-class:
with positive coarse hits from both declared sources, the two endpoint
supports differ in the shared register. -/
theorem selfUpdateOnly_coarse_endpoint_cut (A : AdmissibleScheduler)
    (hA : SelfUpdateOnly A)
    (hfalse : 0 < (coarseProfileOf A).core.hit () (false, true))
    (htrue : 0 < (coarseProfileOf A).core.hit () (true, true)) :
    ¬ (coarseProfileOf A).core.EndpointUnique () := by
  intro hU
  rcases ((coarseProfileOf A).hit_pos_iff_endpoint () (false, true)).mp hfalse
    with ⟨c, hc⟩
  rcases ((coarseProfileOf A).hit_pos_iff_endpoint () (true, true)).mp htrue
    with ⟨d, hd⟩
  have hmemf : ((false, true) : State) ∈ (coarseProfileOf A).core.initial () := by
    simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore]
  have hmemt : ((true, true) : State) ∈ (coarseProfileOf A).core.initial () := by
    simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore]
  have heq : c = d := hU.2 (false, true) hmemf c hc (true, true) hmemt d hd
  have hc1 : c.1 = false := selfUpdateOnly_coarse_endpoint_shared A hA hc
  have hd1 : d.1 = true := selfUpdateOnly_coarse_endpoint_shared A hA hd
  rw [heq] at hc1
  rw [hc1] at hd1
  exact Bool.false_ne_true hd1

/-- Sub-class obstruction at layer 3: no self-update-only scheduler places
the coarse behavior in layer 3. -/
theorem selfUpdateOnly_coarse_not_layer3 (A : AdmissibleScheduler)
    (hA : SelfUpdateOnly A) : () ∉ (coarseProfileOf A).layer3 := by
  intro h3
  change (coarseProfileOf A).core.InL3 () at h3
  have hmemf : ((false, true) : State) ∈ (coarseProfileOf A).core.initial () := by
    simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore]
  have hmemt : ((true, true) : State) ∈ (coarseProfileOf A).core.initial () := by
    simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore]
  have hf := h3.1.2 (false, true) hmemf
  have ht := h3.1.2 (true, true) hmemt
  exact selfUpdateOnly_coarse_endpoint_cut A hA
    (by rw [hf]; norm_num) (by rw [ht]; norm_num) h3.2

/-- Sub-class obstruction at layer 1: every network-update-only scheduler
misses the coarse target from every state whose private flag is raised. -/
theorem networkUpdateOnly_coarse_cut (A : AdmissibleScheduler)
    (hA : NetworkUpdateOnly A) :
    ∀ q : State, q.2 = true → (coarseProfileOf A).core.hit () q = 0 := by
  intro q hq
  show hitProbability A.kernel ((coarseProfileOf A).core.IsTarget ()) q = 0
  apply hitProbability_eq_zero_on_closed A.kernel
    ((coarseProfileOf A).core.IsTarget ()) {r : State | r.2 = true}
  · intro u hu ht
    rw [Set.mem_ofPred_eq] at hu
    have ht' : u.2 = false := by
      simp only [coarseProfileOf, coarseModelOf, TwoBit.coarseCore,
        TwoBit.coarseTarget, TwoBit.CoarseTargetPred,
        FixedBehaviorModel.IsTarget] at ht
      exact @of_decide_eq_true _ _ ht
    rw [hu] at ht'
    exact Bool.noConfusion ht'
  · intro u hu v huv
    rw [Set.mem_ofPred_eq] at hu ⊢
    rw [hA u v huv, hu]
  · exact hq

/-- Pricing corollary: any in-class scheduler that places the coarse behavior
in layer 3 spends shared capacity on some supported step. -/
theorem coarse_layer3_requires_shared_spend (A : AdmissibleScheduler)
    (h3 : () ∈ (coarseProfileOf A).layer3) :
    ∃ q r : State, SupportStep A.kernel q r ∧ sharedCost q r = 1 := by
  by_contra hnone
  push Not at hnone
  have hself : SelfUpdateOnly A := by
    intro q r hqr
    have hne := hnone q r hqr
    by_contra hne1
    exact hne (by simp [sharedCost, hne1])
  exact selfUpdateOnly_coarse_not_layer3 A hself h3

/-- Pricing corollary: any in-class scheduler that places the coarse behavior
in layer 3 spends private capacity on some supported step. -/
theorem coarse_layer3_requires_private_spend (A : AdmissibleScheduler)
    (h3 : () ∈ (coarseProfileOf A).layer3) :
    ∃ q r : State, SupportStep A.kernel q r ∧ privateCost q r = 1 := by
  by_contra hnone
  push Not at hnone
  have hnet : NetworkUpdateOnly A := by
    intro q r hqr
    have hne := hnone q r hqr
    by_contra hne1
    exact hne (by simp [privateCost, hne1])
  change (coarseProfileOf A).core.InL3 () at h3
  have hmemf : ((false, true) : State) ∈ (coarseProfileOf A).core.initial () := by
    simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore]
  have hone := h3.1.2 (false, true) hmemf
  have hzero := networkUpdateOnly_coarse_cut A hnet (false, true) rfl
  rw [hone] at hzero
  norm_num at hzero

/-! ### Full-class escape witness: merge the shared record, then clear -/

/-- Deterministic merge-then-clear move: a raised flag first writes the shared
register to `true`, then clears the private flag; consistent states are
fixed. -/
def mergeNext (q : State) : State :=
  if q.2 = true then (if q.1 = true then (true, false) else (true, true)) else q

def mergeKernel : FiniteMarkovKernel State where
  probability q r := if r = mergeNext q then 1 else 0
  probability_nonneg := by
    intro q r
    split <;> norm_num
  probability_sum_one := by
    intro q
    simp

theorem mergeKernel_support {q r : State}
    (h : SupportStep mergeKernel q r) : r = mergeNext q := by
  by_contra hne
  simp [SupportStep, mergeKernel, hne] at h

theorem mergeKernel_apply (V : State → ℝ) (q : State) :
    mergeKernel.apply V q = V (mergeNext q) := by
  simp [FiniteMarkovKernel.apply, mergeKernel]

/-- The merge-then-clear kernel as a class member: it satisfies all three
clauses while writing the shared register on one supported step and the
private register on another. -/
def mergeScheduler : AdmissibleScheduler where
  kernel := mergeKernel
  mismatch_nonincrease := by
    intro q r hqr
    rw [mergeKernel_support hqr]
    rcases q with ⟨b, d⟩
    cases b <;> cases d <;> norm_num [mergeNext, mismatch]
  locality := by
    intro q r hqr
    rw [mergeKernel_support hqr]
    rcases q with ⟨b, d⟩
    cases b <;> cases d <;> simp [mergeNext, LocalMove]
  capacity_bound := by
    intro q
    rw [Finset.sum_eq_single (mergeNext q)]
    · rcases q with ⟨b, d⟩
      cases b <;> cases d <;>
        norm_num [mergeKernel, mergeNext, stepCost, privateCost, sharedCost]
    · intro r _ hr
      simp [mergeKernel, hr]
    · simp

theorem mergeScheduler_not_selfUpdateOnly : ¬ SelfUpdateOnly mergeScheduler := by
  intro h
  have hstep : SupportStep mergeScheduler.kernel (false, true) (true, true) := by
    simp [SupportStep, mergeScheduler, mergeKernel, mergeNext]
  have hfix := h (false, true) (true, true) hstep
  exact Bool.noConfusion hfix

theorem mergeScheduler_not_networkUpdateOnly :
    ¬ NetworkUpdateOnly mergeScheduler := by
  intro h
  have hstep : SupportStep mergeScheduler.kernel (true, true) (true, false) := by
    simp [SupportStep, mergeScheduler, mergeKernel, mergeNext]
  have hfix := h (true, true) (true, false) hstep
  exact Bool.noConfusion hfix

theorem merge_coarse_hit_one_true :
    (coarseProfileOf mergeScheduler).core.hit () (true, true) = 1 := by
  show hitProbability mergeKernel
    ((coarseModelOf mergeScheduler).IsTarget ()) (true, true) = 1
  rw [hitProbability_bellman]
  have hs : ¬ (coarseModelOf mergeScheduler).IsTarget () (true, true) := by
    simp [coarseModelOf, TwoBit.coarseCore, TwoBit.coarseTarget,
      TwoBit.CoarseTargetPred, FixedBehaviorModel.IsTarget]
  rw [ite_eq_right hs]
  change mergeKernel.apply
    (fun z => hitProbability mergeKernel
      ((coarseModelOf mergeScheduler).IsTarget ()) z) (true, true) = 1
  rw [mergeKernel_apply]
  have hnext : mergeNext (true, true) = (true, false) := by simp [mergeNext]
  rw [hnext, hitProbability_bellman]
  have ht : (coarseModelOf mergeScheduler).IsTarget () (true, false) := by
    simp [coarseModelOf, TwoBit.coarseCore, TwoBit.coarseTarget,
      TwoBit.CoarseTargetPred, FixedBehaviorModel.IsTarget]
  rw [ite_eq_left ht]

theorem merge_coarse_hit_one_false :
    (coarseProfileOf mergeScheduler).core.hit () (false, true) = 1 := by
  show hitProbability mergeKernel
    ((coarseModelOf mergeScheduler).IsTarget ()) (false, true) = 1
  rw [hitProbability_bellman]
  have hs : ¬ (coarseModelOf mergeScheduler).IsTarget () (false, true) := by
    simp [coarseModelOf, TwoBit.coarseCore, TwoBit.coarseTarget,
      TwoBit.CoarseTargetPred, FixedBehaviorModel.IsTarget]
  rw [ite_eq_right hs]
  change mergeKernel.apply
    (fun z => hitProbability mergeKernel
      ((coarseModelOf mergeScheduler).IsTarget ()) z) (false, true) = 1
  rw [mergeKernel_apply]
  have hnext : mergeNext (false, true) = (true, true) := by simp [mergeNext]
  rw [hnext]
  exact merge_coarse_hit_one_true

/-- Under the merge scheduler every positive coarse endpoint from a
raised-flag source is the consistent state with shared register `true`. -/
theorem merge_coarse_endpoint_eq {x c : State} (hx : x.2 = true)
    (hpos : 0 < (coarseProfileOf mergeScheduler).core.endpointMass () x c) :
    c = (true, false) := by
  have htarget := (coarseProfileOf mergeScheduler).endpoint_pos_target hpos
  have hc2 : c.2 = false := by
    simp only [coarseProfileOf, coarseModelOf, TwoBit.coarseCore,
      TwoBit.coarseTarget, TwoBit.CoarseTargetPred,
      FixedBehaviorModel.IsTarget] at htarget
    exact @of_decide_eq_true _ _ htarget
  rcases ((coarseProfileOf mergeScheduler).endpoint_pos_iff_path x () c).mp hpos
    with ⟨n, p, _, hend, hsupp⟩
  have hchain :=
    (coarseProfileOf mergeScheduler).supportedFinPath_reflTransGen hsupp
  rw [hend] at hchain
  have hmem : c ∈ {r : State | r.1 = true ∨ r.2 = true} := by
    refine reflTransGen_mem_of_closed {r : State | r.1 = true ∨ r.2 = true}
      ?_ hchain ?_
    · intro u hu v huv
      rw [Set.mem_ofPred_eq] at hu ⊢
      rw [mergeKernel_support huv]
      rcases u with ⟨b, d⟩
      cases b <;> cases d <;> simp [mergeNext] at hu ⊢
    · rw [Set.mem_ofPred_eq]
      exact Or.inr hx
  rw [Set.mem_ofPred_eq] at hmem
  clear hpos htarget hchain hsupp hend
  rcases c with ⟨cb, cd⟩
  cases cb <;> cases cd <;> simp at hc2 hmem ⊢

/-- Full-class escape at layer 3: the merge scheduler places the coarse
behavior in layer 3, although it lies in neither sub-class. -/
theorem merge_coarse_layer3 : () ∈ (coarseProfileOf mergeScheduler).layer3 := by
  change (coarseProfileOf mergeScheduler).core.InL3 ()
  have hmemt : ((true, true) : State) ∈
      (coarseProfileOf mergeScheduler).core.initial () := by
    simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore]
  have hinit : ∀ q ∈ (coarseProfileOf mergeScheduler).core.initial (),
      q.2 = true := by
    intro q hq
    have hq' : q = (false, true) ∨ q = (true, true) := by
      simpa [coarseProfileOf, coarseModelOf, TwoBit.coarseCore] using hq
    rcases hq' with rfl | rfl <;> rfl
  have hAS : (coarseProfileOf mergeScheduler).core.AlmostSure () := by
    intro q hq
    have hq' : q = (false, true) ∨ q = (true, true) := by
      simpa [coarseProfileOf, coarseModelOf, TwoBit.coarseCore] using hq
    rcases hq' with rfl | rfl
    · exact merge_coarse_hit_one_false
    · exact merge_coarse_hit_one_true
  have hpos : 0 < (coarseProfileOf mergeScheduler).core.hit () (true, true) := by
    rw [merge_coarse_hit_one_true]
    norm_num
  refine ⟨⟨⟨⟨by simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore], ?_⟩,
    ⟨(true, true), hmemt, hpos⟩⟩, hAS⟩, ?_⟩
  · exact ⟨(true, false), by
      simp [coarseProfileOf, coarseModelOf, TwoBit.coarseCore,
        TwoBit.coarseTarget, TwoBit.CoarseTargetPred,
        FixedBehaviorModel.IsTarget]⟩
  · refine ⟨⟨(true, true), hmemt, ?_⟩, ?_⟩
    · exact ((coarseProfileOf mergeScheduler).hit_pos_iff_endpoint
        () (true, true)).mp hpos
    · intro x hx c hc y hy d hd
      have hc' := merge_coarse_endpoint_eq (hinit x hx) hc
      have hd' := merge_coarse_endpoint_eq (hinit y hy) hd
      subst hc'
      subst hd'
      exact (coarseProfileOf mergeScheduler).core.silent.iseqv.refl _

/-- Composed receipt for the endpoint-uniqueness cut on the coarse fixture:
layer 3 is unreachable for the whole self-update-only sub-class, the coarse
target is unreachable for the whole network-update-only sub-class, an
explicit class member outside both sub-classes reaches layer 3, and every
in-class scheduler that reaches layer 3 spends both capacities. -/
theorem coarse_endpoint_capacity_split_receipt :
    (∀ A : AdmissibleScheduler, SelfUpdateOnly A →
      () ∉ (coarseProfileOf A).layer3) ∧
    (∀ A : AdmissibleScheduler, NetworkUpdateOnly A →
      ∀ q : State, q.2 = true → (coarseProfileOf A).core.hit () q = 0) ∧
    (∃ A : AdmissibleScheduler, ¬ SelfUpdateOnly A ∧ ¬ NetworkUpdateOnly A ∧
      () ∈ (coarseProfileOf A).layer3) ∧
    (∀ A : AdmissibleScheduler, () ∈ (coarseProfileOf A).layer3 →
      (∃ q r : State, SupportStep A.kernel q r ∧ sharedCost q r = 1) ∧
      (∃ q r : State, SupportStep A.kernel q r ∧ privateCost q r = 1)) :=
  ⟨selfUpdateOnly_coarse_not_layer3, networkUpdateOnly_coarse_cut,
    ⟨mergeScheduler, mergeScheduler_not_selfUpdateOnly,
      mergeScheduler_not_networkUpdateOnly, merge_coarse_layer3⟩,
    fun A h3 => ⟨coarse_layer3_requires_shared_spend A h3,
      coarse_layer3_requires_private_spend A h3⟩⟩

/-! ## Composed receipt -/

/-- Composed receipt on the declared antecedent bundle: sub-class
nonvacuity and strictness, the all-scheduler defect cut, the capacity-split
separation on the cross fiber, and the almost-sure hypothesis discharge with
its in-class counterexample. -/
theorem scheduler_class_composed_receipt :
    (SelfUpdateOnly repairScheduler ∧
      NetworkUpdateOnly networkSwapScheduler ∧
      ¬ SelfUpdateOnly networkSwapScheduler) ∧
    (∀ A : AdmissibleScheduler, ∀ q : State, q.2 = false →
      hitProbability A.kernel DefectTarget q = 0) ∧
    (∀ b : Bool,
      (∀ A : AdmissibleScheduler, SelfUpdateOnly A →
        hitProbability A.kernel (CrossTarget b) ((!b, false) : State) = 0) ∧
      (∃ A : AdmissibleScheduler, NetworkUpdateOnly A ∧
        hitProbability A.kernel (CrossTarget b) ((!b, false) : State) = 1)) ∧
    ((∀ b : Bool, (fineModelOf repairScheduler).AlmostSure b) ∧
      ∃ A : AdmissibleScheduler, ¬ (fineModelOf A).AlmostSure true) := by
  refine ⟨⟨repairScheduler_selfUpdateOnly,
      networkSwapScheduler_networkUpdateOnly,
      networkSwapScheduler_not_selfUpdateOnly⟩,
    all_scheduler_defect_cut, ?_,
    repairScheduler_discharges_almostSure, class_does_not_force_almostSure⟩
  intro b
  exact capacity_split_separation b

end

#print axioms all_scheduler_defect_cut
#print axioms capacity_split_separation
#print axioms cross_hit_requires_shared_spend
#print axioms repairScheduler_discharges_almostSure
#print axioms class_does_not_force_almostSure
#print axioms defectInjectionKernel_defect_hit
#print axioms scheduler_class_composed_receipt
#print axioms fine_layer2_eq_layer3_of_class
#print axioms selfUpdateOnly_coarse_not_layer3
#print axioms networkUpdateOnly_coarse_cut
#print axioms merge_coarse_layer3
#print axioms coarse_layer3_requires_shared_spend
#print axioms coarse_layer3_requires_private_spend
#print axioms coarse_endpoint_capacity_split_receipt

end ObservableNormalForms.ProtectedObstructions.SchedulerClass

module
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

/-!
# Support of constrained finite information projections

The classical finite I-projection support theorem, proved from the convexity
of x log x and its exact mixture gap at zero. No KKT certificate, full-simplex
assumption, uniform reference or independent-word law is assumed. The
feasible set is any convex set of nonnegative finite vectors with an attained
minimum. Flattening a finite classical observer cover gives such vectors;
the coordinates are cover atoms, not automatically complete history atoms.
-/

set_option autoImplicit false

namespace OPH.SourceConstrainedSelection
noncomputable section
open InformationTheory

variable {A : Type*} [Fintype A]

def entropyTerm (c x : ℝ) : ℝ := x * Real.log x + c*x

def potential (weight cost p : A → ℝ) : ℝ :=
  ∑ i, weight i * entropyTerm (cost i) (p i)

def mixture (t : ℝ) (p q : A → ℝ) : A → ℝ :=
  fun i => (1-t)*p i + t*q i

theorem entropyTerm_mixture_le (c x y t : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    entropyTerm c ((1-t)*x+t*y) ≤
      (1-t)*entropyTerm c x + t*entropyTerm c y := by
  have h := Real.convexOn_mul_log.2 hx hy (sub_nonneg.mpr ht1) ht (by ring)
  simp only [smul_eq_mul] at h
  unfold entropyTerm
  nlinarith

theorem entropyTerm_zero_mixture (c y t : ℝ) (hy : 0 < y) (ht : 0 < t) :
    entropyTerm c (t*y) = t*entropyTerm c y + t*y*Real.log t := by
  unfold entropyTerm
  rw [Real.log_mul (ne_of_gt ht) (ne_of_gt hy)]
  ring

/-- The negative t log t gap at a coordinate populated by the mixture dominates
every finite change elsewhere. This is stronger than ordinary convexity. -/
theorem potential_mixture_gap (weight cost p q : A → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j)
    (i : A) (hpi : p i = 0) (hqi : 0 < q i)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    potential weight cost (mixture t p q) ≤
      (1-t)*potential weight cost p + t*potential weight cost q +
        t*weight i*q i*Real.log t := by
  classical
  calc
    potential weight cost (mixture t p q) ≤
        ∑ j, ((1-t)*(weight j*entropyTerm (cost j) (p j)) +
          t*(weight j*entropyTerm (cost j) (q j)) +
          if j=i then t*weight i*q i*Real.log t else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j=i
      · subst j
        simp only [mixture, hpi, mul_zero, zero_add, entropyTerm,
          Real.log_zero, add_zero, ite_true]
        rw [Real.log_mul (ne_of_gt ht) (ne_of_gt hqi)]
        ring_nf
        exact le_rfl
      · simp only [ite_eq_right hj, add_zero]
        have h := mul_le_mul_of_nonneg_left
          (entropyTerm_mixture_le (cost j) (p j) (q j) t (hp j) (hq j) ht.le ht1) (hw j)
        change weight j * entropyTerm (cost j) ((1-t)*p j+t*q j) ≤ _
        nlinarith
    _ = (1-t)*potential weight cost p + t*potential weight cost q +
        t*weight i*q i*Real.log t := by
      simp only [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp [potential]

theorem exists_small_log (bound : ℝ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ Real.log t < bound := by
  let z := min (-1 : ℝ) (bound-1)
  have hz : z < 0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨Real.exp z, Real.exp_pos z, Real.exp_lt_one_iff.mpr hz, ?_⟩
  rw [Real.log_exp]
  exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

/-- Any attained minimum of the weighted entropy-plus-linear objective on
a convex nonnegative feasible set has the union of all feasible supports. -/
theorem potential_minimizer_support (K : Set (A → ℝ))
    (hK : Convex ℝ K) (hKnonneg : ∀ p ∈ K, ∀ i, 0 ≤ p i)
    (weight cost p : A → ℝ) (hw : ∀ i, 0 < weight i)
    (hp : p ∈ K) (hmin : ∀ q ∈ K, potential weight cost p ≤ potential weight cost q)
    (q : A → ℝ) (hq : q ∈ K) (i : A) (hqi : 0 < q i) : 0 < p i := by
  by_contra hpi
  have hz : p i = 0 := le_antisymm (le_of_not_gt hpi) (hKnonneg p hp i)
  have hc : 0 < weight i*q i := mul_pos (hw i) hqi
  obtain ⟨t, ht, ht1, hlog⟩ := exists_small_log
    ((potential weight cost p-potential weight cost q)/(weight i*q i))
  have hslope := (lt_div_iff₀ hc).mp hlog
  have hmem : mixture t p q ∈ K := by
    convert hK hp hq (sub_nonneg.mpr ht1.le) ht.le (by ring) using 1
    congr 1
  have hbound := potential_mixture_gap weight cost p q (fun j => (hw j).le)
    (hKnonneg p hp) (hKnonneg q hq) i hz hqi t ht ht1.le
  have hminimal := hmin (mixture t p q) hmem
  have hstrict := mul_lt_mul_of_pos_left hslope ht
  nlinarith

/-- Weighted finite classical KL in Mathlib's f-divergence convention. With
normalized local probabilities and one weight per observer this is precisely
the weighted sum of local classical relative entropies. -/
def weightedKL (weight reference p : A → ℝ) : ℝ :=
  ∑ i, weight i * (reference i * klFun (p i/reference i))

theorem klTerm_expansion (x r : ℝ) (hr : 0 < r) :
    r*klFun (x/r) = entropyTerm (-Real.log r-1) x+r := by
  by_cases hx : x=0
  · simp [hx, klFun, entropyTerm]
  · rw [klFun, Real.log_div hx (ne_of_gt hr)]
    unfold entropyTerm
    field_simp
    ring

theorem weightedKL_expansion (weight reference p : A → ℝ)
    (hr : ∀ i, 0 < reference i) :
    weightedKL weight reference p =
      potential weight (fun i => -Real.log (reference i)-1) p +
        ∑ i, weight i*reference i := by
  unfold weightedKL potential
  simp_rw [klTerm_expansion _ _ (hr _), mul_add]
  exact Finset.sum_add_distrib

theorem weightedKL_minimizer_support (K : Set (A → ℝ))
    (hK : Convex ℝ K) (hKnonneg : ∀ p ∈ K, ∀ i, 0 ≤ p i)
    (weight reference p : A → ℝ) (hw : ∀ i, 0 < weight i)
    (hr : ∀ i, 0 < reference i) (hp : p ∈ K)
    (hmin : ∀ q ∈ K, weightedKL weight reference p ≤ weightedKL weight reference q)
    (q : A → ℝ) (hq : q ∈ K) (i : A) (hqi : 0 < q i) : 0 < p i := by
  apply potential_minimizer_support K hK hKnonneg weight
    (fun j => -Real.log (reference j)-1) p hw hp _ q hq i hqi
  intro v hv
  simpa only [weightedKL_expansion weight reference _ hr, add_le_add_iff_right]
    using hmin v hv

/-- A selected zero-probability event made of directly scored cover atoms
is excluded by the entire feasible family. No uniformity or IID
assumption is involved. Atoms absent from the entropy cover are not covered. -/
theorem selected_zero_event_iff (K : Set (A → ℝ))
    (hK : Convex ℝ K) (hKnonneg : ∀ p ∈ K, ∀ i, 0 ≤ p i)
    (weight reference p : A → ℝ) (hw : ∀ i, 0 < weight i)
    (hr : ∀ i, 0 < reference i) (hp : p ∈ K)
    (hmin : ∀ q ∈ K, weightedKL weight reference p ≤ weightedKL weight reference q)
    (bad : A → Prop) :
    (∀ i, bad i → p i=0) ↔ ∀ q ∈ K, ∀ i, bad i → q i=0 := by
  constructor
  · intro h q hq i hi
    by_contra hqi
    have hpositive : 0 < q i := lt_of_le_of_ne (hKnonneg q hq i) (Ne.symm hqi)
    have hpstar := weightedKL_minimizer_support K hK hKnonneg weight reference p
      hw hr hp hmin q hq i hpositive
    rw [h i hi] at hpstar
    exact (lt_irrefl 0) hpstar
  · intro h
    exact h p hp

theorem weightedKL_nonnegative (weight reference p : A → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hr : ∀ i, 0 < reference i)
    (hp : ∀ i, 0 ≤ p i) : 0 ≤ weightedKL weight reference p := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hw i) (mul_nonneg (hr i).le
    (klFun_nonneg (div_nonneg (hp i) (hr i).le)))

theorem weightedKL_self (weight reference : A → ℝ)
    (hr : ∀ i, 0 < reference i) : weightedKL weight reference reference = 0 := by
  unfold weightedKL
  simp [div_self (ne_of_gt (hr _)), klFun_one]

theorem weightedKL_zero_iff (weight reference p : A → ℝ)
    (hw : ∀ i, 0 < weight i) (hr : ∀ i, 0 < reference i)
    (hp : ∀ i, 0 ≤ p i) : weightedKL weight reference p = 0 ↔ p=reference := by
  constructor
  · intro h
    have hterms : ∀ i, weight i*(reference i*klFun (p i/reference i))=0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hw j).le
        (mul_nonneg (hr j).le (klFun_nonneg (div_nonneg (hp j) (hr j).le))))).mp h i
          (Finset.mem_univ i)
    funext i
    have hzero : klFun (p i/reference i)=0 := by
      rcases mul_eq_zero.mp (hterms i) with hbad | hgood
      · exact ((ne_of_gt (hw i)) hbad).elim
      · exact (mul_eq_zero.mp hgood).resolve_left (ne_of_gt (hr i))
    have hratio := (klFun_eq_zero_iff (div_nonneg (hp i) (hr i).le)).mp hzero
    exact (div_eq_one_iff_eq (ne_of_gt (hr i))).mp hratio
  · rintro rfl
    exact weightedKL_self weight _ hr

theorem klTerm_projection_identity (x p r : ℝ) (hp : 0 < p) (hr : 0 < r) :
    r*klFun (x/r) = p*klFun (x/p)+r*klFun (p/r)+(x-p)*Real.log (p/r) := by
  rw [klTerm_expansion x r hr, klTerm_expansion x p hp,
    klTerm_expansion p r hr, Real.log_div (ne_of_gt hp) (ne_of_gt hr)]
  unfold entropyTerm
  ring

/-- An exact affine moment certificate establishes the optimizer on the
whole feasible family. -/
theorem weightedKL_projection_identity (weight reference selected q : A → ℝ)
    (hr : ∀ i, 0 < reference i) (hp : ∀ i, 0 < selected i)
    (hmoment : ∑ i, weight i*(q i-selected i)*Real.log (selected i/reference i)=0) :
    weightedKL weight reference q = weightedKL weight selected q +
      weightedKL weight reference selected := by
  unfold weightedKL
  calc
    _ = ∑ i, (weight i*(selected i*klFun (q i/selected i)) +
        weight i*(reference i*klFun (selected i/reference i)) +
        weight i*(q i-selected i)*Real.log (selected i/reference i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [klTerm_projection_identity _ _ _ (hp i) (hr i)]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hmoment, add_zero]

theorem affine_certificate_unique_minimum (weight reference selected q : A → ℝ)
    (hw : ∀ i, 0 < weight i) (hr : ∀ i, 0 < reference i)
    (hp : ∀ i, 0 < selected i) (hq : ∀ i, 0 ≤ q i)
    (hmoment : ∑ i, weight i*(q i-selected i)*Real.log (selected i/reference i)=0) :
    weightedKL weight reference selected ≤ weightedKL weight reference q ∧
      (weightedKL weight reference selected = weightedKL weight reference q ↔ q=selected) := by
  rw [weightedKL_projection_identity weight reference selected q hr hp hmoment]
  have hnonneg := weightedKL_nonnegative weight selected q (fun i => (hw i).le) hp hq
  constructor
  · linarith
  · constructor
    · intro heq
      apply (weightedKL_zero_iff weight selected q hw hp hq).mp
      linarith
    · rintro rfl
      rw [weightedKL_self weight _ hp, zero_add]

/-- A nonnegative observable cannot vanish at a support-dominating selected
state while being positive at another feasible state. Negative coefficients
or an affine negative offset would invalidate this implication. -/
theorem positive_readout_zero_of_support (coefficient p q : A → ℝ)
    (hc : ∀ i, 0 ≤ coefficient i) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsupport : ∀ i, 0 < q i → 0 < p i)
    (hzero : ∑ i, coefficient i*p i=0) : ∑ i, coefficient i*q i=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hc j) (hp j))).mp hzero i hi
  by_cases hc0 : coefficient i=0
  · simp [hc0]
  · have hp0 := (mul_eq_zero.mp hterm).resolve_left hc0
    have hq0 : q i=0 := by
      by_contra h
      have hpos := hsupport i (lt_of_le_of_ne (hq i) (Ne.symm h))
      rw [hp0] at hpos
      exact (lt_irrefl 0) hpos
    simp [hq0]

/-- Applies to any failure probability represented by a nonnegative linear
observable of the scored atoms. A state-determining cover alone does not
provide this representation, as the separate cover control demonstrates. -/
theorem selected_zero_readout_iff (K : Set (A → ℝ))
    (hK : Convex ℝ K) (hKnonneg : ∀ p ∈ K, ∀ i, 0 ≤ p i)
    (weight reference p coefficient : A → ℝ) (hw : ∀ i, 0 < weight i)
    (hr : ∀ i, 0 < reference i) (hc : ∀ i, 0 ≤ coefficient i) (hp : p ∈ K)
    (hmin : ∀ q ∈ K, weightedKL weight reference p ≤ weightedKL weight reference q) :
    (∑ i, coefficient i*p i=0) ↔ ∀ q ∈ K, ∑ i, coefficient i*q i=0 := by
  constructor
  · intro h q hq
    exact positive_readout_zero_of_support coefficient p q hc (hKnonneg p hp)
      (hKnonneg q hq)
      (weightedKL_minimizer_support K hK hKnonneg weight reference p hw hr hp hmin q hq) h
  · intro h
    exact h p hp

end
end OPH.SourceConstrainedSelection

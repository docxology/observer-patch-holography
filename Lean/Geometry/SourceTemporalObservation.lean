module
public import Geometry.SourceReadAcceptance
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# Complete linear acceptance grammar from a finite observation record

The observation forms are generated independently of the requested meaning.
Agreement on their fibers determines exactly their linear span. This derives
the possible-observation relation and its maximal sound publication rule
for an unrestricted real linear preparation family. It does not identify
this family with the complete A1 data domain or select a metric request.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalObservation
noncomputable section
open OPH.SourceReadAcceptance

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I]

def Agrees (L : I → V →ₗ[ℝ] ℝ) (x y : V) : Prop := ∀ i, L i x = L i y

def Observable (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ x y, Agrees L x y → f x = f y

def Possible (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ)
    (value : ℝ) (samples : I → ℝ) : Prop :=
  ∃ x, (∀ i, L i x = samples i) ∧ f x = value

omit [Fintype I] in
theorem observable_iff_kernel [_instFintypeI : Fintype I] (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) :
    Observable L f ↔ (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker f := by
  constructor
  · intro h z hz
    apply (show f z = 0 from ?_)
    simpa using h z 0 (fun i => by
      have hi := ((Submodule.mem_iInf _).mp hz) i
      simpa using hi)
  · intro h x y hxy
    have hz : x-y ∈ ⨅ i, LinearMap.ker (L i) := by
      apply (Submodule.mem_iInf _).mpr
      intro i
      simp only [LinearMap.mem_ker, map_sub, hxy i, sub_self]
    simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using h hz

/-- Every compatible linear meaning factors through the observed forms.
This covers all linear meanings on this domain, not a finite test menu. -/
theorem observable_iff_span (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) :
    Observable L f ↔ f ∈ Submodule.span ℝ (Set.range L) := by
  constructor
  · intro h
    exact mem_span_of_iInf_ker_le_ker ((observable_iff_kernel L f).mp h)
  · intro h x y hxy
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h
    rw [← hc]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [hxy i])

theorem observable_iff_decoder (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) :
    Observable L f ↔ ∃ c : I → ℝ, ∀ x, f x = ∑ i, c i * L i x := by
  constructor
  · intro h
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
      ((observable_iff_span L f).mp h)
    refine ⟨c,fun x => ?_⟩
    rw [← hc]
    simp
  · rintro ⟨c,hc⟩ x y hxy
    rw [hc x,hc y]
    exact Finset.sum_congr rfl (fun i _ => by rw [hxy i])

/-- At every feasible observation, an invisible perturbation prevents any
sound policy from publishing a nonobservable linear meaning. -/
theorem identifies_iff_observable (L : I → V →ₗ[ℝ] ℝ)
    (f : V →ₗ[ℝ] ℝ) (x : V) :
    Identifies (Possible L f) (fun i => L i x) (f x) ↔ Observable L f := by
  constructor
  · intro h
    apply (observable_iff_kernel L f).mpr
    intro z hz
    have hobs : ∀ i, L i (x+z) = L i x := by
      intro i
      have hi : L i z = 0 := ((Submodule.mem_iInf _).mp hz) i
      simp [hi]
    have he := h.2 (f (x+z)) ⟨x+z,hobs,rfl⟩
    simpa only [LinearMap.mem_ker, map_add, add_eq_left] using he
  · intro h
    refine ⟨⟨x,fun _ => rfl,rfl⟩,?_⟩
    rintro v ⟨y,hy,rfl⟩
    exact h y x hy

theorem canonical_publication_iff (L : I → V →ₗ[ℝ] ℝ)
    (f : V →ₗ[ℝ] ℝ) (x : V) :
    canonical (Possible L f) (fun i => L i x) = some (f x) ↔
      f ∈ Submodule.span ℝ (Set.range L) := by
  rw [canonical_some_iff, identifies_iff_observable, observable_iff_span]

theorem invisible_witness (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ)
    (h : ¬ Observable L f) : ∃ z, (∀ i, L i z = 0) ∧ f z ≠ 0 := by
  rw [observable_iff_kernel] at h
  by_contra hn
  push Not at hn
  apply h
  intro z hz
  exact hn z (fun i => ((Submodule.mem_iInf _).mp hz) i)

theorem nonobservable_abstains (L : I → V →ₗ[ℝ] ℝ)
    (f : V →ₗ[ℝ] ℝ) (publish : (I → ℝ) → Option ℝ)
    (hs : Sound (Possible L f) publish) (h : ¬ Observable L f) (x : V) :
    publish (fun i => L i x) = none := by
  obtain ⟨z,hz,hf⟩ := invisible_witness L f h
  apply shared_observation_abstains (Possible L f) publish hs _ (f x) (f (x+z))
  · exact ⟨x,fun _ => rfl,rfl⟩
  · exact ⟨x+z,fun i => by simp [hz i],rfl⟩
  · intro he
    apply hf
    have he' : f x = f x + f z := by simpa using he
    exact (add_eq_left.mp he'.symm)

omit [Fintype I] in
/-- Prefix extension preserves every identifiable meaning if each old
sample is among the extended observations. -/
theorem observable_extension [_instFintypeI : Fintype I] {J : Type*} [Fintype J]
    (L : I → V →ₗ[ℝ] ℝ) (M : J → V →ₗ[ℝ] ℝ)
    (embed : I → J) (he : ∀ i, M (embed i) = L i)
    (f : V →ₗ[ℝ] ℝ) (h : Observable L f) : Observable M f := by
  intro x y hxy
  apply h x y
  intro i
  simpa [he i] using hxy (embed i)

omit [Fintype I] in
/-- An invertible source presentation changes neither the accepted meanings
nor their temporal availability when preparation and meaning are transported
together. This does not assert refinement optimizer compatibility. -/
theorem observable_rechart [_instFintypeI : Fintype I] {U : Type*} [AddCommGroup U] [Module ℝ U]
    (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ) (e : U ≃ₗ[ℝ] V) :
    Observable (fun i => (L i).comp e.toLinearMap) (f.comp e.toLinearMap) ↔
      Observable L f := by
  constructor
  · intro h x y hxy
    simpa using h (e.symm x) (e.symm y) (fun i => by simpa using hxy i)
  · intro h x y hxy
    exact h (e x) (e y) hxy

/-- Exact coefficient certificates give a noise budget without treating
readout arithmetic or sample precision as free physical resources. -/
theorem decoder_error (L : I → V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ)
    (c ε samples : I → ℝ) (x : V)
    (hc : f x = ∑ i, c i * L i x)
    (he : ∀ i, |samples i-L i x| ≤ ε i) :
    |(∑ i, c i*samples i)-f x| ≤ ∑ i, |c i| * ε i := by
  rw [hc, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |c i*samples i-c i*L i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _))

end
end OPH.SourceTemporalObservation

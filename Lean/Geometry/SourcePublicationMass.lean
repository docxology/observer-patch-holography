module
public import Geometry.SourceCheckpointPolicy
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

/-!
# Monotone native-publication masses

The reference is a normalized finite move law. Publication persists under
subsequent moves. Finite publication probabilities then converge to a
constructed least harmonic majorant; no completion probability is supplied
as an oracle. This construction concerns the declared record predicate.
-/

set_option autoImplicit false

namespace OPH.SourcePublicationMass
noncomputable section
open OPH.SourceCheckpointPolicy Filter
open scoped Topology

variable {S A : Type*} [Fintype A]

theorem mass_mono_terminal (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (f g : S → ℝ) (hfg : ∀ s, f s ≤ g s)
    (n : ℕ) (s : S) : mass step weight f n s ≤ mass step weight g n s := by
  induction n generalizing s with
  | zero => exact hfg s
  | succ n ih => exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (ih _) (hw s a))

theorem mass_const (step : S → A → S) (weight : S → A → ℝ)
    (hs : ∀ s, ∑ a, weight s a = 1) (v : ℝ) (n : ℕ) (s : S) :
    mass step weight (fun _ => v) n s = v := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [mass,ih,← Finset.sum_mul,hs,one_mul]

theorem mass_add_steps (step : S → A → S) (weight : S → A → ℝ)
    (f : S → ℝ) (m n : ℕ) (s : S) :
    mass step weight f (m+n) s = mass step weight (mass step weight f n) m s := by
  induction m generalizing s with
  | zero => simp only [Nat.zero_add,mass]
  | succ m ih => simp only [Nat.succ_add,mass,ih]

theorem mass_harmonic (step : S → A → S) (weight : S → A → ℝ)
    (f : S → ℝ) (hf : ∀ s, ∑ a, weight s a * f (step s a) = f s)
    (n : ℕ) (s : S) : mass step weight f n s = f s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [mass,ih] using hf s

def eventual (step : S → A → S) (weight : S → A → ℝ) (f : S → ℝ) (s : S) : ℝ :=
  ⨆ n : ℕ, mass step weight f n s

theorem mass_bdd (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1) (s : S) :
    BddAbove (Set.range (fun n => mass step weight f n s)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n,rfl⟩
  exact (mass_mono_terminal step weight hw f (fun _ => 1) hf n s).trans_eq
    (mass_const step weight hs 1 n s)

theorem mass_mono_time (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (f : S → ℝ)
    (hp : ∀ s, f s ≤ ∑ a, weight s a * f (step s a)) (s : S) :
    Monotone (fun n => mass step weight f n s) := by
  apply monotone_nat_of_le_succ
  intro n
  simpa only [← mass_add_steps,Nat.add_comm] using
    mass_mono_terminal step weight hw f (mass step weight f 1) hp n s

theorem mass_tendsto (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1)
    (hp : ∀ s, f s ≤ ∑ a, weight s a * f (step s a)) (s : S) :
    Tendsto (fun n => mass step weight f n s) atTop (𝓝 (eventual step weight f s)) :=
  tendsto_atTop_ciSup (mass_mono_time step weight hw f hp s) (mass_bdd step weight hw hs f hf s)

theorem mass_le_eventual (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1) (n : ℕ) (s : S) :
    mass step weight f n s ≤ eventual step weight f s :=
  le_ciSup (mass_bdd step weight hw hs f hf s) n

theorem eventual_le_one (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1) (s : S) :
    eventual step weight f s ≤ 1 := by
  apply ciSup_le
  intro n
  exact (mass_mono_terminal step weight hw f (fun _ => 1) hf n s).trans_eq
    (mass_const step weight hs 1 n s)

theorem eventual_nonneg (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1) (hn : ∀ s, 0 ≤ f s) (s : S) :
    0 ≤ eventual step weight f s :=
  (hn s).trans (mass_le_eventual step weight hw hs f hf 0 s)

theorem eventual_least (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (f g : S → ℝ)
    (hfg : ∀ s, f s ≤ g s) (hg : ∀ s, ∑ a, weight s a * g (step s a) = g s)
    (s : S) : eventual step weight f s ≤ g s := by
  apply ciSup_le
  intro n
  exact (mass_mono_terminal step weight hw f g hfg n s).trans_eq
    (mass_harmonic step weight g hg n s)

theorem eventual_harmonic (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1)
    (hp : ∀ s, f s ≤ ∑ a, weight s a * f (step s a)) (s : S) :
    ∑ a, weight s a * eventual step weight f (step s a) = eventual step weight f s := by
  have hl := tendsto_finsetSum Finset.univ (fun a _ =>
    (mass_tendsto step weight hw hs f hf hp (step s a)).const_mul (weight s a))
  have hr := (mass_tendsto step weight hw hs f hf hp s).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hl (by simpa only [Function.comp_def, mass] using hr)

theorem eventual_pos_iff (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1) (s : S) :
    0 < eventual step weight f s ↔ ∃ n, 0 < mass step weight f n s := by
  constructor
  · intro h
    by_contra hn
    have hle : eventual step weight f s ≤ 0 :=
      ciSup_le (fun n => le_of_not_gt (fun hp => hn ⟨n,hp⟩))
    exact (not_lt_of_ge hle) h
  · rintro ⟨n,hn⟩
    exact hn.trans_le (mass_le_eventual step weight hw hs f hf n s)

theorem eventual_eq_one (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1) (s : S) (he : f s = 1) :
    eventual step weight f s = 1 := by
  apply le_antisymm (eventual_le_one step weight hw hs f hf s)
  simpa only [mass,he] using mass_le_eventual step weight hw hs f hf 0 s

theorem eventual_fixed_mass (step : S → A → S) (weight : S → A → ℝ)
    (hw : ∀ s a, 0 ≤ weight s a) (hs : ∀ s, ∑ a, weight s a = 1)
    (f : S → ℝ) (hf : ∀ s, f s ≤ 1)
    (hp : ∀ s, f s ≤ ∑ a, weight s a * f (step s a)) (n : ℕ) (s : S) :
    mass step weight (eventual step weight f) n s = eventual step weight f s :=
  mass_harmonic step weight _ (eventual_harmonic step weight hw hs f hf hp) n s

end
end OPH.SourcePublicationMass

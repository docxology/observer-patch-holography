module
public import Geometry.SourcePublicationLaw
public import Geometry.SourceCheckpointNative

@[expose] public section

/-!
# Native meaning preservation and the publication limit

Connected support identifies positivity of the constructed limiting mass
with native continuation viability. The response checkpoint contains all
preparation interventions and retained records; no payload or success oracle
is supplied to the controller. The public meaning remains an explicit input.
-/

set_option autoImplicit false

namespace OPH.SourcePublicationNative
noncomputable section
open OPH.SourceTemporalGuard OPH.SourceCheckpointMeaning OPH.SourceCheckpointNative
open OPH.SourceCheckpointPolicy OPH.SourcePublicationMass OPH.SourcePublicationLaw

variable {X R P A : Type*} [DecidableEq P] [Fintype A]

omit [DecidableEq P] in
theorem terminal_le_one (meaning : X → R) (c : Checkpoint X P) : terminal meaning c ≤ 1 := by
  classical
  unfold terminal
  split <;> norm_num

theorem publication_advance (meaning : X → R) (root : P) (c : Checkpoint X P)
    (e : P × P) (hp : Published meaning c) : Published meaning (advance root c e) :=
  publication_extends meaning root c [e] hp

theorem terminal_subharmonic (meaning : X → R) (root : P) (seam : A → P × P)
    (weight : Checkpoint X P → A → ℝ) (hw : ∀ c a, 0 ≤ weight c a)
    (hs : ∀ c, ∑ a, weight c a = 1) (c : Checkpoint X P) :
    terminal meaning c ≤ ∑ a, weight c a * terminal meaning (step root seam c a) := by
  classical
  by_cases hp : Published meaning c
  · have he : ∀ a, terminal meaning (step root seam c a) = 1 := by
      intro a
      exact ite_eq_left (publication_advance meaning root c (seam a) hp)
    simp only [he,mul_one,hs]
    exact terminal_le_one meaning c
  · rw [terminal,ite_eq_right hp]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw c a) (terminal_nonneg meaning _))

def completion (meaning : X → R) (root : P) (seam : A → P × P)
    (weight : Checkpoint X P → A → ℝ) (c : Checkpoint X P) : ℝ :=
  eventual (step root seam) weight (terminal meaning) c

/-- Native topology derives positivity of the limiting continuation mass.
The right side tests retained data and the evolving state, not future outcomes. -/
theorem completion_positive_iff [Fintype P] (G : SimpleGraph P) (hc : G.Connected)
    (meaning : X → R) (root : P) (seam : A → P × P)
    (cover : ∀ e : P × P, G.Adj e.1 e.2 →
      ∃ a, ∀ c : Checkpoint X P, advance root c (seam a) = advance root c e)
    (weight : Checkpoint X P → A → ℝ) (hw : ∀ c a, 0 < weight c a)
    (hs : ∀ c, ∑ a, weight c a = 1)
    (c : Checkpoint X P) (hr : HasRoot root c) :
    0 < completion meaning root seam weight c ↔ Viable meaning c := by
  rw [completion,eventual_pos_iff _ _ (fun c a => (hw c a).le) hs _ (terminal_le_one meaning)]
  constructor
  · rintro ⟨n,hn⟩
    exact positive_mass_viable meaning root seam weight hw c n hn
  · intro hv
    obtain ⟨n,_,hn⟩ := connected_positive_deadline G hc meaning root seam cover weight hw c hv hr
    exact ⟨n,hn⟩

theorem completion_harmonic (meaning : X → R) (root : P) (seam : A → P × P)
    (weight : Checkpoint X P → A → ℝ) (hw : ∀ c a, 0 ≤ weight c a)
    (hs : ∀ c, ∑ a, weight c a = 1) (c : Checkpoint X P) :
    ∑ a, weight c a * completion meaning root seam weight (step root seam c a) =
      completion meaning root seam weight c :=
  eventual_harmonic _ _ hw hs _ (terminal_le_one meaning)
    (terminal_subharmonic meaning root seam weight hw hs) c

theorem completion_published (meaning : X → R) (root : P) (seam : A → P × P)
    (weight : Checkpoint X P → A → ℝ) (hw : ∀ c a, 0 ≤ weight c a)
    (hs : ∀ c, ∑ a, weight c a = 1) (c : Checkpoint X P) (hp : Published meaning c) :
    completion meaning root seam weight c = 1 := by
  classical
  exact eventual_eq_one _ _ hw hs _ (terminal_le_one meaning) c (ite_eq_left hp)

omit [Fintype A] in
theorem run_has_root (root : P) (c : Checkpoint X P) (hr : HasRoot root c)
    (es : List (P × P)) : HasRoot root (run root es c) := by
  induction es generalizing c with
  | nil => exact hr
  | cons e es ih => exact ih _ (advance_has_root root c e)

/-- A positive selected prefix retains exactly the distinctions needed
for eventual publication, and every such prefix retains positive mass. -/
theorem native_cylinder_positive_iff [Fintype P] (G : SimpleGraph P) (hc : G.Connected)
    (meaning : X → R) (root : P) (seam : A → P × P)
    (cover : ∀ e : P × P, G.Adj e.1 e.2 →
      ∃ a, ∀ c : Checkpoint X P, advance root c (seam a) = advance root c e)
    (weight : Checkpoint X P → A → ℝ) (hw : ∀ c a, 0 < weight c a)
    (hs : ∀ c, ∑ a, weight c a = 1)
    (c : Checkpoint X P) (hr : HasRoot root c) (hv : Viable meaning c) (as : List A) :
    0 < cylinder (step root seam) weight (completion meaning root seam weight) c as ↔
      Viable meaning (run root (as.map seam) c) := by
  have hh := (completion_positive_iff G hc meaning root seam cover weight hw hs c hr).mpr hv
  rw [cylinder_positive_iff _ _ hw _ c hh as,finish_run]
  exact completion_positive_iff G hc meaning root seam cover weight hw hs _
    (run_has_root root c hr (as.map seam))

end
end OPH.SourcePublicationNative

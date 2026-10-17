module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Causal paths constructed from a spatial covering

A spatial set covers a convex window within distance `h`. The supplied layered
read law permits every step of length at most `a`, including waiting. Covering
points along a straight segment constructs every `k`-step path inside radius
`k * (a - 2*h)`; the triangle inequality bounds every permitted path by `k*a`.
The set, covering, read law and model clock are inputs. The result does not
identify accepted native repairs or a field action's propagation cone.
-/

namespace OPH.SourceNetCausalCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Covering by actual members of the spatial population. -/
def Covers (Ω S : Set E) (h : ℝ) : Prop :=
  ∀ x ∈ Ω, ∃ s ∈ S, ‖s - x‖ ≤ h

/-- All-neighbour reads advance one layer. Zero displacements are permitted. -/
def Reachable (S : Set E) (a : ℝ) (k : ℕ) (x y : E) : Prop :=
  ∃ p : ℕ → E, p 0 = x ∧ p k = y ∧
    (∀ j ≤ k, p j ∈ S) ∧ (∀ j < k, ‖p (j + 1) - p j‖ ≤ a)

noncomputable def segmentNode (x y : E) (k j : ℕ) : E :=
  x + ((j : ℝ) / (k : ℝ)) • (y - x)

@[simp] theorem segmentNode_zero (x y : E) (k : ℕ) :
    segmentNode x y k 0 = x := by simp [segmentNode]

theorem segmentNode_terminal (x y : E) {k : ℕ} (hk : 0 < k) :
    segmentNode x y k k = y := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  simp [segmentNode, hk']

theorem segmentNode_mem {Ω : Set E} (hΩ : Convex ℝ Ω) {x y : E}
    (hx : x ∈ Ω) (hy : y ∈ Ω) {k j : ℕ} (hk : 0 < k) (hj : j ≤ k) :
    segmentNode x y k j ∈ Ω := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply hΩ.add_smul_mem hx (by simpa using hy)
  exact ⟨div_nonneg (Nat.cast_nonneg j) hk'.le,
    (div_le_one hk').mpr (by exact_mod_cast hj)⟩

theorem segmentNode_step (x y : E) (k j : ℕ) :
    segmentNode x y k (j + 1) - segmentNode x y k j =
      (1 / (k : ℝ)) • (y - x) := by
  simp only [segmentNode, Nat.cast_add, Nat.cast_one]
  module

/-- A covering supplies the path; no path-existence hypothesis is used. -/
theorem covering_constructs_path {Ω S : Set E} {h a : ℝ}
    (hΩ : Convex ℝ Ω) (hS : S ⊆ Ω) (hcover : Covers Ω S h)
    (hh : 0 ≤ h) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    {k : ℕ} (hk : 0 < k) (hd : ‖y - x‖ ≤ (k : ℝ) * (a - 2 * h)) :
    Reachable S a k x y := by
  classical
  have hsamp : ∀ j : ℕ, ∃ z ∈ S,
      j ≤ k → ‖z - segmentNode x y k j‖ ≤ h := by
    intro j
    by_cases hj : j ≤ k
    · obtain ⟨z, hz, he⟩ := hcover _
        (segmentNode_mem hΩ (hS hx) (hS hy) hk hj)
      exact ⟨z, hz, fun _ => he⟩
    · exact ⟨x, hx, fun hj' => False.elim (hj hj')⟩
  choose r hrs hra using hsamp
  let p : ℕ → E := fun j => if j = 0 then x else if j = k then y else r j
  have hpS : ∀ j ≤ k, p j ∈ S := by
    intro j _
    dsimp [p]
    split_ifs
    · exact hx
    · exact hy
    · exact hrs j
  have hpq : ∀ j ≤ k, ‖p j - segmentNode x y k j‖ ≤ h := by
    intro j hj
    dsimp [p]
    split_ifs with hz ht
    · subst j
      simpa using hh
    · subst j
      simpa [segmentNode_terminal x y hk] using hh
    · exact hra j hj
  refine ⟨p, by simp [p], by simp [p, Nat.ne_of_gt hk], hpS, ?_⟩
  intro j hj
  have hj' := hpq j (Nat.le_of_lt hj)
  have hnext := hpq (j + 1) (Nat.succ_le_of_lt hj)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hstep : ‖segmentNode x y k (j + 1) - segmentNode x y k j‖ =
      ‖y - x‖ / (k : ℝ) := by
    rw [segmentNode_step, norm_smul, Real.norm_of_nonneg (by positivity)]
    ring
  have ht : ‖p (j + 1) - p j‖ ≤
      ‖p (j + 1) - segmentNode x y k (j + 1)‖ +
      ‖segmentNode x y k (j + 1) - segmentNode x y k j‖ +
      ‖p j - segmentNode x y k j‖ := by
    calc
      _ = ‖(p (j + 1) - segmentNode x y k (j + 1)) +
          (segmentNode x y k (j + 1) - segmentNode x y k j) +
          (segmentNode x y k j - p j)‖ := by congr 1; abel
      _ ≤ _ := by
        simpa [norm_sub_rev] using (norm_add₃_le (a :=
          p (j + 1) - segmentNode x y k (j + 1)) (b :=
          segmentNode x y k (j + 1) - segmentNode x y k j) (c :=
          segmentNode x y k j - p j))
  rw [hstep] at ht
  have hd' : ‖y - x‖ / (k : ℝ) ≤ a - 2 * h :=
    (div_le_iff₀ hk').mpr (by nlinarith [hd])
  linarith

omit [NormedSpace ℝ E] in
theorem path_displacement_bound (p : ℕ → E) (a : ℝ) (k : ℕ)
    (h : ∀ j < k, ‖p (j + 1) - p j‖ ≤ a) :
    ‖p k - p 0‖ ≤ (k : ℝ) * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hs := h k (Nat.lt_succ_self k)
    have ht : ‖p (k + 1) - p 0‖ ≤ ‖p (k + 1) - p k‖ + ‖p k - p 0‖ := by
      simpa using norm_add_le (p (k + 1) - p k) (p k - p 0)
    push_cast
    nlinarith

omit [NormedSpace ℝ E] in
theorem reachable_outer {S : Set E} {a : ℝ} {k : ℕ} {x y : E}
    (hr : Reachable S a k x y) : ‖y - x‖ ≤ (k : ℝ) * a := by
  obtain ⟨p, hp0, hpk, _, hstep⟩ := hr
  simpa [hp0, hpk] using path_displacement_bound p a k hstep

omit [NormedSpace ℝ E] in
theorem waiting_path {S : Set E} {a : ℝ} (ha : 0 ≤ a) {x : E}
    (hx : x ∈ S) (k : ℕ) : Reachable S a k x x := by
  exact ⟨fun _ => x, rfl, rfl, fun _ _ => hx, fun _ _ => by simpa using ha⟩

/-- The order predicate retains the actual spatial population and layer. -/
def Precedes {S : Set E} (a : ℝ) (e f : ℕ × S) : Prop :=
  e.1 ≤ f.1 ∧ Reachable S a (f.1 - e.1) e.2 f.2

omit [NormedSpace ℝ E] in
theorem same_site_precedes_iff {S : Set E} {a : ℝ} (ha : 0 ≤ a)
    (x : S) (j l : ℕ) : Precedes a (j, x) (l, x) ↔ j ≤ l := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, waiting_path ha x.property (l - j)⟩

omit [NormedSpace ℝ E] in
theorem same_layer_precedes_iff {S : Set E} {a : ℝ} (ha : 0 ≤ a)
    (j : ℕ) (x y : S) : Precedes a (j, x) (j, y) ↔ x = y := by
  constructor
  · intro h
    obtain ⟨p, hp0, hpk, _, _⟩ := h.2
    apply Subtype.ext
    have hpk' : p 0 = (y : E) := by simpa using hpk
    exact hp0.symm.trans hpk'
  · intro h
    subst y
    exact (same_site_precedes_iff ha x j j).mpr (Nat.le_refl j)

omit [NormedSpace ℝ E] in
/-- Every antichain injects into the spatial population through its site. -/
theorem antichain_site_injective {S : Set E} {a : ℝ} (ha : 0 ≤ a)
    (A : Set (ℕ × S))
    (hA : ∀ e ∈ A, ∀ f ∈ A, Precedes a e f → e = f) :
    Set.InjOn Prod.snd A := by
  intro e he f hf hsite
  rcases e with ⟨j, x⟩
  rcases f with ⟨l, y⟩
  change x = y at hsite
  subst y
  rcases le_total j l with hjl | hlj
  · exact hA _ he _ hf ((same_site_precedes_iff ha x j l).mpr hjl)
  · exact (hA _ hf _ he ((same_site_precedes_iff ha x l j).mpr hlj)).symm

omit [NormedSpace ℝ E] in
theorem finite_antichain_card_le {S : Set E} [Fintype S] {a : ℝ}
    (ha : 0 ≤ a) (A : Finset (ℕ × S))
    (hA : ∀ e ∈ A, ∀ f ∈ A, Precedes a e f → e = f) :
    A.card ≤ Fintype.card S := by
  classical
  have hi := antichain_site_injective ha (A : Set (ℕ × S)) hA
  have hf : Function.Injective (fun e : A => e.val.2) := by
    intro e f hef
    exact Subtype.ext (hi e.property f.property hef)
  simpa using Fintype.card_le_of_injective (fun e : A => e.val.2) hf

/-- The cone speed is relative to the supplied layer duration `a / c`. -/
theorem cone_speed_identity (h a c : ℝ) (ha : 0 < a) (hc : 0 < c) (k : ℕ) :
    (k : ℝ) * (a - 2 * h) =
      c * (1 - 2 * h / a) * ((k : ℝ) * (a / c)) := by
  field_simp

#print axioms covering_constructs_path
#print axioms reachable_outer
#print axioms same_layer_precedes_iff
#print axioms finite_antichain_card_le

end OPH.SourceNetCausalCone

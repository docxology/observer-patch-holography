module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace OPH.SourceRoutingHierarchy

inductive Walk {α : Type*} (edge : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Walk edge 0 a a
  | cons {n : ℕ} {a b c : α} : edge a b → Walk edge n b c → Walk edge (n+1) a c

def Within {α : Type*} (edge : α → α → Prop) (D : ℕ) (a b : α) : Prop :=
  ∃ n, n ≤ D ∧ Walk edge n a b

theorem Walk.append {α : Type*} {edge : α → α → Prop} {n m : ℕ} {a b c : α}
    (ab : Walk edge n a b) (bc : Walk edge m b c) : Walk edge (n+m) a c := by
  induction ab with
  | nil => simpa using bc
  | cons h _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Walk.cons h (ih bc)

theorem Within.trans {α : Type*} {edge : α → α → Prop} {n m : ℕ} {a b c : α}
    (ab : Within edge n a b) (bc : Within edge m b c) : Within edge (n+m) a c := by
  obtain ⟨i, hi, wi⟩ := ab
  obtain ⟨j, hj, wj⟩ := bc
  exact ⟨i+j, by omega, wi.append wj⟩

theorem Within.mono {α : Type*} {edge : α → α → Prop} {n m : ℕ} {a b : α}
    (h : Within edge n a b) (hm : n ≤ m) : Within edge m a b := by
  obtain ⟨i, hi, wi⟩ := h
  exact ⟨i, hi.trans hm, wi⟩

/-- A shared coarse vertex gives an edge between two suitable children;
within one parent all four children are at distance at most one. -/
structure Refinement {A B : Type*} (coarse : A → A → Prop) (fine : B → B → Prop)
    (parent : B → A) : Prop where
  fibre : ∀ x y, parent x = parent y → Within fine 1 x y
  bridge : ∀ a b, coarse a b → ∃ u v, parent u = a ∧ parent v = b ∧ fine u v

theorem lift_walk {A B : Type*} {coarse : A → A → Prop} {fine : B → B → Prop}
    {parent : B → A} (r : Refinement coarse fine parent)
    {n : ℕ} {a b : A} (w : Walk coarse n a b) :
    ∀ x, parent x = a → ∃ y, parent y = b ∧ Within fine (2*n) x y := by
  induction w with
  | nil a =>
    intro x hx
    exact ⟨x, hx, 0, by omega, Walk.nil x⟩
  | @cons n a b c hab tail ih =>
    intro x hx
    obtain ⟨u, v, hu, hv, huv⟩ := r.bridge a b hab
    obtain ⟨y, hy, hvy⟩ := ih v hv
    have hxu := r.fibre x u (hx.trans hu.symm)
    have huv' : Within fine 1 u v := ⟨1, le_rfl, Walk.cons huv (Walk.nil v)⟩
    exact ⟨y, hy, by simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm] using (hxu.trans huv').trans hvy⟩

theorem diameter_lift {A B : Type*} {coarse : A → A → Prop} {fine : B → B → Prop}
    {parent : B → A} (r : Refinement coarse fine parent) (D : ℕ)
    (hD : ∀ a b, Within coarse D a b) : ∀ x y, Within fine (2*D+1) x y := by
  intro x y
  obtain ⟨n, hn, w⟩ := hD (parent x) (parent y)
  obtain ⟨z, hz, hxz⟩ := lift_walk r w x rfl
  exact (hxz.trans (r.fibre z y hz)).mono (by omega)

def envelope (D : ℕ) : ℕ → ℕ
  | 0 => D
  | n+1 => 2*envelope D n + 1

theorem envelope_closed (D n : ℕ) : envelope D n + 1 = (D+1)*2^n := by
  induction n with
  | zero => simp [envelope]
  | succ n ih => simp only [envelope, pow_succ]; nlinarith

theorem tower_diameter {A : ℕ → Type*} (edge : (n : ℕ) → A n → A n → Prop)
    (parent : (n : ℕ) → A (n+1) → A n)
    (refine : ∀ n, Refinement (edge n) (edge (n+1)) (parent n))
    (D : ℕ) (base : ∀ a b, Within (edge 0) D a b) :
    ∀ n a b, Within (edge n) (envelope D n) a b := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact diameter_lift (refine n) (envelope D n) ih

/-- The subdivision stencil is the one used by the captured simulator:
three corner children and one central child. Midpoints are shared by edges. -/
def childVertices {α : Type*} [DecidableEq α] (v m : Fin 3 → α) : Fin 4 → Finset α
  | 0 => {v 0, m 0, m 2}
  | 1 => {v 1, m 1, m 0}
  | 2 => {v 2, m 2, m 1}
  | 3 => {m 0, m 1, m 2}

theorem children_share_vertex {α : Type*} [DecidableEq α] (v m : Fin 3 → α)
    (i j : Fin 4) : ∃ x, x ∈ childVertices v m i ∧ x ∈ childVertices v m j := by
  fin_cases i <;> fin_cases j <;> simp [childVertices]

theorem old_vertex_retained {α : Type*} [DecidableEq α] (v m : Fin 3 → α)
    (i : Fin 3) : v i ∈ childVertices v m ⟨i.val, by omega⟩ := by
  fin_cases i <;> simp [childVertices]

def triangleEdge {A V : Type*} (vertices : A → Fin 3 → V) (a b : A) : Prop :=
  a ≠ b ∧ ∃ i j, vertices a i = vertices b j

def subdividedEdge {A V : Type*} [DecidableEq V]
    (vertices midpoints : A → Fin 3 → V) (x y : A × Fin 4) : Prop :=
  x ≠ y ∧ (childVertices (vertices x.1) (midpoints x.1) x.2 ∩
    childVertices (vertices y.1) (midpoints y.1) y.2).Nonempty

/-- Discharges both refinement hypotheses for the actual four-child stencil.
The midpoint labels may be arbitrary: the upper bound only needs the shared
labels within each parent and the retained coarse vertices between parents. -/
theorem stencil_refinement {A V : Type*} [DecidableEq V]
    (vertices midpoints : A → Fin 3 → V) :
    Refinement (triangleEdge vertices) (subdividedEdge vertices midpoints) Prod.fst := by
  constructor
  · intro x y h
    by_cases he : x = y
    · subst y
      exact ⟨0, by omega, Walk.nil x⟩
    · obtain ⟨z, hx, hy⟩ := children_share_vertex (vertices x.1) (midpoints x.1) x.2 y.2
      have hy' : z ∈ childVertices (vertices y.1) (midpoints y.1) y.2 := by
        simpa only [h] using hy
      exact ⟨1, le_rfl, Walk.cons ⟨he, z, Finset.mem_inter.mpr ⟨hx, hy'⟩⟩ (Walk.nil y)⟩
  · intro a b ⟨hne, i, j, hij⟩
    refine ⟨(a, ⟨i.val, by omega⟩), (b, ⟨j.val, by omega⟩), rfl, rfl, ?_⟩
    constructor
    · exact fun he => hne (congrArg Prod.fst he)
    · refine ⟨vertices a i, Finset.mem_inter.mpr ⟨old_vertex_retained _ _ i, ?_⟩⟩
      rw [hij]
      exact old_vertex_retained _ _ j

/-- Integer faces of the simulator's base icosahedron. Geometry and spherical
coordinates are not used in this adjacency certificate. -/
def baseFace : Fin 20 → Finset ℕ := ![
  {0,11,5}, {0,5,1}, {0,1,7}, {0,7,10}, {0,10,11},
  {1,5,9}, {5,11,4}, {11,10,2}, {10,7,6}, {7,1,8},
  {3,9,4}, {3,4,2}, {3,2,6}, {3,6,8}, {3,8,9},
  {4,9,5}, {2,4,11}, {6,2,10}, {8,6,7}, {9,8,1}]

def baseEdge (a b : Fin 20) : Prop := a ≠ b ∧ (baseFace a ∩ baseFace b).Nonempty

instance (a b : Fin 20) : Decidable (baseEdge a b) := inferInstanceAs
  (Decidable (a ≠ b ∧ (baseFace a ∩ baseFace b).Nonempty))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem base_paths : ∀ a b : Fin 20,
    a = b ∨ baseEdge a b ∨
    (∃ u, baseEdge a u ∧ baseEdge u b) ∨
    (∃ u v, baseEdge a u ∧ baseEdge u v ∧ baseEdge v b) := by
  decide

theorem base_diameter : ∀ a b, Within baseEdge 3 a b := by
  intro a b
  rcases base_paths a b with he | hab | ⟨u, hau, hub⟩ | ⟨u, v, hau, huv, hvb⟩
  · subst b
    exact ⟨0, by omega, Walk.nil a⟩
  · exact ⟨1, by omega, Walk.cons hab (Walk.nil b)⟩
  · exact ⟨2, by omega, Walk.cons hau (Walk.cons hub (Walk.nil b))⟩
  · exact ⟨3, by omega, Walk.cons hau (Walk.cons huv (Walk.cons hvb (Walk.nil b)))⟩

end OPH.SourceRoutingHierarchy

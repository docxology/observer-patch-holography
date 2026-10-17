module
public import Geometry.SourceTemporalTomography
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-!
# Connected support constructs a complete native read plan

Finite connected topology supplies the calibration plan used by the native
tomography theorem. Each phase adds a fresh vertex along supported edges
through the calibrated region. A decreasing complement cardinal proves
termination. This is an existence theorem for exact scalar readout, not
selection of a schedule, a physical instrument or a metric read menu.
-/

set_option autoImplicit false

namespace OPH.SourceTemporalConnected
noncomputable section
open OPH.SourceTemporalTomography

universe u
variable {P : Type u} [DecidableEq P]

def Supported (G : SimpleGraph P) (es : List (P × P)) : Prop :=
  ∀ e ∈ es, G.Adj e.1 e.2

def Rooted (G : SimpleGraph P) (root : P) (K : Finset P) : Prop :=
  ∀ p ∈ K, ∃ vs : List P, (p::vs).Nodup ∧ destination p vs = root ∧
    (∀ q ∈ vs, q ∈ K) ∧ Supported G (route p vs)

omit [DecidableEq P] in
theorem walk_stays [_instDecidableEqP : DecidableEq P] (G : SimpleGraph P) (K : Set P)
    (closed : ∀ a ∈ K, ∀ b, G.Adj a b → b ∈ K)
    {a b : P} (walk : G.Walk a b) (ha : a ∈ K) : b ∈ K := by
  induction walk with
  | nil => exact ha
  | @cons a b c hadj tail ih => exact ih (closed a ha b hadj)

theorem connected_extension (G : SimpleGraph P) (connected : G.Connected)
    (root : P) (K : Finset P) (hr : root ∈ K) (hp : ∃ p, p ∉ K) :
    ∃ u, u ∉ K ∧ ∃ v, v ∈ K ∧ G.Adj u v := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨p,hp⟩ := hp
  apply hp
  apply (connected root p).elim
  intro walk
  apply walk_stays G (K : Set P) ?_ walk hr
  intro a ha b hab
  by_contra hb
  exact hn b hb a ha hab.symm

theorem rooted_insert (G : SimpleGraph P) (root : P) (K : Finset P)
    (hK : Rooted G root K) (u v : P) (hu : u ∉ K) (hv : v ∈ K) (hadj : G.Adj u v) :
    Rooted G root (insert u K) := by
  obtain ⟨vs,hn,he,hk,hs⟩ := hK v hv
  have hnu : (u::v::vs).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hn⟩
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact hu (h ▸ hv)
    · exact hu (hk u h)
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · refine ⟨v::vs,hnu,he,?_,?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Finset.mem_insert_of_mem hv
      · exact Finset.mem_insert_of_mem (hk q hq)
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hadj
      · exact hs e he
  · obtain ⟨ws,hn,he,hk,hs⟩ := hK p hp
    exact ⟨ws,hn,he,fun q hq => Finset.mem_insert_of_mem (hk q hq),hs⟩

/-- Every proper rooted region can be enlarged, and the number of remaining
ports strictly decreases. The resulting plan requires no successful-word
or target-decoder premise. -/
theorem exists_plan [Fintype P] (G : SimpleGraph P) (connected : G.Connected)
    (root : P) (K : Finset P) (hr : root ∈ K) (hK : Rooted G root K) :
    ∃ plan : Plan root (K : Set P), Supported G (lower plan) := by
  classical
  have aux : ∀ n : ℕ, ∀ K : Finset P, Kᶜ.card = n → root ∈ K → Rooted G root K →
      ∃ plan : Plan root (K : Set P), Supported G (lower plan) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K hn hr hK
      by_cases hc : ∀ p, p ∈ K
      · refine ⟨.done (K : Set P) hc,?_⟩
        intro e he
        exact False.elim (List.not_mem_nil he)
      · have hp : ∃ p, p ∉ K := by simpa only [not_forall] using hc
        obtain ⟨u,hu,v,hv,hadj⟩ := connected_extension G connected root K hr hp
        obtain ⟨vs,hvs,hend,hmem,hsupp⟩ := hK v hv
        have hsimple : (u::v::vs).Nodup := by
          refine List.nodup_cons.mpr ⟨?_,hvs⟩
          intro h
          rcases List.mem_cons.mp h with h | h
          · exact hu (h ▸ hv)
          · exact hu (hmem u h)
        have hlt : (insert u K)ᶜ.card < n := by
          rw [← hn,Finset.compl_insert]
          exact Finset.card_erase_lt_of_mem (Finset.mem_compl.mpr hu)
        obtain ⟨next,hnative⟩ : ∃ plan : Plan root (insert u (K : Set P)),
            Supported G (lower plan) := by
          have hex := ih _ hlt (insert u K) rfl
            (Finset.mem_insert_of_mem hr) (rooted_insert G root K hK u v hu hv hadj)
          have heq : ((insert u K : Finset P) : Set P) = insert u (K : Set P) := by
            ext p
            simp
          rw [heq] at hex
          exact hex
        refine ⟨.step (K : Set P) u (v::vs) hu hsimple ?_ hend next,?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hv
          · exact hmem p hp
        · intro e he
          rcases List.mem_append.mp he with he | he
          · rcases List.mem_cons.mp he with rfl | he
            · exact hadj
            · exact hsupp e he
          · exact hnative e he
  exact aux Kᶜ.card K rfl hr hK

/-- From connected topology alone, a supported native word and one-receiver
observation protocol distinguish all exact initial scalar states. -/
theorem connected_native_completion [Fintype P] (G : SimpleGraph P)
    (connected : G.Connected) (root : P) :
    ∃ plan : Plan root {root}, Supported G (lower plan) ∧
      Function.Injective (completionSamples plan) := by
  have hroot : Rooted G root {root} := by
    intro p hp
    have he : p = root := Finset.mem_singleton.mp hp
    subst p
    refine ⟨[],by simp,rfl,?_,?_⟩
    · simp
    · intro e he
      exact False.elim (List.not_mem_nil he)
  obtain ⟨plan,hp⟩ : ∃ plan : Plan root {root}, Supported G (lower plan) := by
    have hex := exists_plan G connected root {root} (by simp) hroot
    have heq : (({root} : Finset P) : Set P) = {root} := by ext p; simp
    rw [heq] at hex
    exact hex
  exact ⟨plan,hp,completion_injective plan⟩

end
end OPH.SourceTemporalConnected

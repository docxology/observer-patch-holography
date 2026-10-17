module
public import Geometry.SourceNetCausalCone

@[expose] public section

set_option autoImplicit false

/-!
# The layered event order of a read law

INPUTS.  A type `S` of sites; a step relation `step : S → S → Prop`, the
read law, where `step x y` says that an event at site `y` reads an event at
site `x` one layer earlier; and the layer rule that every read advances the
layer by exactly one.  Waiting is the same-site read, so the statements that
use waiting take reflexivity of `step` as an explicit hypothesis.  Symmetry
of the read law is recorded in `ReadLaw` and proved for the concrete ball
law; none of the order statements use it.

WHAT IS PROVED.  `Walk step k x y` is a `k`-step walk of the read law.
`LayerPrec step (j, x) (j', y)` holds when `j ≤ j'` and a `(j' - j)`-step
walk joins the sites.  With no hypothesis on `step`, the relation is a
partial order (`layerPrec_isPartialOrder`, packaged as the `PartialOrder`
instance on `Event step`) and it is the reflexive transitive closure of the
one-layer reads `(j, x) → (j + 1, y)` with `step x y`
(`layerPrec_iff_reflTransGen`).  Under reflexivity, walks are monotone in
their length (`Walk.succ`, `Walk.mono`), the graph distance `walkDist` is
the least walk length (`walk_iff_walkDist_le`), and a `k`-step walk exists
exactly when a shortest walk of length at most `k` exists
(`walk_iff_shortest`).  Every layer is an antichain, every antichain injects
into the sites through its site coordinate, and the width of the finite
layered poset is the number of sites, also inside every layer window
(`width_eq_card_sites`, `width_eq_card_sites_window`).  Every event at layer
`j` has height `j`: strict chains from layer zero to the event have at most
`j` steps, one-layer read chains have exactly `j` steps, and the waiting
chain attains `j` (`height_eq_layer`, `readChain_length`).  The concrete
ball read law of `Geometry/SourceNetCausalCone.lean` is an instance:
`Reachable S a k x y` is `Walk` for the step `‖v - u‖ ≤ a`
(`reachable_iff_walk`) and `Precedes a` is `LayerPrec`
(`precedes_iff_layerPrec`), so every statement above transfers to that
order.

NOT CLAIMED.  No physical clock is identified; the layer index is the model
clock of the supplied construction.  The population of sites and the read
law are inputs; nothing here selects them by native repair.  No manifold,
volume law or continuum limit is reconstructed; those limit statements are
analytic and live in the paper.
-/

namespace OPH.SourceNetLayeredOrder

open Relation

variable {S : Type*}

/-- A read law: waiting is permitted and reads are symmetric. -/
structure ReadLaw (step : S → S → Prop) : Prop where
  refl : ∀ x, step x x
  symm : ∀ x y, step x y → step y x

/-- A `k`-step walk of the read law from `x` to `y`. -/
inductive Walk (step : S → S → Prop) : ℕ → S → S → Prop
  | nil (x : S) : Walk step 0 x x
  | cons {k : ℕ} {x y z : S} (hxy : step x y) (hw : Walk step k y z) :
      Walk step (k + 1) x z

namespace Walk

variable {step : S → S → Prop}

theorem zero_eq {x y : S} (h : Walk step 0 x y) : x = y := by
  cases h
  rfl

theorem succ_iff {k : ℕ} {x z : S} :
    Walk step (k + 1) x z ↔ ∃ y, step x y ∧ Walk step k y z := by
  constructor
  · intro h
    cases h with
    | cons hxy hw => exact ⟨_, hxy, hw⟩
  · rintro ⟨y, hxy, hw⟩
    exact Walk.cons hxy hw

/-- Walks concatenate; lengths add. -/
theorem append {k : ℕ} {x y : S} (h₁ : Walk step k x y) :
    ∀ {l : ℕ} {z : S}, Walk step l y z → Walk step (k + l) x z := by
  induction h₁ with
  | nil x =>
    intro l z h₂
    simpa using h₂
  | cons hxy _ ih =>
    intro l z h₂
    rw [Nat.add_right_comm]
    exact Walk.cons hxy (ih h₂)

/-- Waiting: under reflexivity every site walks to itself in any length. -/
theorem wait (hrefl : ∀ x, step x x) (x : S) (k : ℕ) : Walk step k x x := by
  induction k with
  | zero => exact Walk.nil x
  | succ k ih => exact Walk.cons (hrefl x) ih

/-- One waiting step at the end lengthens a walk. -/
theorem succ (hrefl : ∀ x, step x x) {k : ℕ} {x y : S}
    (h : Walk step k x y) : Walk step (k + 1) x y :=
  h.append (Walk.cons (hrefl y) (Walk.nil y))

/-- Walks are monotone in their length. -/
theorem mono (hrefl : ∀ x, step x x) {k l : ℕ} (hkl : k ≤ l) {x y : S}
    (h : Walk step k x y) : Walk step l x y := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact Walk.succ hrefl ih

end Walk

section Distance

variable {step : S → S → Prop}

open scoped Classical in
/-- The graph distance: the least walk length, given that a walk exists. -/
noncomputable def walkDist (step : S → S → Prop) {x y : S}
    (h : ∃ k, Walk step k x y) : ℕ :=
  Nat.find h

open scoped Classical in
theorem walkDist_spec {x y : S} (h : ∃ k, Walk step k x y) :
    Walk step (walkDist step h) x y :=
  Nat.find_spec h

open scoped Classical in
theorem walkDist_le {x y : S} (h : ∃ k, Walk step k x y) {k : ℕ}
    (hk : Walk step k x y) : walkDist step h ≤ k :=
  Nat.find_min' h hk

open scoped Classical in
theorem not_walk_of_lt_walkDist {x y : S} (h : ∃ k, Walk step k x y)
    {m : ℕ} (hm : m < walkDist step h) : ¬ Walk step m x y :=
  Nat.find_min h hm

/-- With waiting, a `k`-step walk exists exactly when the distance is at most `k`. -/
theorem walk_iff_walkDist_le (hrefl : ∀ x, step x x) {x y : S}
    (h : ∃ k, Walk step k x y) (k : ℕ) :
    Walk step k x y ↔ walkDist step h ≤ k := by
  constructor
  · exact walkDist_le h
  · intro hk
    exact Walk.mono hrefl hk (walkDist_spec h)

/-- Shortest walks: the distance characterization without naming the distance. -/
theorem walk_iff_shortest (hrefl : ∀ x, step x x) {k : ℕ} {x y : S} :
    Walk step k x y ↔
      ∃ m, m ≤ k ∧ Walk step m x y ∧ ∀ m' < m, ¬ Walk step m' x y := by
  constructor
  · intro hk
    have h : ∃ k, Walk step k x y := ⟨k, hk⟩
    exact ⟨walkDist step h, walkDist_le h hk, walkDist_spec h,
      fun _ hm => not_walk_of_lt_walkDist h hm⟩
  · rintro ⟨m, hmk, hm, _⟩
    exact Walk.mono hrefl hmk hm

end Distance

/-- The layered relation: `j ≤ j'` and a `(j' - j)`-step walk between the sites. -/
def LayerPrec (step : S → S → Prop) (e f : ℕ × S) : Prop :=
  e.1 ≤ f.1 ∧ Walk step (f.1 - e.1) e.2 f.2

/-- The one-layer read: an event at layer `j + 1` reads a permitted site at layer `j`. -/
def Read (step : S → S → Prop) (e f : ℕ × S) : Prop :=
  f.1 = e.1 + 1 ∧ step e.2 f.2

section Order

variable {step : S → S → Prop}

theorem layerPrec_refl (e : ℕ × S) : LayerPrec step e e := by
  refine ⟨le_rfl, ?_⟩
  rw [Nat.sub_self]
  exact Walk.nil e.2

theorem layerPrec_trans {e f g : ℕ × S} (h₁ : LayerPrec step e f)
    (h₂ : LayerPrec step f g) : LayerPrec step e g := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  have hw := h₁.2.append h₂.2
  have e' : f.1 - e.1 + (g.1 - f.1) = g.1 - e.1 := by
    have := h₁.1
    have := h₂.1
    omega
  rw [e'] at hw
  exact hw

theorem layerPrec_antisymm {e f : ℕ × S} (h₁ : LayerPrec step e f)
    (h₂ : LayerPrec step f e) : e = f := by
  have hj : e.1 = f.1 := le_antisymm h₁.1 h₂.1
  have hw := h₁.2
  rw [hj, Nat.sub_self] at hw
  exact Prod.ext hj hw.zero_eq

/-- The layered relation is a partial order with no hypothesis on the read law. -/
theorem layerPrec_isPartialOrder (step : S → S → Prop) :
    IsPartialOrder (ℕ × S) (LayerPrec step) where
  refl := layerPrec_refl
  trans := fun _ _ _ => layerPrec_trans
  antisymm := fun _ _ => layerPrec_antisymm

end Order

/-- The events of a read law: a layer and a site. -/
structure Event (step : S → S → Prop) where
  layer : ℕ
  site : S

/-- The layered order as a `PartialOrder` on the events. -/
instance (step : S → S → Prop) : PartialOrder (Event step) where
  le e f := LayerPrec step (e.layer, e.site) (f.layer, f.site)
  le_refl e := layerPrec_refl _
  le_trans _ _ _ := layerPrec_trans
  le_antisymm e f h₁ h₂ := by
    have h := layerPrec_antisymm h₁ h₂
    cases e
    cases f
    simp only [Prod.mk.injEq] at h
    rw [h.1, h.2]

theorem event_le_iff (step : S → S → Prop) (e f : Event step) :
    e ≤ f ↔ LayerPrec step (e.layer, e.site) (f.layer, f.site) :=
  Iff.rfl

section Closure

variable {step : S → S → Prop}

/-- A walk of `k` steps lifts to a chain of `k` one-layer reads. -/
theorem walk_reflTransGen {k : ℕ} :
    ∀ {x y : S}, Walk step k x y → ∀ j : ℕ,
      ReflTransGen (Read step) (j, x) (j + k, y) := by
  induction k with
  | zero =>
    intro x y h j
    obtain rfl := h.zero_eq
    simpa using (ReflTransGen.refl : ReflTransGen (Read step) (j, x) (j, x))
  | succ k ih =>
    intro x z h j
    obtain ⟨y, hxy, hw⟩ := Walk.succ_iff.mp h
    have hr : Read step (j, x) (j + 1, y) := ⟨rfl, hxy⟩
    have e : j + (k + 1) = j + 1 + k := by omega
    rw [e]
    exact ReflTransGen.head hr (ih hw (j + 1))

/-- One further read extends layered precedence. -/
theorem layerPrec_read {e f g : ℕ × S} (h : LayerPrec step e f)
    (hr : Read step f g) : LayerPrec step e g := by
  obtain ⟨hle, hw⟩ := h
  obtain ⟨hlayer, hstep⟩ := hr
  refine ⟨by omega, ?_⟩
  have hw' := hw.append (Walk.cons hstep (Walk.nil g.2))
  have e' : g.1 - e.1 = f.1 - e.1 + (0 + 1) := by omega
  rw [e']
  exact hw'

/-- The event order is the reflexive transitive closure of the one-layer reads. -/
theorem layerPrec_iff_reflTransGen (e f : ℕ × S) :
    LayerPrec step e f ↔ ReflTransGen (Read step) e f := by
  constructor
  · rintro ⟨hle, hw⟩
    have h := walk_reflTransGen hw e.1
    rw [Nat.add_sub_of_le hle] at h
    simpa using h
  · intro h
    induction h with
    | refl => exact layerPrec_refl e
    | tail _ hbc ih => exact layerPrec_read ih hbc

end Closure

section Antichains

variable {step : S → S → Prop}

theorem same_layer_iff (j : ℕ) (x y : S) :
    LayerPrec step (j, x) (j, y) ↔ x = y := by
  constructor
  · intro h
    have hw := h.2
    rw [Nat.sub_self] at hw
    exact hw.zero_eq
  · intro h
    subst h
    exact layerPrec_refl _

theorem same_site_iff (hrefl : ∀ x, step x x) (x : S) (j l : ℕ) :
    LayerPrec step (j, x) (l, x) ↔ j ≤ l := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, Walk.wait hrefl x (l - j)⟩

/-- Antichains of the layered order. -/
def IsAntichainL (step : S → S → Prop) (A : Set (ℕ × S)) : Prop :=
  ∀ e ∈ A, ∀ f ∈ A, LayerPrec step e f → e = f

/-- Every layer is an antichain. -/
theorem layer_isAntichain (j : ℕ) :
    IsAntichainL step {e : ℕ × S | e.1 = j} := by
  intro e he f hf h
  rcases e with ⟨je, x⟩
  rcases f with ⟨jf, y⟩
  change je = j at he
  change jf = j at hf
  subst he
  subst hf
  rw [(same_layer_iff _ x y).mp h]

/-- Every antichain injects into the sites through its site coordinate. -/
theorem antichain_site_injOn (hrefl : ∀ x, step x x) (A : Set (ℕ × S))
    (hA : IsAntichainL step A) : Set.InjOn Prod.snd A := by
  intro e he f hf hsite
  rcases e with ⟨j, x⟩
  rcases f with ⟨l, y⟩
  change x = y at hsite
  subst hsite
  rcases le_total j l with hjl | hlj
  · exact hA _ he _ hf ((same_site_iff hrefl x j l).mpr hjl)
  · exact (hA _ hf _ he ((same_site_iff hrefl x l j).mpr hlj)).symm

theorem antichain_card_le [Fintype S] (hrefl : ∀ x, step x x)
    (A : Finset (ℕ × S)) (hA : IsAntichainL step (A : Set (ℕ × S))) :
    A.card ≤ Fintype.card S := by
  classical
  have h := Finset.card_le_card_of_injOn (s := A) (t := Finset.univ) Prod.snd
    (fun _ _ => Finset.mem_univ _) (antichain_site_injOn hrefl _ hA)
  simpa using h

/-- Layer zero as a finite set of events. -/
def layerZero (S : Type*) [Fintype S] : Finset (ℕ × S) :=
  Finset.univ.map ⟨fun x => (0, x), fun _ _ h => (Prod.mk.inj h).2⟩

theorem layerZero_card (S : Type*) [Fintype S] :
    (layerZero S).card = Fintype.card S := by
  simp [layerZero]

theorem mem_layerZero [Fintype S] (e : ℕ × S) :
    e ∈ layerZero S ↔ e.1 = 0 := by
  rcases e with ⟨j, x⟩
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_map.mp h
    exact (congrArg Prod.fst ha).symm
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨x, Finset.mem_univ x, ?_⟩
    change j = 0 at h
    subst j
    rfl

theorem layerZero_isAntichain [Fintype S] :
    IsAntichainL step ((layerZero S : Finset (ℕ × S)) : Set (ℕ × S)) := by
  intro e he f hf h
  have he' : e.1 = 0 := (mem_layerZero e).mp he
  have hf' : f.1 = 0 := (mem_layerZero f).mp hf
  exact layer_isAntichain 0 e he' f hf' h

/-- The width of the layered poset is the number of sites. -/
theorem width_eq_card_sites [Fintype S] (hrefl : ∀ x, step x x) :
    IsGreatest {n : ℕ | ∃ A : Finset (ℕ × S),
      IsAntichainL step (A : Set (ℕ × S)) ∧ A.card = n} (Fintype.card S) := by
  constructor
  · exact ⟨layerZero S, layerZero_isAntichain, layerZero_card S⟩
  · rintro n ⟨A, hA, rfl⟩
    exact antichain_card_le hrefl A hA

/-- The width statement inside every layer window `0, …, K`. -/
theorem width_eq_card_sites_window [Fintype S] (hrefl : ∀ x, step x x) (K : ℕ) :
    IsGreatest {n : ℕ | ∃ A : Finset (ℕ × S), (∀ e ∈ A, e.1 ≤ K) ∧
      IsAntichainL step (A : Set (ℕ × S)) ∧ A.card = n} (Fintype.card S) := by
  constructor
  · refine ⟨layerZero S, ?_, layerZero_isAntichain, layerZero_card S⟩
    intro e he
    rw [(mem_layerZero e).mp he]
    exact Nat.zero_le K
  · rintro n ⟨A, _, hA, rfl⟩
    exact antichain_card_le hrefl A hA

end Antichains

section Height

variable {step : S → S → Prop}

/-- Strict layered precedence. -/
def StrictLayerPrec (step : S → S → Prop) (e f : ℕ × S) : Prop :=
  LayerPrec step e f ∧ e ≠ f

/-- A strict step raises the layer. -/
theorem strict_layer_lt {e f : ℕ × S} (h : StrictLayerPrec step e f) :
    e.1 < f.1 := by
  rcases Nat.lt_or_ge e.1 f.1 with hlt | hge
  · exact hlt
  · exfalso
    apply h.2
    have hj : e.1 = f.1 := le_antisymm h.1.1 hge
    have hw := h.1.2
    rw [hj, Nat.sub_self] at hw
    exact Prod.ext hj hw.zero_eq

/-- A strict chain of `n` steps: consecutive terms are strictly ordered. -/
def IsStrictChain (step : S → S → Prop) (c : ℕ → ℕ × S) (n : ℕ) : Prop :=
  ∀ i < n, StrictLayerPrec step (c i) (c (i + 1))

/-- A chain of one-layer reads. -/
def IsReadChain (step : S → S → Prop) (c : ℕ → ℕ × S) (n : ℕ) : Prop :=
  ∀ i < n, Read step (c i) (c (i + 1))

theorem strictChain_layer_ge (c : ℕ → ℕ × S) (n : ℕ)
    (hc : IsStrictChain step c n) : (c 0).1 + n ≤ (c n).1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have h2 := strict_layer_lt (hc n (Nat.lt_succ_self n))
    omega

/-- Strict chains from layer zero to an event at layer `j` have at most `j` steps. -/
theorem strictChain_length_le (c : ℕ → ℕ × S) (n : ℕ)
    (hc : IsStrictChain step c n) (h0 : (c 0).1 = 0) : n ≤ (c n).1 := by
  have := strictChain_layer_ge c n hc
  omega

theorem readChain_layer (c : ℕ → ℕ × S) (n : ℕ) (hc : IsReadChain step c n) :
    (c n).1 = (c 0).1 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    have h2 := (hc n (Nat.lt_succ_self n)).1
    omega

/-- Read chains from layer zero to an event at layer `j` have exactly `j` steps. -/
theorem readChain_length (c : ℕ → ℕ × S) (n j : ℕ) (hc : IsReadChain step c n)
    (h0 : (c 0).1 = 0) (hn : (c n).1 = j) : n = j := by
  have := readChain_layer c n hc
  omega

/-- The waiting chain at a site, read by read. -/
theorem waiting_readChain (hrefl : ∀ x, step x x) (x : S) (n : ℕ) :
    IsReadChain step (fun i => (i, x)) n :=
  fun _ _ => ⟨rfl, hrefl x⟩

theorem waiting_strictChain (hrefl : ∀ x, step x x) (x : S) (n : ℕ) :
    IsStrictChain step (fun i => (i, x)) n := by
  intro i _
  refine ⟨(same_site_iff hrefl x i (i + 1)).mpr (Nat.le_succ i), ?_⟩
  intro h
  have := (Prod.mk.inj h).1
  omega

/-- Every event at layer `j` has height `j`: the longest strict chain from
layer zero has `j` steps, attained by the waiting chain. -/
theorem height_eq_layer (hrefl : ∀ x, step x x) (j : ℕ) (x : S) :
    IsGreatest {n : ℕ | ∃ c : ℕ → ℕ × S,
      IsStrictChain step c n ∧ (c 0).1 = 0 ∧ c n = (j, x)} j := by
  constructor
  · exact ⟨fun i => (i, x), waiting_strictChain hrefl x j, rfl, rfl⟩
  · rintro n ⟨c, hc, h0, hn⟩
    have := strictChain_length_le c n hc h0
    rw [hn] at this
    exact this

end Height

section Concrete

open OPH.SourceNetCausalCone

variable {E : Type*} [NormedAddCommGroup E]

/-- The ball read law on the population `S`: reads within edge radius `a`. -/
def ballStep (S : Set E) (a : ℝ) (u v : S) : Prop := ‖(v : E) - u‖ ≤ a

theorem ballStep_readLaw (S : Set E) {a : ℝ} (ha : 0 ≤ a) :
    ReadLaw (ballStep S a) where
  refl := fun x => by simp [ballStep, ha]
  symm := fun x y h => by
    unfold ballStep at h ⊢
    rw [norm_sub_rev]
    exact h

/-- The concrete path relation is the abstract walk relation of the ball law. -/
theorem reachable_iff_walk (S : Set E) (a : ℝ) (k : ℕ) (x y : S) :
    Reachable S a k (x : E) y ↔ Walk (ballStep S a) k x y := by
  constructor
  · intro h
    induction k generalizing x with
    | zero =>
      obtain ⟨p, hp0, hpk, _, _⟩ := h
      have hxy : x = y := Subtype.ext (hp0.symm.trans hpk)
      subst hxy
      exact Walk.nil x
    | succ k ih =>
      obtain ⟨p, hp0, hpk, hpS, hstep⟩ := h
      let y1 : S := ⟨p 1, hpS 1 (by omega)⟩
      refine Walk.cons (y := y1) ?_ (ih y1 ?_)
      · show ‖p 1 - (x : E)‖ ≤ a
        rw [← hp0]
        exact hstep 0 (by omega)
      · exact ⟨fun j => p (j + 1), rfl, hpk, fun j hj => hpS (j + 1) (by omega),
          fun j hj => hstep (j + 1) (by omega)⟩
  · intro h
    induction k generalizing x with
    | zero =>
      obtain rfl := h.zero_eq
      exact ⟨fun _ => x, rfl, rfl, fun _ _ => x.2, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨y1, hxy, hw⟩ := Walk.succ_iff.mp h
      obtain ⟨p, hp0, hpk, hpS, hstep⟩ := ih y1 hw
      refine ⟨fun j => match j with | 0 => (x : E) | i + 1 => p i, rfl, hpk, ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => exact x.2
        | succ i => exact hpS i (by omega)
      · intro j hj
        cases j with
        | zero =>
          show ‖p 0 - (x : E)‖ ≤ a
          rw [hp0]
          exact hxy
        | succ i => exact hstep i (by omega)

/-- The paper's `Precedes` is the abstract layered order of the ball law. -/
theorem precedes_iff_layerPrec (S : Set E) (a : ℝ) (e f : ℕ × S) :
    Precedes a e f ↔ LayerPrec (ballStep S a) e f :=
  and_congr_right fun _ => reachable_iff_walk S a (f.1 - e.1) e.2 f.2

/-- The concrete order is a partial order. -/
theorem precedes_isPartialOrder (S : Set E) (a : ℝ) :
    IsPartialOrder (ℕ × S) (Precedes a) where
  refl := fun e => (precedes_iff_layerPrec S a e e).mpr (layerPrec_refl e)
  trans := fun e f g h₁ h₂ => (precedes_iff_layerPrec S a e g).mpr
    (layerPrec_trans ((precedes_iff_layerPrec S a e f).mp h₁)
      ((precedes_iff_layerPrec S a f g).mp h₂))
  antisymm := fun e f h₁ h₂ => layerPrec_antisymm
    ((precedes_iff_layerPrec S a e f).mp h₁) ((precedes_iff_layerPrec S a f e).mp h₂)

/-- The concrete order is the reflexive transitive closure of the ball reads. -/
theorem precedes_iff_reflTransGen (S : Set E) (a : ℝ) (e f : ℕ × S) :
    Precedes a e f ↔ ReflTransGen (Read (ballStep S a)) e f :=
  (precedes_iff_layerPrec S a e f).trans (layerPrec_iff_reflTransGen e f)

/-- The concrete width statement: every finite population has width `|S|`. -/
theorem precedes_width_eq_card (S : Set E) [Fintype S] {a : ℝ} (ha : 0 ≤ a) :
    IsGreatest {n : ℕ | ∃ A : Finset (ℕ × S),
      (∀ e ∈ A, ∀ f ∈ A, Precedes a e f → e = f) ∧ A.card = n} (Fintype.card S) := by
  have hrefl : ∀ x : S, ballStep S a x x := (ballStep_readLaw S ha).refl
  constructor
  · refine ⟨layerZero S, ?_, layerZero_card S⟩
    intro e he f hf hef
    exact layerZero_isAntichain (step := ballStep S a) e he f hf
      ((precedes_iff_layerPrec S a e f).mp hef)
  · rintro n ⟨A, hA, rfl⟩
    refine antichain_card_le hrefl A ?_
    intro e he f hf hef
    exact hA e he f hf ((precedes_iff_layerPrec S a e f).mpr hef)

end Concrete

#print axioms layerPrec_isPartialOrder
#print axioms layerPrec_iff_reflTransGen
#print axioms walk_iff_shortest
#print axioms walk_iff_walkDist_le
#print axioms width_eq_card_sites
#print axioms width_eq_card_sites_window
#print axioms height_eq_layer
#print axioms readChain_length
#print axioms reachable_iff_walk
#print axioms precedes_iff_layerPrec
#print axioms precedes_iff_reflTransGen
#print axioms precedes_width_eq_card

end OPH.SourceNetLayeredOrder

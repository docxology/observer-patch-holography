module
public import ObserverPatchHolography.ScalarSeamRepair

@[expose] public section

/-!
# Reusable classical transport with declared local feedback

Local immutable-record export, a local zero reset, and factor-two readback
are supplied operations. They are not derived from the canonical pair mean.
The exact hop has unit signal gain; bounded additive errors accumulate
linearly. A labelled semantic read-from refinement preserves the logical
order when its local edge conditions and finite read paths are certified.

The labels say nothing about physical causality. Version sequencing,
write-after-write order and hash-chain order are not semantic read inputs.
No quantum operation, physical clock or source-selected read law is proved.
-/

namespace OPH.SourceFeedbackTransport

noncomputable section

def receive (payload exportError resetError meanError readError decodeError : ℝ) : ℝ :=
  2 * (((payload + exportError + resetError) / 2 + meanError) + readError) + decodeError

theorem receive_error_identity (x e r m s a : ℝ) :
    receive x e r m s a - x = e + r + 2 * m + 2 * s + a := by
  unfold receive
  ring

theorem exact_receive (x : ℝ) : receive x 0 0 0 0 0 = x := by
  unfold receive
  ring

theorem unit_signal_gain (x y e r m s a : ℝ) :
    receive x e r m s a - receive y e r m s a = x - y := by
  unfold receive
  ring

def route (x : ℝ) : List (ℝ × ℝ × ℝ × ℝ × ℝ) → ℝ
  | [] => x
  | (e,r,m,s,a) :: tail => route (receive x e r m s a) tail

def hopError (errors : ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  errors.1 + errors.2.1 + 2 * errors.2.2.1 + 2 * errors.2.2.2.1 + errors.2.2.2.2

theorem route_error_identity (x : ℝ) (errors : List (ℝ × ℝ × ℝ × ℝ × ℝ)) :
    route x errors - x = (errors.map hopError).sum := by
  induction errors generalizing x with
  | nil => simp [route]
  | cons head tail ih =>
    rcases head with ⟨e,r,m,s,a⟩
    have h := ih (receive x e r m s a)
    have hhop := receive_error_identity x e r m s a
    simp only [route, List.map_cons, List.sum_cons, hopError]
    linarith

theorem route_error_bound (x : ℝ) (errors : List (ℝ × ℝ × ℝ × ℝ × ℝ)) :
    |route x errors - x| ≤ (errors.map fun t => |hopError t|).sum := by
  rw [route_error_identity]
  induction errors with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)

theorem bounded_hop_error (e r m s a E R M S A : ℝ)
    (he : |e| ≤ E) (hr : |r| ≤ R) (hm : |m| ≤ M)
    (hs : |s| ≤ S) (ha : |a| ≤ A) :
    |hopError (e,r,m,s,a)| ≤ E + R + 2*M + 2*S + A := by
  have h1 := abs_add_le e r
  have h2 := abs_add_le (e+r) (2*m)
  have h3 := abs_add_le (e+r+2*m) (2*s)
  have h4 := abs_add_le (e+r+2*m+2*s) a
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h2 h3
  simp only [hopError]
  linarith

theorem route_uniform_bound (x B : ℝ) (errors : List (ℝ × ℝ × ℝ × ℝ × ℝ))
    (h : ∀ t ∈ errors, |hopError t| ≤ B) :
    |route x errors - x| ≤ errors.length * B := by
  have hs : ∀ ts : List (ℝ × ℝ × ℝ × ℝ × ℝ),
      (∀ t ∈ ts, |hopError t| ≤ B) →
      (ts.map fun t => |hopError t|).sum ≤ ts.length * B := by
    intro ts
    induction ts with
    | nil => intro _; simp
    | cons head tail ih =>
      intro hb
      have hh := hb head (by simp)
      have ht := ih (by
        intro t ht
        exact hb t (by simp [ht]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith
  exact (route_error_bound x errors).trans (hs errors h)

theorem sharp_uniform_error (x E R M S A : ℝ) (d : ℕ) :
    route x (List.replicate d (E,R,M,S,A)) - x =
      d * (E + R + 2*M + 2*S + A) := by
  rw [route_error_identity]
  simp [List.map_replicate, List.sum_replicate, hopError, nsmul_eq_mul]
  ring

theorem repeated_exact_hops (x : ℝ) (d : ℕ) :
    route x (List.replicate d (0,0,0,0,0)) = x := by
  induction d with
  | zero => rfl
  | succ d ih => simpa [List.replicate_succ, route, exact_receive] using ih

/-- `none` labels initialization and constant resets; a nonconstant event
is labelled by the logical version from which its payload descends. -/
def Below {α : Type*} (r : α → α → Prop) : Option α → Option α → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => Relation.ReflTransGen r a b

theorem below_refl {α : Type*} (r : α → α → Prop) (a : Option α) : Below r a a := by
  cases a with
  | none => trivial
  | some a => exact Relation.ReflTransGen.refl

theorem below_trans {α : Type*} (r : α → α → Prop) {a b c : Option α}
    (hab : Below r a b) (hbc : Below r b c) : Below r a c := by
  cases a with
  | none => trivial
  | some a =>
    cases b with
    | none => exact False.elim hab
    | some b =>
      cases c with
      | none => exact False.elim hbc
      | some c => exact hab.trans hbc

/-- Local certificate checks suffice for every retained operational path. -/
theorem semantic_projection_sound {α β : Type*} (logical : α → α → Prop)
    (operational : β → β → Prop) (label : β → Option α)
    (hedges : ∀ u v, operational u v → Below logical (label u) (label v))
    {u v : β} (hpath : Relation.ReflTransGen operational u v) :
    Below logical (label u) (label v) := by
  induction hpath with
  | refl => exact below_refl logical _
  | @tail v w _ hvw ih => exact below_trans logical ih (hedges v w hvw)

/-- A concrete compiler supplies a finite retained path for each requested
logical read; no claim that the requested reads themselves are selected. -/
theorem semantic_projection_complete {α β : Type*} (logical : α → α → Prop)
    (operational : β → β → Prop) (embed : α → β)
    (hlift : ∀ a b, logical a b → Relation.ReflTransGen operational (embed a) (embed b))
    {a b : α} (hpath : Relation.ReflTransGen logical a b) :
    Relation.ReflTransGen operational (embed a) (embed b) := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.trans (hlift b c hbc)

theorem exact_induced_logical_order {α β : Type*} (logical : α → α → Prop)
    (operational : β → β → Prop) (embed : α → β) (label : β → Option α)
    (hsection : ∀ a, label (embed a) = some a)
    (hedges : ∀ u v, operational u v → Below logical (label u) (label v))
    (hlift : ∀ a b, logical a b → Relation.ReflTransGen operational (embed a) (embed b))
    (a b : α) :
    Relation.ReflTransGen operational (embed a) (embed b) ↔
      Relation.ReflTransGen logical a b := by
  constructor
  · intro h
    have hs := semantic_projection_sound logical operational label hedges h
    simpa [hsection, Below] using hs
  · exact semantic_projection_complete logical operational embed hlift

end

end OPH.SourceFeedbackTransport

#print axioms OPH.SourceFeedbackTransport.route_error_bound
#print axioms OPH.SourceFeedbackTransport.exact_induced_logical_order

module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# Live logical versions in a fixed local working store

The specified layered program consumes only the preceding payload layer. A
source's pruned multicast tree is completed before the next source starts.
Thus two payload banks and one relay slot per carrier suffice. These are
scalar slots, not fixed-bit words; the controller and retained event log are
separate. Local read/write feedback and the lifetime discipline are explicit.
No canonical pair-mean selection or arbitrary historical-read service follows.
-/

namespace OPH.SourceRoutingStorage

inductive Register (C : ℕ) where
  | scratch (owner : Fin C) (port : Fin 12)
  | zero (owner : Fin C)
  | address (owner : Fin C) (axis : Fin 6)
  | accumulator (owner : Fin C)
  | payload (layer : ℕ) (owner : Fin C)
  | relay (layer source : ℕ) (owner : Fin C)
  deriving DecidableEq

def owner {C : ℕ} : Register C → Fin C
  | .scratch c _ | .zero c | .address c _ | .accumulator c
  | .payload _ c | .relay _ _ c => c

def index {C : ℕ} : Register C → Fin 23
  | .scratch _ p => ⟨p.val, by omega⟩
  | .zero _ => 12
  | .address _ a => ⟨13 + a.val, by omega⟩
  | .accumulator _ => 19
  | .payload t _ => ⟨20 + t % 2, by omega⟩
  | .relay _ _ _ => 22

def slot {C : ℕ} (r : Register C) : Fin C × Fin 23 := (owner r, index r)

/-- An upper bound on the live set during source `s` of the layer consuming
payload `k` and producing payload `k+1`. Actual allocated live sets may be
smaller, particularly before the first write to the next bank. -/
def Live {C : ℕ} (k s : ℕ) : Register C → Prop
  | .payload t _ => t = k ∨ t = k + 1
  | .relay t u _ => t = k ∧ u = s
  | _ => True

/-- Reuse never aliases distinct simultaneously live logical registers. -/
theorem live_slot_injective {C k s : ℕ} {a b : Register C}
    (ha : Live k s a) (hb : Live k s b) (h : slot a = slot b) : a = b := by
  have ho := congrArg Prod.fst h
  have hi := congrArg (fun x : Fin C × Fin 23 => x.2.val) h
  cases a <;> cases b <;>
    simp_all [slot, owner, index, Live, Fin.ext_iff] <;> omega

/-- Every read uses the owner's own physical carrier. -/
theorem slot_owner {C : ℕ} (r : Register C) : (slot r).1 = owner r := rfl

def Realizes {C : ℕ} {V : Type*} (active : Register C → Prop)
    (logical : Register C → V) (physical : (Fin C × Fin 23) → V) : Prop :=
  ∀ r, active r → physical (slot r) = logical r

/-- One physical write refines the logical write when the active versions obey
the derived lifetime coloring. Retired versions need not be retained. -/
theorem write_realizes {C k s : ℕ} {V : Type*}
    (active : Register C → Prop) (logical : Register C → V)
    (physical : (Fin C × Fin 23) → V) (out : Register C) (value : V)
    (hreal : Realizes active logical physical)
    (hactive : ∀ r, active r → Live k s r) (hout : Live k s out) :
    Realizes (fun r => active r ∨ r = out)
      (Function.update logical out value)
      (Function.update physical (slot out) value) := by
  intro r hr
  by_cases he : r = out
  · subst r
    simp
  · have har : active r := hr.resolve_right he
    have hs : slot r ≠ slot out := fun h =>
      he (live_slot_injective (hactive r har) hout h)
    simpa [Function.update_of_ne he, Function.update_of_ne hs] using hreal r har

/-- Dropping dead logical bindings changes no admitted live read. -/
theorem retire_realizes {C : ℕ} {V : Type*} {before after : Register C → Prop}
    {logical : Register C → V} {physical : (Fin C × Fin 23) → V}
    (h : Realizes before logical physical) (hsub : ∀ r, after r → before r) :
    Realizes after logical physical := fun r hr => h r (hsub r hr)

theorem carrier_slot_count (C : ℕ) : Fintype.card (Fin C × Fin 23) = 23 * C := by
  simp [Nat.mul_comm]

/-- Arithmetic comparison for the occupied-host census `14C+9n`, enforced
by `storage.py` on finite controls. `Live` includes addresses, accumulators
and payload banks on every carrier, so its kernel layout bound is `23C`. -/
theorem occupied_slot_bound {C n : ℕ} (h : n ≤ C) :
    14 * C + 9 * n ≤ 23 * C := by omega

/-- This allocator intentionally does not preserve arbitrarily old versions. -/
theorem retired_payload_alias {C : ℕ} (k : ℕ) (c : Fin C) :
    slot (.payload (k + 2) c) = slot (.payload k c) := by
  simp [slot, owner, index]

end OPH.SourceRoutingStorage

module
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace OPH.SourceRoutingBudget

open scoped BigOperators

def readCount {n : ℕ} (K : ℕ) (menu : Fin n → Finset (Fin n)) : ℕ :=
  K * ∑ s, (menu s).card

def hopCount {C n K : ℕ} (relays : Fin K → Fin n → Finset (Fin C)) : ℕ :=
  ∑ k, ∑ s, (relays k s).card

def eventCount (C n K R H : ℕ) : ℕ := 13*C + 8*n + 2*K*n + R + 6*H

/-- The actual family includes each site's own preceding version. -/
theorem readCount_lower {n : ℕ} (K : ℕ) (menu : Fin n → Finset (Fin n))
    (self : ∀ s, s ∈ menu s) : K*n ≤ readCount K menu := by
  have h : n ≤ ∑ s, (menu s).card := by
    calc
      n = ∑ _ : Fin n, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun s _ => Finset.one_le_card.mpr ⟨s, self s⟩
  exact Nat.mul_le_mul_left K h

theorem readCount_upper {n : ℕ} (K : ℕ) (menu : Fin n → Finset (Fin n)) :
    readCount K menu ≤ K*n*n := by
  have h : (∑ s, (menu s).card) ≤ n*n := by
    calc
      _ ≤ ∑ _ : Fin n, n := Finset.sum_le_sum fun s _ => by
        simpa using Finset.card_le_univ (menu s)
      _ = _ := by simp
  simpa [readCount, Nat.mul_assoc] using Nat.mul_le_mul_left K h

/-- A pruned rooted tree captures each nonroot carrier at most once. Shared
prefixes are counted once, rather than charging a unicast path per read. -/
theorem hopCount_upper {C n K : ℕ} (relays : Fin K → Fin n → Finset (Fin C))
    (root : Fin n → Fin C) (no_root : ∀ k s, root s ∉ relays k s) :
    hopCount relays ≤ K*n*(C-1) := by
  have h (k : Fin K) (s : Fin n) : (relays k s).card ≤ C-1 := by
    have hsub : relays k s ⊂ (Finset.univ : Finset (Fin C)) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      constructor
      · exact Finset.subset_univ _
      · intro he
        apply no_root k s
        rw [he]
        exact Finset.mem_univ _
    have ht : (relays k s).card < C := by
      simpa using Finset.card_lt_card hsub
    omega
  calc
    hopCount relays ≤ ∑ _ : Fin K, ∑ _ : Fin n, (C-1) := by
      exact Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun s _ => h k s
    _ = _ := by simp [Nat.mul_assoc]

theorem eventCount_upper {C n K R H : ℕ}
    (hr : R ≤ K*n*n) (hh : H ≤ K*n*(C-1)) :
    eventCount C n K R H ≤ 13*C+8*n+2*K*n+K*n*n+6*(K*n*(C-1)) := by
  unfold eventCount
  omega

/-- Uniform raw operation mass cannot inherit the distinguished-event weight:
even the self reads, starts and commits give at least three times that count.
This is a whole-window census, not a claim about every primitive-order interval. -/
theorem three_times_logical_le_events {C n K R H : ℕ} (hr : K*n ≤ R) :
    3*((K+1)*n) + 13*C + 5*n ≤ eventCount C n K R H := by
  unfold eventCount
  nlinarith

/-- A quantitative incompatibility, consuming a separately proved logical
count error. No operational volume law is assumed or silently selected. -/
theorem raw_mass_error_lower {E N : ℕ} {w V ε : ℝ}
    (hcount : 3*N ≤ E) (hw : 0 ≤ w) (hlogical : |w*(N : ℝ)-V| ≤ ε) :
    2*V-3*ε ≤ |w*(E : ℝ)-V| := by
  have he : (3 : ℝ)*(N : ℝ) ≤ (E : ℝ) := by exact_mod_cast hcount
  have hm := mul_le_mul_of_nonneg_left he hw
  have hl := (abs_le.mp hlogical).1
  have ha := le_abs_self (w*(E : ℝ)-V)
  nlinarith

/-- A serial primitive tick representing one logical layer must divide its
entire event cost. A common tick cannot equal the declared logical duration
when a layer contains more than one operation. -/
theorem serial_tick_bound {τ Δ : ℝ} {cost : ℕ} (hcost : 1 < cost)
    (hτ : 0 < τ) (h : (cost : ℝ)*τ ≤ Δ) : τ < Δ := by
  have hc : (1 : ℝ) < cost := by exact_mod_cast hcost
  nlinarith

end OPH.SourceRoutingBudget

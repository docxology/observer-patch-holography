module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

/-!
# A constructive causal-cone sandwich for a refining lattice law

This module concerns a supplied integer three-dimensional spatial lattice.
In one time layer a signal may make any integer displacement of Euclidean
length at most `R`, including zero. Coordinatewise floor rounding constructs
a path to every endpoint inside the narrower cone with speed `R - 3`.
Every permitted path lies inside the outer cone with speed `R`.

After assigning spatial scale `h > 0` and layer duration `R * h`, the relative
cone margin is `3 / R`. Thus growing direction menus, rather than refinement
of a fixed finite stencil alone, give a constructive way to shrink the causal
discrepancy. The lattice, dimension, move law and time assignment are inputs.
This proves neither selection of that law by observer dynamics nor physical
clock calibration, count--volume convergence or manifold reconstruction.
-/

namespace OPH.RefiningLatticeCausalCone

abbrev Lattice := Fin 3 → ℤ
abbrev Space := EuclideanSpace ℝ (Fin 3)

def embed (d : Lattice) : Space := WithLp.toLp 2 (fun i => (d i : ℝ))

@[simp] theorem embed_apply (d : Lattice) (i : Fin 3) :
    embed d i = (d i : ℝ) := rfl

@[simp] theorem embed_zero : embed 0 = 0 := by ext i; simp [embed]

@[simp] theorem embed_sub (a b : Lattice) :
    embed (a - b) = embed a - embed b := by ext i; simp [embed]

/-- A floor difference has less than one unit of error, including negative
coordinates. This avoids accumulating errors over the path length. -/
theorem floor_difference_error (a b : ℝ) :
    |((⌊b⌋ : ℤ) : ℝ) - ((⌊a⌋ : ℤ) : ℝ) - (b - a)| < 1 := by
  have ha := Int.floor_le a
  have hb := Int.floor_le b
  have ha' := Int.lt_floor_add_one a
  have hb' := Int.lt_floor_add_one b
  rw [abs_lt]
  constructor <;> linarith

/-- Conservative Euclidean bound used to keep the cone margin rational. -/
theorem norm_le_three_of_coordinate_error (v : Space)
    (h : ∀ i : Fin 3, |v i| ≤ 1) : ‖v‖ ≤ 3 := by
  have hs (i : Fin 3) : (v i) ^ 2 ≤ 1 := by
    have hi := abs_le.mp (h i)
    nlinarith
  have hn := EuclideanSpace.real_norm_sq_eq v
  simp only [Fin.sum_univ_succ] at hn
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  norm_num at hn
  nlinarith [norm_nonneg v]

/-- Explicit integer path obtained by rounding points of a straight segment. -/
noncomputable def roundedNode (d : Lattice) (k j : ℕ) : Lattice :=
  fun i => ⌊(j : ℝ) * (d i : ℝ) / (k : ℝ)⌋

@[simp] theorem roundedNode_zero (d : Lattice) (k : ℕ) :
    roundedNode d k 0 = 0 := by ext i; simp [roundedNode]

theorem roundedNode_terminal (d : Lattice) {k : ℕ} (hk : 0 < k) :
    roundedNode d k k = d := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  ext i
  simp [roundedNode, mul_div_cancel_left₀, hk']

/-- Each rounded step differs from the target average step by at most three
Euclidean units, uniformly in both the number of steps and the endpoint. -/
theorem rounded_step_error (d : Lattice) (k j : ℕ) :
    ‖embed (roundedNode d k (j + 1) - roundedNode d k j) -
      (1 / (k : ℝ)) • embed d‖ ≤ 3 := by
  apply norm_le_three_of_coordinate_error
  intro i
  have hf := floor_difference_error
    ((j : ℝ) * (d i : ℝ) / (k : ℝ))
    (((j + 1 : ℕ) : ℝ) * (d i : ℝ) / (k : ℝ))
  have hid : ((j + 1 : ℕ) : ℝ) * (d i : ℝ) / (k : ℝ) -
      (j : ℝ) * (d i : ℝ) / (k : ℝ) =
      (1 / (k : ℝ)) * (d i : ℝ) := by push_cast; ring
  rw [hid] at hf
  simpa [embed, roundedNode] using le_of_lt hf

theorem rounded_step_norm (d : Lattice) (k j : ℕ) :
    ‖embed (roundedNode d k (j + 1) - roundedNode d k j)‖ ≤
      ‖embed d‖ / (k : ℝ) + 3 := by
  have he := rounded_step_error d k j
  have ht := norm_sub_le
    (embed (roundedNode d k (j + 1) - roundedNode d k j) -
      (1 / (k : ℝ)) • embed d)
    (-((1 / (k : ℝ)) • embed d))
  have hn : ‖(1 / (k : ℝ)) • embed d‖ = ‖embed d‖ / (k : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  rw [hn] at ht
  linarith

/-- Reachability in exactly `k` layers of the supplied all-moves ball law. -/
def Reachable (R : ℝ) (k : ℕ) (d : Lattice) : Prop :=
  ∃ p : ℕ → Lattice, p 0 = 0 ∧ p k = d ∧
    ∀ j < k, ‖embed (p (j + 1) - p j)‖ ≤ R

theorem inner_cone_reachable (R : ℝ) (d : Lattice) {k : ℕ}
    (hk : 0 < k) (hd : ‖embed d‖ ≤ (k : ℝ) * (R - 3)) :
    Reachable R k d := by
  refine ⟨roundedNode d k, roundedNode_zero d k,
    roundedNode_terminal d hk, ?_⟩
  intro j _
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hdiv : ‖embed d‖ / (k : ℝ) ≤ R - 3 :=
    (div_le_iff₀ hk').mpr (by simpa [mul_comm] using hd)
  exact le_trans (rounded_step_norm d k j) (by linarith)

/-- The outer bound uses only the local speed cap; no rounding assumption. -/
theorem path_displacement_bound (p : ℕ → Space) (R : ℝ) (k : ℕ)
    (h : ∀ j < k, ‖p (j + 1) - p j‖ ≤ R) :
    ‖p k - p 0‖ ≤ (k : ℝ) * R := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hi := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have hs := h k (Nat.lt_succ_self k)
      have ht : ‖p (k + 1) - p 0‖ ≤
          ‖p (k + 1) - p k‖ + ‖p k - p 0‖ := by
        simpa using norm_add_le (p (k + 1) - p k) (p k - p 0)
      push_cast
      nlinarith

theorem reachable_outer_cone (R : ℝ) (d : Lattice) (k : ℕ)
    (h : Reachable R k d) : ‖embed d‖ ≤ (k : ℝ) * R := by
  rcases h with ⟨p, hp0, hpk, hstep⟩
  have hb := path_displacement_bound (fun j => embed (p j)) R k
    (fun j hj => by simpa using hstep j hj)
  simpa [hp0, hpk] using hb

/-- Quantitative replacement for exact finite order/cone equivalence. -/
theorem causal_cone_sandwich (R : ℝ) (d : Lattice) {k : ℕ} (hk : 0 < k) :
    (‖embed d‖ ≤ (k : ℝ) * (R - 3) → Reachable R k d) ∧
    (Reachable R k d → ‖embed d‖ ≤ (k : ℝ) * R) :=
  ⟨inner_cone_reachable R d hk, reachable_outer_cone R d k⟩

/-- With spatial spacing `h` and layer duration `R*h`, the inner speed is
`1 - 3/R`. No independently asserted exact finite cone embedding is needed. -/
theorem scaled_inner_cone_reachable (h R : ℝ) (d : Lattice) {k : ℕ}
    (hh : 0 < h) (hR : 0 < R) (hk : 0 < k)
    (hd : ‖h • embed d‖ ≤ ((k : ℝ) * (R * h)) * (1 - 3 / R)) :
    Reachable R k d := by
  have heq : ((k : ℝ) * (R * h)) * (1 - 3 / R) =
      h * ((k : ℝ) * (R - 3)) := by field_simp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh, heq] at hd
  exact inner_cone_reachable R d hk ((mul_le_mul_iff_right₀ hh).mp hd)

theorem scaled_reachable_outer_cone (h R : ℝ) (d : Lattice) (k : ℕ)
    (hh : 0 ≤ h) (hr : Reachable R k d) :
    ‖h • embed d‖ ≤ (k : ℝ) * (R * h) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  have hb := mul_le_mul_of_nonneg_left (reachable_outer_cone R d k hr) hh
  nlinarith

/-- A fixed radius-one menu fails exact cone faithfulness even for a
strictly timelike endpoint: `(1,1,1)` lies within radius two but needs at
least three of the permitted axis-or-wait moves. -/
theorem fixed_menu_missing_timelike_endpoint :
    ‖embed (fun _ : Fin 3 => (1 : ℤ))‖ < 2 ∧
      ¬ Reachable 1 2 (fun _ : Fin 3 => (1 : ℤ)) := by
  constructor
  · have hn := EuclideanSpace.real_norm_sq_eq
      (embed (fun _ : Fin 3 => (1 : ℤ)))
    norm_num [embed, Fin.sum_univ_succ] at hn
    have hn' : ‖embed (fun _ : Fin 3 => (1 : ℤ))‖ ^ 2 = 3 := by
      simpa [embed] using hn
    nlinarith [norm_nonneg (embed (fun _ : Fin 3 => (1 : ℤ)))]
  · rintro ⟨p, hp0, hp2, hs⟩
    have ha := hs 0 (by omega)
    have hb := hs 1 (by omega)
    simp [hp0, hp2] at ha hb
    have hi (i : Fin 3) :
        1 ≤ (p 1 i : ℝ) ^ 2 + (1 - (p 1 i : ℝ)) ^ 2 := by
      have hc : p 1 i ≤ 0 ∨ 1 ≤ p 1 i := by omega
      rcases hc with hc | hc
      · have hc' : (p 1 i : ℝ) ≤ 0 := by exact_mod_cast hc
        nlinarith [sq_nonneg (p 1 i : ℝ)]
      · have hc' : (1 : ℝ) ≤ (p 1 i : ℝ) := by exact_mod_cast hc
        nlinarith [sq_nonneg ((p 1 i : ℝ) - 1)]
    have hqa := EuclideanSpace.real_norm_sq_eq (embed (p 1))
    have hqb := EuclideanSpace.real_norm_sq_eq
      (embed (fun _ : Fin 3 => (1 : ℤ)) - embed (p 1))
    simp only [Fin.sum_univ_succ, embed_apply, PiLp.sub_apply] at hqa hqb
    norm_num at hqa hqb
    have h0 := hi 0
    have h1 := hi 1
    have h2 := hi 2
    nlinarith [norm_nonneg (embed (p 1)),
      norm_nonneg (embed (fun _ : Fin 3 => (1 : ℤ)) - embed (p 1))]

#print axioms causal_cone_sandwich
#print axioms scaled_inner_cone_reachable
#print axioms fixed_menu_missing_timelike_endpoint

end OPH.RefiningLatticeCausalCone

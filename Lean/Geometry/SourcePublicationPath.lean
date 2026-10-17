module
public import Geometry.SourceCheckpointPipeline

@[expose] public section

/-! Native algebra underlying the four-port eventual-publication control.
The all-word invariant and its almost-sure consequence are proved analytically
in DERIVATION.md; these identities concern actual native pair means. -/

set_option autoImplicit false

namespace OPH.SourcePublicationPath
noncomputable section
open ObserverPatchHolography.ScalarSeamRepair

def left (a : ℝ) : Fin 4 → ℝ := ![-2*a,a,a,0]
def right (a : ℝ) : Fin 4 → ℝ := ![-a/2,-a/2,a,0]

theorem enter_left : pairAverage (1 : Fin 4) (2 : Fin 4) ![1,-1,0,0] = left (-1/2) := by
  funext i
  fin_cases i <;> simp [pairAverage,left]
  norm_num

theorem left_zero (a : ℝ) : pairAverage (0 : Fin 4) 1 (left a) = right a := by
  funext i
  fin_cases i <;> simp [pairAverage,left,right] <;> ring

theorem right_one (a : ℝ) : pairAverage (1 : Fin 4) 2 (right a) = left (a/4) := by
  funext i
  fin_cases i <;> simp [pairAverage,left,right] <;> ring

theorem left_one (a : ℝ) : pairAverage (1 : Fin 4) 2 (left a) = left a := by
  funext i
  fin_cases i <;> simp [pairAverage,left]

theorem right_zero (a : ℝ) : pairAverage (0 : Fin 4) 1 (right a) = right a := by
  funext i
  fin_cases i <;> simp [pairAverage,right]

theorem left_sample (a : ℝ) : pairAverage (2 : Fin 4) 3 (left a) 3 = a/2 := by
  simp [pairAverage,left]

theorem right_sample (a : ℝ) : pairAverage (2 : Fin 4) 3 (right a) 3 = a/2 := by
  simp [pairAverage,right]

/-- Conserved total and a recorded contrasting response jointly distinguish
both independent preparation coordinates, after any subsequent state loss. -/
theorem contrast_and_total_injective (u v : ℝ) (huv : u ≠ v)
    (x y x' y' : ℝ) (ht : x+y=x'+y')
    (hr : u*x+v*y=u*x'+v*y') : x=x' ∧ y=y' := by
  have hx : (u-v)*(x-x')=0 := by nlinarith [congrArg (fun t : ℝ => v*t) ht]
  have hx' : x=x' := sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr huv))
  constructor
  · exact hx'
  · linarith

/-- The native initial potential solves the competing first-move equation. -/
theorem initial_potential (p₀ p₁ p₂ : ℝ) (h₀ : 0 < p₀) (h₁ : 0 < p₁)
    (hs : p₀+p₁+p₂=1) : p₁+p₂*(p₁/(p₀+p₁)) = p₁/(p₀+p₁) := by
  have hd : p₀+p₁ ≠ 0 := ne_of_gt (add_pos h₀ h₁)
  field_simp
  nlinarith

theorem selected_first (p₀ p₁ p₂ : ℝ) (h₀ : 0 < p₀) (h₁ : 0 < p₁) :
    p₁/(p₁/(p₀+p₁)) = p₀+p₁ ∧
      p₂*(p₁/(p₀+p₁))/(p₁/(p₀+p₁)) = p₂ := by
  have hd : p₀+p₁ ≠ 0 := ne_of_gt (add_pos h₀ h₁)
  constructor <;> field_simp

theorem uniform_guard_differs : (2/3 : ℝ) ≠ 1/2 := by norm_num

end
end OPH.SourcePublicationPath

module
public import Geometry.SourceBankMachine

@[expose] public section

/-!
# Finite correspondence checks for the captured control

The generated control certificate evaluates this checker in the kernel.
Rows describe the captured plan's logical instruction, every observed scale,
and the complete native work of that stage. This finite comparison does not
prove the captured scalar-port embedding or the Python compiler in general.
-/

set_option autoImplicit false

namespace OPH.SourceBankTrace
open OPH.SourceBankMachine

abbrev Row := Op × List (ℕ × ℕ) × ℕ

def checks (k : ℕ) : List Op → Scales → List Row → Bool
  | [], _, [] => true
  | op::ops, e, row::rows =>
      decide (op = row.1) && decide (opWork op k e = row.2.2) &&
      row.2.1.all (fun poll => decide (scaleStep op e poll.1 = poll.2)) &&
      checks k ops (scaleStep op e) rows
  | _, _, _ => false

theorem checks_length (k : ℕ) (ops : List Op) (e : Scales) (rows : List Row)
    (h : checks k ops e rows = true) : ops.length = rows.length := by
  induction ops generalizing e rows with
  | nil => cases rows <;> simp_all [checks]
  | cons op ops ih =>
    cases rows with
    | nil => simp [checks] at h
    | cons row rows =>
      simp only [checks,Bool.and_eq_true] at h
      simpa using ih _ _ h.2

theorem checks_work (k : ℕ) (ops : List Op) (e : Scales) (rows : List Row)
    (h : checks k ops e rows = true) : work ops k e = (rows.map (fun row => row.2.2)).sum := by
  induction ops generalizing e rows with
  | nil => cases rows <;> simp_all [checks,work]
  | cons op ops ih =>
    cases rows with
    | nil => simp [checks] at h
    | cons row rows =>
      simp only [checks,Bool.and_eq_true,decide_eq_true_eq] at h
      simp only [work,List.map_cons,List.sum_cons,h.1.1.2,ih _ _ h.2]

end OPH.SourceBankTrace

module
public import ExteriorSelection

@[expose] public section

/-!
# Charge conjugation in the Weyl census and Yukawa action

The even-parity exterior table is an all-left-Weyl census. A four-component
Yukawa expression instead uses the charge conjugates of its singlet rows.
These checks bind both notations to the existing integer charge table and
reject their mixed use. The component grammar, chirality interpretation,
Higgs choice and kinetic law remain supplied; no spacetime action or
physical field selection follows from these finite charge identities.
-/

namespace OPH.WeylYukawaConventions

open OPH.ExteriorSelection

/-- Index dictionary in the committed even exterior sector. -/
def qRow : Fin 10 := 3
def uConjugateRow : Fin 10 := 2
def dConjugateRow : Fin 10 := 8
def lRow : Fin 10 := 9
def eConjugateRow : Fin 10 := 4
def hRow : Fin 10 := 1

/-- A right-handed action field is the charge conjugate of the census row. -/
def rightCharge (row : Fin 10) : ℤ := -charge row

theorem all_fermion_rows_selected :
    mem evenMask qRow = true ∧ mem evenMask uConjugateRow = true ∧
    mem evenMask dConjugateRow = true ∧ mem evenMask lRow = true ∧
    mem evenMask eConjugateRow = true := by decide

theorem conjugate_charge_dictionary (i : Fin 10) :
    charge (conj i) = rightCharge i := by
  fin_cases i <;> decide

theorem right_singlet_charges :
    rightCharge uConjugateRow = 4 ∧ rightCharge dConjugateRow = -2 ∧
    rightCharge eConjugateRow = -6 := by decide

/-- All-left-Weyl up channel uses H, with the weak epsilon contraction. -/
theorem weyl_up_neutral :
    charge qRow + charge hRow + charge uConjugateRow = 0 := by decide

/-- All-left-Weyl down channel uses the conjugate Higgs. -/
theorem weyl_down_neutral :
    charge qRow - charge hRow + charge dConjugateRow = 0 := by decide

theorem weyl_lepton_neutral :
    charge lRow - charge hRow + charge eConjugateRow = 0 := by decide

/-- Four-component up channel uses Qbar, Htilde and u_R. -/
theorem dirac_up_neutral :
    -charge qRow - charge hRow + rightCharge uConjugateRow = 0 := by decide

theorem dirac_down_neutral :
    -charge qRow + charge hRow + rightCharge dConjugateRow = 0 := by decide

theorem dirac_lepton_neutral :
    -charge lRow + charge hRow + rightCharge eConjugateRow = 0 := by decide

/-- Mixing the census names into the four-component expression is charged. -/
theorem mixed_up_charge :
    -charge qRow - charge hRow + charge uConjugateRow = -8 := by decide

theorem mixed_down_charge :
    -charge qRow + charge hRow + charge dConjugateRow = 4 := by decide

theorem mixed_lepton_charge :
    -charge lRow + charge hRow + charge eConjugateRow = 12 := by decide

theorem mixed_convention_not_neutral :
    -charge qRow - charge hRow + charge uConjugateRow ≠ 0 ∧
    -charge qRow + charge hRow + charge dConjugateRow ≠ 0 ∧
    -charge lRow + charge hRow + charge eConjugateRow ≠ 0 := by decide

/-- Charge neutrality forces the conjugate sign for any fixed singlet. -/
theorem right_charge_forced (left higgs singlet : ℤ)
    (hWeyl : left + higgs + singlet = 0) (right : ℤ)
    (hDirac : -left - higgs + right = 0) : right = -singlet := by omega

/-- The weak epsilon tensor transforms by the determinant. Coefficients
commute; this is the tensor identity, not a replacement of fermions by numbers. -/
theorem epsilon_transform {R : Type*} [CommRing R]
    (a b c d x y z w : R) :
    (a*x+b*y)*(c*z+d*w)-(c*x+d*y)*(a*z+b*w) =
      (a*d-b*c)*(x*w-y*z) := by ring

theorem epsilon_SL2_invariant {R : Type*} [CommRing R]
    (a b c d x y z w : R) (hdet : a*d-b*c=1) :
    (a*x+b*y)*(c*z+d*w)-(c*x+d*y)*(a*z+b*w) = x*w-y*z := by
  rw [epsilon_transform, hdet, one_mul]

#print axioms right_charge_forced
#print axioms epsilon_SL2_invariant
#print axioms mixed_convention_not_neutral

end OPH.WeylYukawaConventions

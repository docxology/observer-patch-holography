module
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

set_option autoImplicit false

/-!
# Work response and its missing source identification

The volume extension and the canonical work convention are supplied. The
first family proves that a complete fixed-volume energy history does not
determine pressure. The field identities apply to explicitly supplied
Hamiltonian scaling in three spatial dimensions. No native repair energy,
physical volume, equilibrium preparation or calibration is derived.
-/

namespace OPH.EOS

noncomputable def extension (Q V₀ α V : ℝ) : ℝ := Q * (V / V₀) ^ (-α)

theorem extension_agrees (Q V₀ α : ℝ) (hV : V₀ ≠ 0) :
    extension Q V₀ α V₀ = Q := by
  simp [extension, div_self hV]

theorem extension_positive (Q V₀ α V : ℝ) (hQ : 0 < Q)
    (hV₀ : 0 < V₀) (hV : 0 < V) : 0 < extension Q V₀ α V := by
  exact mul_pos hQ (Real.rpow_pos_of_pos (div_pos hV hV₀) _)

theorem extension_derivative (Q V₀ α : ℝ) (hV : V₀ ≠ 0) :
    HasDerivAt (extension Q V₀ α) (-α * Q / V₀) V₀ := by
  have hd := (hasDerivAt_id V₀).div_const V₀
  have hn : V₀ / V₀ ≠ 0 := by simp [hV]
  have hp := (hd.rpow_const (p := -α) (Or.inl hn)).const_mul Q
  convert hp using 1
  · rfl
  · simp only [id_eq, div_self hV, Real.one_rpow]
    ring

theorem arbitrary_reference_w (Q V₀ α : ℝ) (hQ : Q ≠ 0) (hV : V₀ ≠ 0) :
    -deriv (extension Q V₀ α) V₀ / (extension Q V₀ α V₀ / V₀) = α := by
  rw [(extension_derivative Q V₀ α hV).deriv, extension_agrees Q V₀ α hV]
  field_simp

/-- Even fixing a positive energy history leaves every local work ratio
available if the volume extension is unprovided. The chosen extensions do
not establish an equilibrium ensemble or identify Q as physical energy. -/
theorem fixed_history_does_not_select_w {ι : Type*} (Q : ι → ℝ)
    (V₀ α β : ℝ) (hQ : ∀ i, Q i ≠ 0) (hV : V₀ ≠ 0) :
    (∀ i, extension (Q i) V₀ α V₀ = extension (Q i) V₀ β V₀) ∧
    (∀ i, -deriv (extension (Q i) V₀ α) V₀ /
      (extension (Q i) V₀ α V₀ / V₀) = α) ∧
    (∀ i, -deriv (extension (Q i) V₀ β) V₀ /
      (extension (Q i) V₀ β V₀ / V₀) = β) := by
  exact ⟨fun i => by simp [extension_agrees, hV],
    fun i => arbitrary_reference_w (Q i) V₀ α (hQ i) hV,
    fun i => arbitrary_reference_w (Q i) V₀ β (hQ i) hV⟩

theorem distinct_work_ratios_same_history {ι : Type*} (Q : ι → ℝ)
    (i₀ : ι) (V₀ α β : ℝ) (hQ : ∀ i, Q i ≠ 0) (hV : V₀ ≠ 0)
    (hαβ : α ≠ β) :
    (∀ i, extension (Q i) V₀ α V₀ = extension (Q i) V₀ β V₀) ∧
    -deriv (extension (Q i₀) V₀ α) V₀ / (Q i₀ / V₀) ≠
      -deriv (extension (Q i₀) V₀ β) V₀ / (Q i₀ / V₀) := by
  constructor
  · exact (fixed_history_does_not_select_w Q V₀ α β hQ hV).1
  · have ha := arbitrary_reference_w (Q i₀) V₀ α (hQ i₀) hV
    have hb := arbitrary_reference_w (Q i₀) V₀ β (hQ i₀) hV
    rw [extension_agrees (Q i₀) V₀ α hV] at ha
    rw [extension_agrees (Q i₀) V₀ β hV] at hb
    rw [ha, hb]
    exact hαβ

theorem pair_mean_quadratic_drop (a b : ℝ) :
    (a^2+b^2)/2 - (((a+b)/2)^2+((a+b)/2)^2)/2 = (a-b)^2/4 := by ring

theorem added_loss_record_conserves (Q Q' B : ℝ) :
    Q' + (B + (Q-Q')) = Q+B := by ring

noncomputable def scalarHamiltonian (K G U L : ℝ) : ℝ :=
  K / L^3 + G*L + U*L^3

theorem scalar_dilation_derivative (K G U : ℝ) :
    HasDerivAt (scalarHamiltonian K G U) (-3*K+G+3*U) 1 := by
  have cube := (hasDerivAt_id (1 : ℝ)).pow 3
  have kinetic := (hasDerivAt_const (1 : ℝ) K).div cube (by norm_num)
  have grad := (hasDerivAt_id (1 : ℝ)).const_mul G
  have mass := cube.const_mul U
  convert (kinetic.add grad).add mass using 1
  · funext L
    simp [scalarHamiltonian]
  · norm_num
    ring

/-- V=L³ and fixed original field q and canonical p are part of the
Hamiltonian convention. The mass-normalized coordinates must not be held
fixed instead when defining instantaneous stress. -/
theorem scalar_pressure_from_work (K G U : ℝ) :
    -deriv (scalarHamiltonian K G U) 1 / 3 = K-G/3-U := by
  rw [(scalar_dilation_derivative K G U).deriv]
  ring

theorem scalar_stress_bounds (K G U : ℝ)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hU : 0 ≤ U) :
    -(K+G+U) ≤ K-G/3-U ∧ K-G/3-U ≤ K+G+U := by constructor <;> nlinarith

theorem scalar_virial_pressure (K G U : ℝ) (hv : K = G+U) :
    K-G/3-U = 2*G/3 := by rw [hv]; ring

/-- Fixed mass-normalized canonical coordinates give a different transient
work derivative. Their pressure agrees only under a virial condition. -/
theorem scalar_coordinate_pressure_difference (K G U : ℝ) :
    (K-G/3-U) - 2*G/3 = K-G-U := by ring

theorem scalar_virial_ratio_bounds (K G U : ℝ) (hG : 0 ≤ G) (hU : 0 ≤ U)
    (hH : 0 < K+G+U) (hv : K = G+U) :
    0 ≤ (K-G/3-U)/(K+G+U) ∧ (K-G/3-U)/(K+G+U) ≤ 1/3 := by
  constructor
  · exact div_nonneg (by rw [scalar_virial_pressure K G U hv]; positivity) (le_of_lt hH)
  · apply (div_le_iff₀ hH).2
    rw [hv]
    nlinarith

theorem scalar_massless_virial (K G : ℝ) (hG : G ≠ 0) (hv : K = G) :
    (K-G/3)/(K+G) = 1/3 := by
  rw [hv]
  field_simp
  ring

theorem maxwell_dilation_derivative (E : ℝ) :
    HasDerivAt (fun L : ℝ => E/L) (-E) 1 := by
  simpa [Pi.div_def] using (hasDerivAt_const (1 : ℝ) E).div (hasDerivAt_id 1) (by norm_num)

/-- A supplied 3D Maxwell Hamiltonian scaling as L⁻¹ has trace-average
stress E/(3V). This says nothing about isotropy of individual stresses. -/
theorem maxwell_reference_ratio (E : ℝ) (hE : E ≠ 0) :
    (-deriv (fun L : ℝ => E/L) 1 / 3) / E = 1/3 := by
  rw [(maxwell_dilation_derivative E).deriv]
  field_simp

end OPH.EOS

#print axioms OPH.EOS.fixed_history_does_not_select_w
#print axioms OPH.EOS.scalar_pressure_from_work
#print axioms OPH.EOS.scalar_virial_ratio_bounds
#print axioms OPH.EOS.maxwell_reference_ratio

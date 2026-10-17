module
public import Geometry.FlatDiamondError
public import Geometry.SourceNetCausalCone

@[expose] public section

set_option autoImplicit false

/-!
# Explicit weighted Alexandrov-volume error of the generated read order

The cells may be assigned to representatives outside the cells. Coverage,
disjointness and assignment are allowed almost everywhere. All-neighbour
paths are constructed from the supplied spatial covering, including the
zero-hop endpoint case. No count or volume convergence is an input.
-/

namespace OPH.SourceNetVolumeError

open MeasureTheory Set Real Filter
open OPH.SourceNetCausalCone OPH.SourceCausalBoundary OPH.FlatDiamondVolume OPH.FlatDiamondError
open scoped BigOperators Classical Topology

noncomputable section

abbrev Carrier := EuclideanSpace ℝ (Fin 3)

theorem covering_constructs_path_zero_or_pos {Ω S : Set Carrier} {h a : ℝ}
    (hΩ : Convex ℝ Ω) (hS : S ⊆ Ω) (hcover : Covers Ω S h)
    (hh : 0 ≤ h) (ha : 0 ≤ a) {x y : Carrier} (hx : x ∈ S) (hy : y ∈ S)
    {k : ℕ} (hd : ‖y - x‖ ≤ (k : ℝ) * (a - 2 * h)) :
    Reachable S a k x y := by
  by_cases hk : k = 0
  · subst k
    have heq : y = x := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hd) (norm_nonneg _)))
    subst y
    exact waiting_path ha hx 0
  · exact covering_constructs_path hΩ hS hcover hh hx hy (Nat.pos_of_ne_zero hk) hd

def layerMember {ι : Type*} (site : ι → Carrier) (a : ℝ) (K j : ℕ) (x : Carrier) (i : ι) : Prop :=
  Reachable (range site) a j x (site i) ∧ Reachable (range site) a (K - j) (site i) x

def layerMass {ι : Type*} [Fintype ι] (C : ι → Set Space) (site : ι → Carrier)
    (a : ℝ) (K j : ℕ) (x : Carrier) : ℝ :=
  ∑ i, volume.real (C i) * (if layerMember site a K j x i then (1 : ℝ) else 0)

def selectedCells {ι : Type*} [Fintype ι] (C : ι → Set Space) (P : ι → Prop) : Set Space :=
  ⋃ i ∈ Finset.univ.filter P, C i

theorem selectedCells_measurable {ι : Type*} [Fintype ι] (C : ι → Set Space) (P : ι → Prop)
    (hC : ∀ i, MeasurableSet (C i)) : MeasurableSet (selectedCells C P) :=
  MeasurableSet.biUnion (to_countable _) (fun i _ => hC i)

theorem selectedCells_mass {ι : Type*} [Fintype ι] (C : ι → Set Space) (P : ι → Prop)
    (hC : ∀ i, MeasurableSet (C i)) (hd : Pairwise (fun i j => AEDisjoint volume (C i) (C j)))
    (hf : ∀ i, volume (C i) ≠ ⊤) :
    volume.real (selectedCells C P) = ∑ i, volume.real (C i) * (if P i then (1 : ℝ) else 0) := by
  rw [selectedCells, measureReal_biUnion_finset₀ (fun i _ j _ hij => hd hij)
    (fun i _ => (hC i).nullMeasurableSet) (fun i _ => hf i), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem mem_selectedCells {ι : Type*} [Fintype ι] (C : ι → Set Space) (P : ι → Prop) (y : Space) :
    y ∈ selectedCells C P ↔ ∃ i, P i ∧ y ∈ C i := by simp [selectedCells]

/-- Exact layer sandwich obtained from actual generated paths and assigned cells. -/
theorem layerMass_sandwich {ι : Type*} [Fintype ι]
    (C : ι → Set Space) (site : ι → Carrier) {Ω : Set Carrier}
    (hΩ : Convex ℝ Ω) (hS : range site ⊆ Ω) {h a H : ℝ}
    (hcover : Covers Ω (range site) h) (hh : 0 ≤ h) (ha : 2 * h < a) (hH : 0 ≤ H)
    (hC : ∀ i, MeasurableSet (C i)) (hd : Pairwise (fun i j => AEDisjoint volume (C i) (C j)))
    (hf : ∀ i, volume (C i) ≠ ⊤)
    (hcells : ∀ᵐ y ∂(volume : Measure Space), (WithLp.toLp 2 y : Carrier) ∈ Ω → ∃ i, y ∈ C i)
    (hassign : ∀ i, ∀ᵐ y ∂(volume : Measure Space), y ∈ C i → ‖site i - WithLp.toLp 2 y‖ ≤ H)
    (K j : ℕ) (hj : j ≤ K) (x : Space) (hx : (WithLp.toLp 2 x : Carrier) ∈ range site)
    (hbuffer : ∀ y ∈ coordinateBall x ((K : ℝ) * a / 2 + H), (WithLp.toLp 2 y : Carrier) ∈ Ω) :
    let m := min (j : ℝ) ((K - j : ℕ) : ℝ)
    (4 * Real.pi / 3) * (max 0 ((a - 2 * h) * m - H)) ^ 3 ≤ layerMass C site a K j (WithLp.toLp 2 x) ∧
    layerMass C site a K j (WithLp.toLp 2 x) ≤ (4 * Real.pi / 3) * (a * m + H) ^ 3 := by
  dsimp only
  let m := min (j : ℝ) ((K - j : ℕ) : ℝ)
  have hm : 0 ≤ m := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hKj : ((K - j : ℕ) : ℝ) = (K : ℝ) - j := Nat.cast_sub hj
  have hmK : 2 * m ≤ K := by dsimp [m]; linarith [min_le_left (j : ℝ) ((K - j : ℕ) : ℝ), min_le_right (j : ℝ) ((K - j : ℕ) : ℝ)]
  have ha0 : 0 < a := by linarith
  let P := layerMember site a K j (WithLp.toLp 2 x)
  let U := selectedCells C P
  have hu : volume.real U = layerMass C site a K j (WithLp.toLp 2 x) := selectedCells_mass C P hC hd hf
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ i, y ∈ C i → ‖site i - WithLp.toLp 2 y‖ ≤ H := ae_all_iff.mpr hassign
  have hupper : U ≤ᵐ[volume] coordinateBall x (a * m + H) := by
    filter_upwards [hall] with y hy
    intro hyU
    obtain ⟨i, hi, hyi⟩ := (mem_selectedCells C P y).mp hyU
    have h₁ := reachable_outer hi.1
    have h₂ := reachable_outer hi.2
    rw [norm_sub_rev] at h₂
    have hrad : ‖site i - WithLp.toLp 2 x‖ ≤ a * m := by
      dsimp [m]
      rw [mul_min_of_nonneg _ _ ha0.le]
      exact le_min (by nlinarith) (by nlinarith)
    have htri := dist_triangle (WithLp.toLp 2 y : Carrier) (site i) (WithLp.toLp 2 x)
    simp only [dist_eq_norm, norm_sub_rev (WithLp.toLp 2 y) (site i)] at htri
    change ‖(WithLp.toLp 2 y : Carrier) - WithLp.toLp 2 x‖ ≤ a * m + H
    linarith [hy i hyi]
  have hub : volume U ≤ volume (coordinateBall x (a * m + H)) := measure_mono_ae hupper
  have hballf : volume (coordinateBall x (a * m + H)) ≠ ⊤ := (coordinateBall_compact _ _).measure_ne_top
  have huf : volume U ≠ ⊤ := ne_top_of_le_ne_top hballf hub
  have hup : layerMass C site a K j (WithLp.toLp 2 x) ≤ (4 * Real.pi / 3) * (a * m + H) ^ 3 := by
    rw [← hu, ← coordinateBall_volume_real x (by positivity : 0 ≤ a * m + H)]
    exact ENNReal.toReal_mono hballf hub
  refine ⟨?_, hup⟩
  by_cases hlo : (a - 2 * h) * m - H ≤ 0
  · rw [max_eq_left hlo]
    simp only [zero_pow (by norm_num : 3 ≠ 0), mul_zero, ← hu]
    exact measureReal_nonneg
  · have hlo : 0 < (a - 2 * h) * m - H := lt_of_not_ge hlo
    rw [max_eq_right hlo.le]
    have hlower : coordinateBall x ((a - 2 * h) * m - H) ≤ᵐ[volume] U := by
      filter_upwards [hall, hcells] with y hy hcov
      intro hyr
      have hdist : ‖(WithLp.toLp 2 y : Carrier) - WithLp.toLp 2 x‖ ≤ (a - 2 * h) * m - H := hyr
      have hyrB : y ∈ coordinateBall x ((K : ℝ) * a / 2 + H) := by
        change ‖(WithLp.toLp 2 y : Carrier) - WithLp.toLp 2 x‖ ≤ _
        nlinarith [mul_nonneg hh hm, mul_le_mul_of_nonneg_left hmK ha0.le]
      obtain ⟨i, hyi⟩ := hcov (hbuffer y hyrB)
      have htri := dist_triangle (site i) (WithLp.toLp 2 y : Carrier) (WithLp.toLp 2 x)
      simp only [dist_eq_norm] at htri
      have hin : ‖site i - WithLp.toLp 2 x‖ ≤ (a - 2 * h) * m := by linarith [hy i hyi]
      have hiS : site i ∈ range site := mem_range_self i
      have hp₁ := covering_constructs_path_zero_or_pos hΩ hS hcover hh ha0.le hx hiS
        (hin.trans (by nlinarith [mul_le_mul_of_nonneg_left (min_le_left (j : ℝ) ((K-j : ℕ) : ℝ)) (sub_pos.mpr ha).le]))
      have hp₂ := covering_constructs_path_zero_or_pos hΩ hS hcover hh ha0.le hiS hx
        (show ‖(WithLp.toLp 2 x : Carrier) - site i‖ ≤ ((K-j : ℕ) : ℝ) * (a-2*h) by
          rw [norm_sub_rev]
          exact hin.trans (by nlinarith [mul_le_mul_of_nonneg_left (min_le_right (j : ℝ) ((K-j : ℕ) : ℝ)) (sub_pos.mpr ha).le]))
      exact (mem_selectedCells C P y).mpr ⟨i, ⟨hp₁, hp₂⟩, hyi⟩
    rw [← hu, ← coordinateBall_volume_real x hlo.le]
    exact ENNReal.toReal_mono huf (measure_mono_ae hlower)

theorem layer_shell_error {a h H K m V : ℝ} (hh : 0 ≤ h) (ha : 2 * h < a)
    (hH : 0 ≤ H) (hm : 0 ≤ m) (hmK : 2 * m ≤ K)
    (hlo : (4 * Real.pi / 3) * (max 0 ((a - 2 * h) * m - H)) ^ 3 ≤ V)
    (hup : V ≤ (4 * Real.pi / 3) * (a * m + H) ^ 3) :
    |V - (4 * Real.pi / 3) * (a * m) ^ 3| ≤
      4 * Real.pi * (K * a / 2 + H) ^ 2 * (H + K * h) := by
  have ha0 : 0 < a := by linarith
  have hr : 0 ≤ a * m := mul_nonneg ha0.le hm
  have hrR : a * m ≤ K * a / 2 + H := by nlinarith
  have huR : a * m + H ≤ K * a / 2 + H := by nlinarith
  have hlr : max 0 ((a - 2 * h) * m - H) ≤ a * m := by
    apply max_le hr
    nlinarith [mul_nonneg hh hm]
  have hld : |max 0 ((a - 2 * h) * m - H) - a * m| ≤ H + K * h := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlr)]
    nlinarith [le_max_right 0 ((a - 2 * h) * m - H), mul_le_mul_of_nonneg_right hmK hh]
  have hud : |a * m + H - a * m| ≤ H + K * h := by
    have hK : 0 ≤ K := by linarith
    rw [add_sub_cancel_left, abs_of_nonneg hH]
    nlinarith [mul_nonneg hK hh]
  have hle := radial_shell_bound (le_max_left 0 _) hr (hlr.trans hrR) hrR
  have hue := radial_shell_bound (add_nonneg hr hH) hr huR hrR
  have hfac : 0 ≤ 4 * Real.pi * (K * a / 2 + H) ^ 2 := by positivity
  have hlb := hle.trans (mul_le_mul_of_nonneg_left hld hfac)
  have hub := hue.trans (mul_le_mul_of_nonneg_left hud hfac)
  rw [abs_le] at hlb hub ⊢
  constructor <;> linarith [hlb.1, hub.2]

theorem section_at_layer {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (K j : ℕ) (hj : j ≤ K) :
    sectionVolume c ((K : ℝ) * (a / c)) ((j : ℝ) * (a / c)) =
      (4 * Real.pi / 3) * (a * min (j : ℝ) ((K - j : ℕ) : ℝ)) ^ 3 := by
  unfold sectionVolume
  congr 2
  rw [mul_min_of_nonneg _ _ hc.le, mul_min_of_nonneg _ _ ha, Nat.cast_sub hj]
  congr 1 <;> field_simp

def weightedVolume {ι : Type*} [Fintype ι] (C : ι → Set Space) (site : ι → Carrier)
    (a c : ℝ) (K : ℕ) (x : Carrier) : ℝ :=
  (a / c) * ∑ j ∈ Finset.range (K + 1), layerMass C site a K j x

/-- The paper's explicit finite error, including all K+1 layers and the
temporal quadrature term. Both inequalities use the generated read order. -/
theorem weighted_alexandrov_error {ι : Type*} [Fintype ι]
    (C : ι → Set Space) (site : ι → Carrier) {Ω : Set Carrier}
    (hΩ : Convex ℝ Ω) (hS : range site ⊆ Ω) {h a H c : ℝ}
    (hcover : Covers Ω (range site) h) (hh : 0 ≤ h) (ha : 2 * h < a) (hH : 0 ≤ H) (hc : 0 < c)
    (hC : ∀ i, MeasurableSet (C i)) (hd : Pairwise (fun i j => AEDisjoint volume (C i) (C j)))
    (hf : ∀ i, volume (C i) ≠ ⊤)
    (hcells : ∀ᵐ y ∂(volume : Measure Space), (WithLp.toLp 2 y : Carrier) ∈ Ω → ∃ i, y ∈ C i)
    (hassign : ∀ i, ∀ᵐ y ∂(volume : Measure Space), y ∈ C i → ‖site i - WithLp.toLp 2 y‖ ≤ H)
    (K : ℕ) (x : Space) (hx : (WithLp.toLp 2 x : Carrier) ∈ range site)
    (hbuffer : ∀ y ∈ coordinateBall x ((K : ℝ) * a / 2 + H), (WithLp.toLp 2 y : Carrier) ∈ Ω) :
    let δ := a / c
    let T := (K : ℝ) * δ
    |weightedVolume C site a c K (WithLp.toLp 2 x) - Real.pi * c ^ 3 * T ^ 4 / 24| ≤
      4 * Real.pi * (T + δ) * (c * T / 2 + H) ^ 2 * (H + c * T * h / a) +
        Real.pi * c ^ 3 * T ^ 3 * δ / 2 := by
  dsimp only
  have ha0 : 0 < a := by linarith
  let δ := a / c
  let T := (K : ℝ) * δ
  let E := 4 * Real.pi * ((K : ℝ) * a / 2 + H) ^ 2 * (H + (K : ℝ) * h)
  have hδ : 0 < δ := div_pos ha0 hc
  have hjerr (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      |layerMass C site a K j (WithLp.toLp 2 x) - sectionVolume c T ((j : ℝ) * δ)| ≤ E := by
    have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hs := layerMass_sandwich C site hΩ hS hcover hh ha hH hC hd hf hcells hassign K j hjK x hx hbuffer
    rw [section_at_layer ha0.le hc K j hjK]
    exact layer_shell_error hh ha hH (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (by have hh := Nat.cast_sub (R := ℝ) hjK; linarith [min_le_left (j : ℝ) ((K-j : ℕ) : ℝ), min_le_right (j : ℝ) ((K-j : ℕ) : ℝ)]) hs.1 hs.2
  have hspace : |weightedVolume C site a c K (WithLp.toLp 2 x) -
      δ * ∑ j ∈ Finset.range (K + 1), sectionVolume c T ((j : ℝ) * δ)| ≤ (T + δ) * E := by
    change |δ * _ - δ * _| ≤ _
    rw [← mul_sub, abs_mul, abs_of_pos hδ, ← Finset.sum_sub_distrib]
    calc
      _ ≤ δ * ∑ j ∈ Finset.range (K + 1),
          |layerMass C site a K j (WithLp.toLp 2 x) - sectionVolume c T ((j : ℝ) * δ)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hδ.le
      _ ≤ δ * ∑ _ ∈ Finset.range (K + 1), E :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjerr) hδ.le
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; dsimp [T]; ring
  have htime := section_riemann_error K hδ hc.le
  have htotal := (abs_sub_le (weightedVolume C site a c K (WithLp.toLp 2 x))
    (δ * ∑ j ∈ Finset.range (K + 1), sectionVolume c T ((j : ℝ) * δ))
    (Real.pi * c ^ 3 * T ^ 4 / 24)).trans (add_le_add hspace htime)
  have hTa : c * T = (K : ℝ) * a := by dsimp [T, δ]; field_simp
  have hTha : c * T * h / a = (K : ℝ) * h := by rw [hTa]; field_simp
  convert htotal using 1
  dsimp only [E]
  rw [hTha, hTa]
  ring

/-- General weighted-family convergence from the proved finite estimate.
Cells need not have equal masses, populations and windows may vary, and
neither a count limit nor a volume-error hypothesis is supplied. -/
theorem weighted_alexandrov_tendsto {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (C : (n : ℕ) → ι n → Set Space) (site : (n : ℕ) → ι n → Carrier)
    (Ω : ℕ → Set Carrier) (a h H : ℕ → ℝ) {c T : ℝ} (hc : 0 < c)
    (hΩ : ∀ n, Convex ℝ (Ω n)) (hS : ∀ n, range (site n) ⊆ Ω n)
    (hcover : ∀ n, Covers (Ω n) (range (site n)) (h n))
    (ha : ∀ n, 0 < a n) (hh : ∀ n, 0 ≤ h n) (hH : ∀ n, 0 ≤ H n)
    (hC : ∀ n i, MeasurableSet (C n i))
    (hd : ∀ n, Pairwise (fun i j => AEDisjoint volume (C n i) (C n j)))
    (hf : ∀ n i, volume (C n i) ≠ ⊤)
    (hcells : ∀ n, ∀ᵐ y ∂(volume : Measure Space),
      (WithLp.toLp 2 y : Carrier) ∈ Ω n → ∃ i, y ∈ C n i)
    (hassign : ∀ n i, ∀ᵐ y ∂(volume : Measure Space),
      y ∈ C n i → ‖site n i - WithLp.toLp 2 y‖ ≤ H n)
    (K : ℕ → ℕ) (x : ℕ → Space)
    (hx : ∀ n, (WithLp.toLp 2 (x n) : Carrier) ∈ range (site n))
    (hbuffer : ∀ᶠ n in atTop, ∀ y ∈ coordinateBall (x n) ((K n : ℝ) * a n / 2 + H n),
      (WithLp.toLp 2 y : Carrier) ∈ Ω n)
    (ha0 : Tendsto a atTop (𝓝 0)) (hH0 : Tendsto H atTop (𝓝 0))
    (hratio : Tendsto (fun n => h n / a n) atTop (𝓝 0))
    (hT : Tendsto (fun n => (K n : ℝ) * (a n / c)) atTop (𝓝 T)) :
    Tendsto (fun n => weightedVolume (C n) (site n) (a n) c (K n) (WithLp.toLp 2 (x n)))
      atTop (𝓝 (Real.pi * c ^ 3 * T ^ 4 / 24)) := by
  let δ := fun n => a n / c
  let Tn := fun n => (K n : ℝ) * δ n
  let V := fun n => weightedVolume (C n) (site n) (a n) c (K n) (WithLp.toLp 2 (x n))
  let ref := fun n => Real.pi * c ^ 3 * (Tn n) ^ 4 / 24
  let err := fun n => 4 * Real.pi * (Tn n + δ n) * (c * Tn n / 2 + H n) ^ 2 *
      (H n + c * Tn n * (h n / a n)) + Real.pi * c ^ 3 * (Tn n) ^ 3 * δ n / 2
  have hδ : Tendsto δ atTop (𝓝 0) := by simpa only [zero_div] using ha0.div_const c
  have hsmall : ∀ᶠ n in atTop, 2 * h n < a n := by
    filter_upwards [hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
    have hd := (div_lt_iff₀ (ha n)).mp hn
    linarith
  have herr : Tendsto err atTop (𝓝 0) := by
    have hs := (((hT.add hδ).const_mul (4 * Real.pi)).mul
      ((((hT.const_mul c).div_const 2).add hH0).pow 2)).mul
        (hH0.add ((hT.const_mul c).mul hratio))
    have ht := (((hT.pow 3).const_mul (Real.pi * c ^ 3)).mul hδ).div_const 2
    simpa only [err, Tn, δ, mul_zero, zero_div, add_zero, mul_assoc] using hs.add ht
  have hdiff : Tendsto (fun n => V n - ref n) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero, Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg (V n - ref n))) _ herr
    filter_upwards [hsmall, hbuffer] with n hn hb
    have he := weighted_alexandrov_error (C n) (site n) (hΩ n) (hS n) (hcover n)
      (hh n) hn (hH n) hc (hC n) (hd n) (hf n) (hcells n) (hassign n) (K n) (x n) (hx n) hb
    simpa only [V, ref, err, Tn, δ, mul_div_assoc] using he
  have href : Tendsto ref atTop (𝓝 (Real.pi * c ^ 3 * T ^ 4 / 24)) :=
    ((hT.pow 4).const_mul (Real.pi * c ^ 3)).div_const 24
  simpa only [sub_add_cancel, zero_add] using hdiff.add href

#print axioms weighted_alexandrov_tendsto
#print axioms weighted_alexandrov_error
#print axioms layerMass_sandwich

end
end OPH.SourceNetVolumeError

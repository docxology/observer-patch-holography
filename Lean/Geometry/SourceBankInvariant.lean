module
public import Geometry.SourceBankMachine

@[expose] public section

/-! The compiler establishes workspace, retirement and finite-store
conditions required by native lowering. No well-formed execution trace is
assumed as an input to these compiler theorems. -/

set_option autoImplicit false

namespace OPH.SourceBankInvariant
open OPH.SourceBankMachine

def Clean (v : Values) : Prop := v 1 = 0 ∧ v 3 = 0

def Ready (op : Op) (v : Values) : Prop := v 1 = 0 ∧
  match op with
  | .transfer _ t _ => t = 3 → v 3 = 0
  | _ => True

def Safe : List Op → Values → Prop
  | [], _ => True
  | op::rest, v => Ready op v ∧ Safe rest (valueStep op v)

theorem safe_append (ops rest : List Op) (v : Values) :
    Safe (ops++rest) v ↔ Safe ops v ∧ Safe rest (values ops v) := by
  induction ops generalizing v with
  | nil => simp [Safe, values]
  | cons op ops ih => simp [Safe, values, ih, and_assoc]

theorem request_safe (s d : ℕ) (v : Values) (hc : Clean v) :
    Safe (request s d) v := by
  simp [request, Safe, Ready, valueStep, hc.1,hc.2]

theorem request_clean (s d : ℕ) (v : Values) : Clean (values (request s d) v) := by
  rw [request_values]
  simp [Clean]

theorem requests_clean (ss : List ℕ) (rd : ℕ → ℕ) (v : Values) (hc : Clean v) :
    Clean (values (requests ss rd) v) := by
  induction ss generalizing v with
  | nil => exact hc
  | cons s ss ih =>
    rw [requests, List.flatMap_cons, values_append]
    exact ih _ (request_clean s (rd s) v)

theorem requests_safe (ss : List ℕ) (rd : ℕ → ℕ) (v : Values) (hc : Clean v) :
    Safe (requests ss rd) v := by
  induction ss generalizing v with
  | nil => trivial
  | cons s ss ih =>
    rw [requests, List.flatMap_cons, safe_append]
    exact ⟨request_safe s (rd s) v hc,ih _ (request_clean s (rd s) v)⟩

theorem site_clean (ss : List ℕ) (t : ℕ) (rd : ℕ → ℕ) (wd : ℕ)
    (ht : 4 ≤ t) (v : Values) (hc : Clean v) : Clean (values (site ss t rd wd) v) := by
  have hs : Clean (valueStep .start v) := by simp [Clean,valueStep,hc.2]
  have hr := requests_clean ss rd (valueStep .start v) hs
  simpa [site, values_append, values, valueStep, Clean, show 1 ≠ t by omega,
    show 3 ≠ t by omega] using hr

theorem site_safe (ss : List ℕ) (t : ℕ) (rd : ℕ → ℕ) (wd : ℕ)
    (ht : 4 ≤ t) (v : Values) (hc : Clean v) : Safe (site ss t rd wd) v := by
  have hs : Clean (valueStep .start v) := by simp [Clean,valueStep,hc.2]
  have hr := requests_clean ss rd (valueStep .start v) hs
  change Ready .start v ∧ Safe (requests ss rd ++ [.transfer 0 t wd]) (valueStep .start v)
  constructor
  · exact ⟨hc.1,trivial⟩
  · rw [safe_append]
    exact ⟨requests_safe ss rd _ hs,⟨⟨hr.1,fun h => by omega⟩,trivial⟩⟩

theorem layer_clean (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) (v : Values) (hc : Clean v) :
    Clean (values (layerSites n side menu rd wd sites) v) := by
  induction sites generalizing v with
  | nil => exact hc
  | cons i rest ih =>
    rw [layerSites, values_append]
    exact ih _ (site_clean _ _ _ _ (bank_ge n (!side) i) v hc)

theorem layer_safe (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) (v : Values) (hc : Clean v) :
    Safe (layerSites n side menu rd wd sites) v := by
  induction sites generalizing v with
  | nil => trivial
  | cons i rest ih =>
    rw [layerSites, safe_append]
    exact ⟨site_safe _ _ _ _ (bank_ge n (!side) i) v hc,
      ih _ (site_clean _ _ _ _ (bank_ge n (!side) i) v hc)⟩

theorem program_clean (n : ℕ) (rd wd : ℕ → ℕ) (side : Bool)
    (menus : List (Layer n)) (v : Values) (hc : Clean v) :
    Clean (values (program n rd wd side menus) v) := by
  induction menus generalizing side v with
  | nil => exact hc
  | cons menu rest ih =>
    rw [program, values_append]
    exact ih _ _ (layer_clean n side menu rd wd _ v hc)

theorem program_safe (n : ℕ) (rd wd : ℕ → ℕ) (side : Bool)
    (menus : List (Layer n)) (v : Values) (hc : Clean v) :
    Safe (program n rd wd side menus) v := by
  induction menus generalizing side v with
  | nil => trivial
  | cons menu rest ih =>
    rw [program, safe_append]
    exact ⟨layer_safe n side menu rd wd _ v hc,
      ih _ _ (layer_clean n side menu rd wd _ v hc)⟩

def Confined (R : ℕ) : Op → Prop
  | .transfer s t _ => s < R ∧ t < R
  | _ => True

def Supported (R : ℕ) (v : Values) : Prop := ∀ i, R ≤ i → v i = 0

theorem step_supported (R : ℕ) (hR : 4 ≤ R) (op : Op) (v : Values)
    (ho : Confined R op) (hv : Supported R v) : Supported R (valueStep op v) := by
  intro i hi
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h3 : i ≠ 3 := by omega
  cases op with
  | start => simp [valueStep,h0,h1,hv i hi]
  | add => simp [valueStep,h0,hv i hi]
  | retire => simp [valueStep,h1,h3,hv i hi]
  | transfer s t d =>
    have ht := ho.2
    simp [valueStep,show i ≠ t by omega,hv i hi]

theorem values_supported (R : ℕ) (hR : 4 ≤ R) (ops : List Op) (v : Values)
    (ho : ∀ op ∈ ops, Confined R op) (hv : Supported R v) : Supported R (values ops v) := by
  induction ops generalizing v with
  | nil => exact hv
  | cons op ops ih =>
    exact ih (valueStep op v) (fun o h => ho o (by simp [h]))
      (step_supported R hR op v (ho op (by simp)) hv)

theorem bank_lt (n : ℕ) (side : Bool) (i : Fin n) : bank n side i < 4+2*n := by
  have hi := i.isLt
  cases side <;> simp [bank] <;> omega

theorem request_confined (R s d : ℕ) (hR : 4 ≤ R) (hs : s < R) :
    ∀ op ∈ request s d, Confined R op := by
  intro op ho
  simp only [request,List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp [Confined,hs]
  omega

theorem requests_confined (R : ℕ) (hR : 4 ≤ R) (ss : List ℕ) (rd : ℕ → ℕ)
    (hs : ∀ s ∈ ss, s < R) : ∀ op ∈ requests ss rd, Confined R op := by
  intro op ho
  obtain ⟨s,hss,hsop⟩ := List.mem_flatMap.mp ho
  exact request_confined R s (rd s) hR (hs s hss) op hsop

theorem site_confined (R : ℕ) (hR : 4 ≤ R) (ss : List ℕ) (t : ℕ) (rd : ℕ → ℕ)
    (wd : ℕ) (hs : ∀ s ∈ ss, s < R) (ht : t < R) :
    ∀ op ∈ site ss t rd wd, Confined R op := by
  intro op ho
  simp only [site,List.mem_append,List.mem_singleton] at ho
  rcases ho with (rfl | hr) | rfl
  · trivial
  · exact requests_confined R hR ss rd hs op hr
  · simp [Confined,ht]; omega

theorem layer_confined (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) : ∀ op ∈ layerSites n side menu rd wd sites,
      Confined (4+2*n) op := by
  induction sites with
  | nil => simp [layerSites]
  | cons i rest ih =>
    intro op ho
    rcases List.mem_append.mp ho with hs | hr
    · exact site_confined _ (by omega) _ _ _ _
        (by intro s hs; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs; exact bank_lt n side j)
        (bank_lt n (!side) i) op hs
    · exact ih op hr

theorem program_confined (n : ℕ) (rd wd : ℕ → ℕ) (side : Bool)
    (menus : List (Layer n)) : ∀ op ∈ program n rd wd side menus, Confined (4+2*n) op := by
  induction menus generalizing side with
  | nil => simp [program]
  | cons menu rest ih =>
    intro op ho
    rcases List.mem_append.mp ho with hl | hr
    · exact layer_confined n side menu rd wd _ op hl
    · exact ih (!side) op hr

def Shape (R : ℕ) (rd wd : ℕ → ℕ) : Op → Prop
  | .transfer s t d => (4 ≤ s ∧ s < R ∧ t = 3 ∧ d = rd s) ∨
      (s = 0 ∧ 4 ≤ t ∧ t < R ∧ d = wd t)
  | _ => True

theorem requests_shape (R : ℕ) (ss : List ℕ) (rd wd : ℕ → ℕ)
    (hs : ∀ s ∈ ss, 4 ≤ s ∧ s < R) : ∀ op ∈ requests ss rd, Shape R rd wd op := by
  intro op ho
  obtain ⟨s,hss,hsop⟩ := List.mem_flatMap.mp ho
  simp only [request,List.mem_cons,List.not_mem_nil,or_false] at hsop
  rcases hsop with rfl | rfl | rfl
  · exact Or.inl ⟨(hs s hss).1,(hs s hss).2,rfl,rfl⟩
  · trivial
  · trivial

theorem site_shape (R : ℕ) (ss : List ℕ) (t : ℕ) (rd wd : ℕ → ℕ)
    (hs : ∀ s ∈ ss, 4 ≤ s ∧ s < R) (ht : 4 ≤ t ∧ t < R) :
    ∀ op ∈ site ss t rd (wd t), Shape R rd wd op := by
  intro op ho
  simp only [site,List.mem_append,List.mem_singleton] at ho
  rcases ho with (rfl | hr) | rfl
  · trivial
  · exact requests_shape R ss rd wd hs op hr
  · exact Or.inr ⟨rfl,ht.1,ht.2,rfl⟩

theorem layer_shape (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) : ∀ op ∈ layerSites n side menu rd wd sites,
      Shape (4+2*n) rd wd op := by
  induction sites with
  | nil => simp [layerSites]
  | cons i rest ih =>
    intro op ho
    rcases List.mem_append.mp ho with hs | hr
    · exact site_shape _ _ _ _ _
        (by intro s hs; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hs
            exact ⟨bank_ge n side j,bank_lt n side j⟩)
        ⟨bank_ge n (!side) i,bank_lt n (!side) i⟩ op hs
    · exact ih op hr

theorem program_shape (n : ℕ) (rd wd : ℕ → ℕ) (side : Bool)
    (menus : List (Layer n)) : ∀ op ∈ program n rd wd side menus, Shape (4+2*n) rd wd op := by
  induction menus generalizing side with
  | nil => simp [program]
  | cons menu rest ih =>
    intro op ho
    rcases List.mem_append.mp ho with hl | hr
    · exact layer_shape n side menu rd wd _ op hl
    · exact ih (!side) op hr

end OPH.SourceBankInvariant

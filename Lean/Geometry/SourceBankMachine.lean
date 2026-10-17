module
public import Geometry.SourceNativeProgramBudget

@[expose] public section

/-!
# A bank compiler with derived logical outputs

The instruction stream depends on finite request lists and route depths,
never on payloads. Two disjoint banks make the preceding layer readable
throughout the next layer, including after other outputs have been stored.
This module proves the compiler's logical semantics. Native lowering and
its geometric obligations are separate from this integer computation.
-/

set_option autoImplicit false

namespace OPH.SourceBankMachine

abbrev Values := ℕ → ℤ
abbrev Scales := ℕ → ℕ

inductive Op where
  | start
  | add
  | retire
  | transfer (source target depth : ℕ)
  deriving DecidableEq, Repr

def valueStep : Op → Values → Values
  | .start, v => fun i => if i = 0 then v 2 else if i = 1 then 0 else v i
  | .add, v => fun i => if i = 0 then v 0+v 3 else v i
  | .retire, v => fun i => if i = 1 ∨ i = 3 then 0 else v i
  | .transfer s t _, v => fun i => if i = t then v s else v i

def scaleStep : Op → Scales → Scales
  | .start, e => fun i => if i = 0 ∨ i = 2 then e 2+1 else e i
  | .add, e => fun i => if i = 0 then max (e 0) (e 3+1)+1
      else if i = 3 then max (e 0) (e 3+1) else e i
  | .retire, e => e
  | .transfer s t d, e => fun i => if i = t then e s+d
      else if i = s then e s+1 else e i

def values : List Op → Values → Values
  | [], v => v
  | op::ops, v => values ops (valueStep op v)

def scales : List Op → Scales → Scales
  | [], e => e
  | op::ops, e => scales ops (scaleStep op e)

theorem values_append (ops rest : List Op) (v : Values) :
    values (ops++rest) v = values rest (values ops v) := by
  induction ops generalizing v with
  | nil => rfl
  | cons op ops ih => exact ih _

theorem scales_append (ops rest : List Op) (e : Scales) :
    scales (ops++rest) e = scales rest (scales ops e) := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih => exact ih _

def request (s d : ℕ) : List Op := [.transfer s 3 d, .add, .retire]

theorem request_values (s d : ℕ) (v : Values) :
    values (request s d) v = fun i => if i = 0 then v 0+v s
      else if i = 1 ∨ i = 3 then 0 else v i := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h3 : i = 3 <;>
    simp [request, values, valueStep, h0, h1, h3]

def requests (ss : List ℕ) (depth : ℕ → ℕ) : List Op :=
  ss.flatMap (fun s => request s (depth s))

theorem requests_frame (ss : List ℕ) (depth : ℕ → ℕ) (v : Values)
    (i : ℕ) (hi : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 3) :
    values (requests ss depth) v i = v i := by
  induction ss generalizing v with
  | nil => rfl
  | cons s ss ih =>
    rw [requests, List.flatMap_cons, values_append]
    rw [show List.flatMap (fun s => request s (depth s)) ss = requests ss depth from rfl,
      ih, request_values]
    simp [hi.1, hi.2.1, hi.2.2]

theorem requests_sum (ss : List ℕ) (depth : ℕ → ℕ)
    (hs : ∀ s ∈ ss, 4 ≤ s) (v : Values) :
    values (requests ss depth) v 0 = v 0+(ss.map v).sum := by
  induction ss generalizing v with
  | nil => simp [requests, values]
  | cons s ss ih =>
    rw [requests, List.flatMap_cons, values_append]
    rw [show List.flatMap (fun s => request s (depth s)) ss = requests ss depth from rfl,
      ih (fun t ht => hs t (by simp [ht]))]
    have hm : ss.map (values (request s (depth s)) v) = ss.map v := by
      apply List.map_congr_left
      intro t ht
      have hb := hs t (by simp [ht])
      rw [request_values]
      simp [show t ≠ 0 by omega, show t ≠ 1 by omega, show t ≠ 3 by omega]
    rw [hm, request_values]
    simp [add_assoc]

def site (ss : List ℕ) (target : ℕ) (readDepth : ℕ → ℕ) (writeDepth : ℕ) : List Op :=
  [.start] ++ requests ss readDepth ++ [.transfer 0 target writeDepth]

theorem site_output (ss : List ℕ) (target : ℕ) (rd : ℕ → ℕ) (wd : ℕ)
    (hs : ∀ s ∈ ss, 4 ≤ s) (v : Values) :
    values (site ss target rd wd) v target = v 2+(ss.map v).sum := by
  simp only [site, values_append, values, valueStep]
  rw [requests_sum ss rd hs]
  have hm : ss.map (valueStep .start v) = ss.map v := by
    apply List.map_congr_left
    intro s hs'
    have hb := hs s hs'
    simp [valueStep, show s ≠ 0 by omega, show s ≠ 1 by omega]
  simpa [valueStep] using congrArg (fun z => v 2+z.sum) hm

theorem site_frame (ss : List ℕ) (target : ℕ) (rd : ℕ → ℕ) (wd : ℕ)
    (v : Values) (i : ℕ) (hi : i ≠ 0 ∧ i ≠ 1 ∧ i ≠ 3 ∧ i ≠ target) :
    values (site ss target rd wd) v i = v i := by
  simp only [site, values_append, values, valueStep, ite_eq_right hi.2.2.2]
  rw [requests_frame ss rd _ i ⟨hi.1,hi.2.1,hi.2.2.1⟩]
  simp [hi.1, hi.2.1]

def bank (n : ℕ) (side : Bool) (i : Fin n) : ℕ :=
  4+(if side then n else 0)+i.val

theorem bank_ge (n : ℕ) (side : Bool) (i : Fin n) : 4 ≤ bank n side i := by
  unfold bank
  omega

theorem bank_injective (n : ℕ) (side : Bool) : Function.Injective (bank n side) := by
  intro i j h
  apply Fin.ext
  simpa [bank] using h

theorem banks_disjoint (n : ℕ) (side : Bool) (i j : Fin n) :
    bank n side i ≠ bank n (!side) j := by
  have hi := i.isLt
  have hj := j.isLt
  cases side <;> simp [bank] <;> omega

abbrev Layer (n : ℕ) := Fin n → List (Fin n)

def layerSites (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ) :
    List (Fin n) → List Op
  | [] => []
  | i::rest => site ((menu i).map (bank n side)) (bank n (!side) i)
      rd (wd (bank n (!side) i)) ++ layerSites n side menu rd wd rest

theorem layer_input (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) (v : Values) (i : Fin n) :
    values (layerSites n side menu rd wd sites) v (bank n side i) = v (bank n side i) := by
  induction sites generalizing v with
  | nil => rfl
  | cons j rest ih =>
    rw [layerSites, values_append, ih]
    have hb := bank_ge n side i
    exact site_frame _ _ _ _ v _ ⟨by omega,by omega,by omega,banks_disjoint n side i j⟩

theorem layer_unit (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) (v : Values) :
    values (layerSites n side menu rd wd sites) v 2 = v 2 := by
  induction sites generalizing v with
  | nil => rfl
  | cons j rest ih =>
    rw [layerSites, values_append, ih]
    have hb := bank_ge n (!side) j
    exact site_frame _ _ _ _ v 2 ⟨by decide,by decide,by decide,by omega⟩

theorem layer_output_unwritten (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) (v : Values) (i : Fin n) (hi : i ∉ sites) :
    values (layerSites n side menu rd wd sites) v (bank n (!side) i) = v (bank n (!side) i) := by
  induction sites generalizing v with
  | nil => rfl
  | cons j rest ih =>
    have hrest : i ∉ rest := fun h => hi (by simp [h])
    have hij : i ≠ j := fun h => hi (by simp [h])
    rw [layerSites, values_append, ih _ hrest]
    have hb := bank_ge n (!side) i
    exact site_frame _ _ _ _ v _ ⟨by omega,by omega,by omega,
      fun h => hij (bank_injective n (!side) h)⟩

theorem layer_output (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (sites : List (Fin n)) (hn : sites.Nodup) (v : Values) (i : Fin n) (hi : i ∈ sites) :
    values (layerSites n side menu rd wd sites) v (bank n (!side) i) =
      v 2+((menu i).map (fun j => v (bank n side j))).sum := by
  induction sites generalizing v with
  | nil => simp at hi
  | cons j rest ih =>
    obtain ⟨hjr,hr⟩ := List.nodup_cons.mp hn
    rw [layerSites, values_append]
    rcases List.mem_cons.mp hi with hij | hir
    · subst i
      rw [layer_output_unwritten n side menu rd wd rest _ j hjr,
        site_output _ _ _ _ (by intro s hs; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs; exact bank_ge n side a)]
      simp [List.map_map, Function.comp_def]
    · rw [ih hr _ hir]
      have hu : values (site ((menu j).map (bank n side)) (bank n (!side) j)
          rd (wd (bank n (!side) j))) v 2 = v 2 := by
        have hb := bank_ge n (!side) j
        exact site_frame _ _ _ _ v 2 ⟨by decide,by decide,by decide,by omega⟩
      rw [hu]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      have hb := bank_ge n side a
      exact site_frame _ _ _ _ v _ ⟨by omega,by omega,by omega,banks_disjoint n side a j⟩

def layer (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ) : List Op :=
  layerSites n side menu rd wd (List.finRange n)

theorem layer_recurrence (n : ℕ) (side : Bool) (menu : Layer n) (rd wd : ℕ → ℕ)
    (v : Values) (i : Fin n) :
    values (layer n side menu rd wd) v (bank n (!side) i) =
      v 2+((menu i).map (fun j => v (bank n side j))).sum :=
  layer_output n side menu rd wd _ (List.nodup_finRange n) v i (List.mem_finRange i)

def program (n : ℕ) (rd wd : ℕ → ℕ) : Bool → List (Layer n) → List Op
  | _, [] => []
  | side, menu::rest => layer n side menu rd wd ++ program n rd wd (!side) rest

def finalSide {α : Type*} : Bool → List α → Bool
  | side, [] => side
  | side, _::rest => finalSide (!side) rest

def recurrence (n : ℕ) (unit : ℤ) : List (Layer n) → (Fin n → ℤ) → (Fin n → ℤ)
  | [], v => v
  | menu::rest, v => recurrence n unit rest (fun i => unit+((menu i).map v).sum)

theorem program_unit (n : ℕ) (rd wd : ℕ → ℕ) (side : Bool)
    (menus : List (Layer n)) (v : Values) : values (program n rd wd side menus) v 2 = v 2 := by
  induction menus generalizing side v with
  | nil => rfl
  | cons menu rest ih =>
    rw [program, values_append, ih]
    exact layer_unit n side menu rd wd _ v

/-- The final bank contains the iterated recurrence. The conclusion is
derived from the emitted instructions, including writes followed by reads
in later layers; it is not a correctness premise of the native backend. -/
theorem program_recurrence (n : ℕ) (rd wd : ℕ → ℕ) (side : Bool)
    (menus : List (Layer n)) (v : Values) (i : Fin n) :
    values (program n rd wd side menus) v (bank n (finalSide side menus) i) =
      recurrence n (v 2) menus (fun j => v (bank n side j)) i := by
  induction menus generalizing side v with
  | nil => rfl
  | cons menu rest ih =>
    rw [program, values_append]
    change values (program n rd wd (!side) rest) (values (layer n side menu rd wd) v)
      (bank n (finalSide (!side) rest) i) = _
    rw [ih]
    have hu := layer_unit n side menu rd wd (List.finRange n) v
    change values (layer n side menu rd wd) v 2 = v 2 at hu
    rw [hu]
    have hi : (fun j => values (layer n side menu rd wd) v (bank n (!side) j)) =
        fun j => v 2+((menu j).map (fun s => v (bank n side s))).sum := by
      funext j
      exact layer_recurrence n side menu rd wd v j
    rw [hi]
    rfl

theorem sum_bound {α : Type*} (ss : List α) (v cap : α → ℤ)
    (hv : ∀ i, |v i| ≤ cap i) : |(ss.map v).sum| ≤ (ss.map cap).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (hv s) ih)

/-- Public caps propagate through the same requested sums without knowing
any payload. Signed cancellation never invalidates the bound. -/
theorem recurrence_bound (n : ℕ) (unit : ℤ) (menus : List (Layer n))
    (v cap : Fin n → ℤ) (hv : ∀ i, |v i| ≤ cap i) :
    ∀ i, |recurrence n unit menus v i| ≤ recurrence n |unit| menus cap i := by
  induction menus generalizing v cap with
  | nil => exact hv
  | cons menu rest ih =>
    apply ih
    intro i
    exact (abs_add_le _ _).trans (add_le_add (le_refl _) (sum_bound (menu i) v cap hv))

def scaleCharge : Op → ℕ
  | .start => 1
  | .add => 2
  | .retire => 0
  | .transfer _ _ d => d+1

theorem scale_step_bound (op : Op) (e : Scales) (M : ℕ) (h : ∀ i, e i ≤ M) :
    ∀ i, scaleStep op e i ≤ M+scaleCharge op := by
  intro i
  cases op with
  | start => simp only [scaleStep, scaleCharge]; split <;> have := h i <;> have := h 2 <;> omega
  | add =>
    have h0 := h 0
    have h3 := h 3
    have hi := h i
    simp only [scaleStep, scaleCharge, Nat.max_def]
    split_ifs <;> omega
  | retire => exact h i
  | transfer s t d =>
    have hi := h i
    have hs := h s
    simp only [scaleStep, scaleCharge]
    split_ifs <;> omega

theorem scales_bound (ops : List Op) (e : Scales) (M : ℕ) (h : ∀ i, e i ≤ M) :
    ∀ i, scales ops e i ≤ M+(ops.map scaleCharge).sum := by
  induction ops generalizing e M with
  | nil => simpa [scales] using h
  | cons op ops ih =>
    have hb := ih (scaleStep op e) (M+scaleCharge op) (scale_step_bound op e M h)
    simpa [scales, add_assoc] using hb

def opWork (op : Op) (k : ℕ) (e : Scales) : ℕ :=
  match op with
  | .start => 3*k+3
  | .add => 3*(max (e 0) (e 3+1)-e 0)+3*(max (e 0) (e 3+1)-(e 3+1))+5
  | .retire => 4
  | .transfer _ t d => (if t = 3 then 4 else 5)+2*(d-2)+
      (1+2*(d-2))*(d-2+1)^2*k

def work : List Op → ℕ → Scales → ℕ
  | [], _, _ => 0
  | op::ops, k, e => opWork op k e+work ops k (scaleStep op e)

def cleanupCharge : Op → ℕ
  | .start => 1
  | .transfer _ _ d => (d-1)^2
  | _ => 0

def cleanupBudget (ops : List Op) : ℕ := (ops.map cleanupCharge).sum

theorem work_append (ops rest : List Op) (k : ℕ) (e : Scales) :
    work (ops++rest) k e = work ops k e+work rest k (scales ops e) := by
  induction ops generalizing e with
  | nil => simp [work,scales]
  | cons op ops ih => simp [work,scales,ih,add_assoc]

end OPH.SourceBankMachine

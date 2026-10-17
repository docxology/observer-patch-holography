module
public import Geometry.SourceBankCompiler

@[expose] public section

/-!
# An inhabited finite bus for every finite bank program

This explicit bus uses the workspace and two scratch cells. It witnesses
the compiler's route premises for every width and every finite request
program. Its star connections are declared graph data; they do not prove an
embedding into the captured W12 graph or source selection.
-/

set_option autoImplicit false

namespace OPH.SourceBankBusWitness
noncomputable section
open OPH.SourceBankMachine OPH.SourceBankInvariant OPH.SourceBankLowering
open OPH.SourceBankCompiler OPH.SourceNativeStoredProgram OPH.SourceEncodedMemory
open OPH.SourceNativeShuttle

def readCells (R s : ℕ) : Equiv.Perm ℕ :=
  (((Equiv.swap 0 R).trans (Equiv.swap 1 (R+1))).trans
    (Equiv.swap 2 3)).trans (Equiv.swap 2 s)

def writeCells (R t : ℕ) : Equiv.Perm ℕ :=
  (((Equiv.swap 0 1).trans (Equiv.swap 0 R)).trans
    (Equiv.swap 2 t)).trans (Equiv.swap 3 0)

theorem read_cells (R s : ℕ) (hs : 4 ≤ s) (hR : s < R) :
    readCells R s 0 = R ∧ readCells R s 1 = R+1 ∧
      readCells R s 2 = 3 ∧ readCells R s 3 = s := by
  have hn : ∀ i < 4, i ≠ s ∧ i ≠ R ∧ i ≠ R+1 := by intro i hi; omega
  have hr : R ≠ R+1 ∧ R ≠ s ∧ R+1 ≠ s := by omega
  simp [readCells,Equiv.trans_apply,Equiv.swap_apply_def,
    hn 1 (by omega),hn 2 (by omega),hn 3 (by omega)]
  split_ifs <;> omega

theorem write_cells (R t : ℕ) (ht : 4 ≤ t) (hR : t < R) :
    writeCells R t 0 = 1 ∧ writeCells R t 1 = R ∧
      writeCells R t 2 = t ∧ writeCells R t 3 = 0 := by
  have hn : ∀ i < 4, i ≠ t ∧ i ≠ R := by intro i hi; omega
  have hr : R ≠ t := by omega
  simp [writeCells,Equiv.trans_apply,Equiv.swap_apply_def,
    hn 1 (by omega),hn 2 (by omega),hn 3 (by omega),hr]
  split_ifs <;> omega

def readRoute (R s : ℕ) (hs : 4 ≤ s) (hR : s < R) : Route s 3 3 where
  cells := readCells R s
  depth_pos := by decide
  source_eq := (read_cells R s hs hR).2.2.2
  target_eq := (read_cells R s hs hR).2.2.1

def writeRoute (R t : ℕ) (ht : 4 ≤ t) (hR : t < R) : Route 0 t 3 where
  cells := writeCells R t
  depth_pos := by decide
  source_eq := (write_cells R t ht hR).2.2.2
  target_eq := (write_cells R t ht hR).2.2.1

theorem read_scratch (R s : ℕ) (hs : 4 ≤ s) (hR : s < R) :
    ∀ i < 3-1, (readRoute R s hs hR).cells i = 1 ∨ R ≤ (readRoute R s hs hR).cells i := by
  intro i hi
  have hh := read_cells R s hs hR
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inr (by simp [readRoute,hh.1])
  · exact Or.inr (by simp [readRoute,hh.2.1])

theorem write_scratch (R t : ℕ) (ht : 4 ≤ t) (hR : t < R) :
    ∀ i < 3-1, (writeRoute R t ht hR).cells i = 1 ∨ R ≤ (writeRoute R t ht hR).cells i := by
  intro i hi
  have hh := write_cells R t ht hR
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inl hh.1
  · exact Or.inr (by simp [writeRoute,hh.2.1])

def routeFor (R s t d : ℕ) (h : Shape R (fun _ => 3) (fun _ => 3) (.transfer s t d)) :
    Route s t d := by
  have hd : d = 3 := by rcases h with h | h; exact h.2.2.2; exact h.2.2.2
  subst d
  by_cases ht : t = 3
  · have hs : 4 ≤ s ∧ s < R := by
      rcases h with h | h
      · exact ⟨h.1,h.2.1⟩
      · omega
    subst t
    exact readRoute R s hs.1 hs.2
  · have hs : s = 0 ∧ 4 ≤ t ∧ t < R := by
      rcases h with h | h
      · exact False.elim (ht h.2.2.1)
      · exact ⟨h.1,h.2.1,h.2.2.1⟩
    have hs0 := hs.1
    subst s
    exact writeRoute R t hs.2.1 hs.2.2

theorem routeFor_scratch (R s t d : ℕ)
    (h : Shape R (fun _ => 3) (fun _ => 3) (.transfer s t d)) :
    ∀ i < d-1, (routeFor R s t d h).cells i = 1 ∨ R ≤ (routeFor R s t d h).cells i := by
  have hd : d = 3 := by rcases h with h | h; exact h.2.2.2; exact h.2.2.2
  subst d
  by_cases ht : t = 3
  · have hs : 4 ≤ s ∧ s < R := by rcases h with h | h; exact ⟨h.1,h.2.1⟩; omega
    subst t
    simpa [routeFor] using read_scratch R s hs.1 hs.2
  · have hs : s = 0 ∧ 4 ≤ t ∧ t < R := by
      rcases h with h | h
      · exact False.elim (ht h.2.2.1)
      · exact ⟨h.1,h.2.1,h.2.2.1⟩
    obtain ⟨rfl,ht4,htR⟩ := hs
    simpa [routeFor,ht] using write_scratch R t ht4 htR

def place (R : ℕ) : (ops : List Op) →
    (∀ op ∈ ops, Shape R (fun _ => 3) (fun _ => 3) op) → Placed ops
  | [], _ => .nil
  | .start::ops, h => .start (place R ops (fun op ho => h op (by simp [ho])))
  | .add::ops, h => .add (place R ops (fun op ho => h op (by simp [ho])))
  | .retire::ops, h => .retire (place R ops (fun op ho => h op (by simp [ho])))
  | .transfer s t d::ops, h => .transfer (routeFor R s t d (h _ (by simp)))
      (place R ops (fun op ho => h op (by simp [ho])))

theorem place_scratch (R : ℕ) (ops : List Op)
    (h : ∀ op ∈ ops, Shape R (fun _ => 3) (fun _ => 3) op) : Scratch R (place R ops h) := by
  induction ops with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | start => exact ih _
    | add => exact ih _
    | retire => exact ih _
    | transfer s t d => exact ⟨routeFor_scratch R s t d _,ih _⟩

def placement (n : ℕ) (side : Bool) (menus : List (Layer n)) :
    Placed (program n (fun _ => 3) (fun _ => 3) side menus) :=
  place (4+2*n) _ (program_shape n (fun _ => 3) (fun _ => 3) side menus)

theorem placement_scratch (n : ℕ) (side : Bool) (menus : List (Layer n)) :
    Scratch (4+2*n) (placement n side menus) := place_scratch _ _ _

/-- Every finite typed request program has an actual native construction on
this declared bus; route existence is discharged by explicit permutations. -/
theorem every_program_native (n : ℕ) (side : Bool) (menus : List (Layer n))
    (k : ℕ) (b g A : ℝ) (v : Values) (e : Scales) (hA : 0 ≤ A)
    (ha : Bounded A (amplitude g v e)) (hc : Clean v) (hv : Supported (4+2*n) v) :
    Construction (encode b (amplitude g v e))
      (encode b (amplitude g (values (program n (fun _ => 3) (fun _ => 3) side menus) v)
        (scales (program n (fun _ => 3) (fun _ => 3) side menus) e)))
      (nativeWord (placement n side menus) k e) (error (placement n side menus) k A) :=
  compiled_program _ _ side menus (placement n side menus) k b g A v e
    hA ha hc hv (placement_scratch n side menus)

end
end OPH.SourceBankBusWitness

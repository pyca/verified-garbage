import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.PairedTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

def first (z bar : Nat → Nat) : List Nat :=
 (List.range 8).flatMap fun block =>
  [1,2,4,8,16].flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 256/len-1-(32*block)/(2*len)-(if len=1 then 4*g else if len=2 then 2*g else g)
    let zs := if len=1 then (List.range 4).map fun j => z (idx-j)
     else if len=2 then [z idx,z idx,z (idx-1),z (idx-1)]
     else List.replicate 4 (z idx)
    zs ++ zs.map bar

def firstLayout : List (Nat × Bool) :=
 (List.range 8).flatMap fun block =>
  ([1,2,4,8,16] : List Nat).flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 256/len-1-(32*block)/(2*len)-(if len=1 then 4*g else if len=2 then 2*g else g)
    let zs := if len=1 then (List.range 4).map (fun j => idx-j)
     else if len=2 then [idx,idx,idx-1,idx-1]
     else List.replicate 4 idx
    zs.map (fun z => (z,false)) ++ zs.map (fun z => (z,true))

theorem firstLayout_eq : firstLayout = InverseTable.layout.take 960 := by decide +kernel

private theorem map_if {α β : Type} (f : α → β) (p : Prop) [Decidable p] (a b : List α) :
    (if p then a else b).map f = if p then a.map f else b.map f := by
  split <;> rfl

theorem first_layout (z bar : Nat → Nat) :
    first z bar = (InverseTable.layout.take 960).map
      (fun p => if p.2 then bar (z p.1) else z p.1) := by
  rw [← firstLayout_eq]
  simp only [first,firstLayout,List.map_append,List.map_flatMap,List.map_map,
    map_if,List.map_replicate,List.map_cons,List.map_nil,Function.comp_def,
    Bool.false_eq_true,ite_false,ite_true]

def tailRoot (j : Nat) : Nat :=
  if j=7 then 16382 else if j=6 then (z 1*16382)%8380417 else z (7-j)

def tailLayout : List (Nat × Bool) :=
  (List.range 8).flatMap fun j => List.replicate 4 (j,false) ++ List.replicate 4 (j,true)

def tailValue (p : Nat × Bool) : Nat := if p.2 then bar (tailRoot p.1) else tailRoot p.1

theorem expandedVals_layout : expandedVals =
    (InverseTable.layout.take 960).map InverseTable.value ++ tailLayout.map tailValue := by
  change first z bar ++ _ = _
  rw [first_layout]
  simp only [tailLayout,tailValue,List.map_flatMap,List.map_append,List.map_replicate,
    Bool.false_eq_true,ite_false,ite_true,tailRoot]
  rfl

theorem tailLayout_length : tailLayout.length=64 := by decide +kernel

theorem expandedVals_length : expandedVals.length=1024 := by
  rw [expandedVals_layout,List.length_append,List.length_map,List.length_map,
    List.length_take,InverseTable.layout_length,tailLayout_length]
  decide

theorem tail_layout : ∀ j : Fin 8, ∀ e : Fin 4,
    tailLayout[8*j.val+e.val]! = (j.val,false) ∧
    tailLayout[8*j.val+e.val+4]! = (j.val,true) := by decide +kernel

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable

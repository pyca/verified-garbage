import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt

namespace VG.Proof.MlDsa.AArch64.Optimized.TableConstants
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Symbolic table layout: root index and whether the word is its reciprocal.
Checking this small layout never evaluates modular exponentiation. -/
def layout : List (Nat × Bool) :=
 let first := (List.range 8).flatMap fun block =>
  ([16,8,4,2,1] : List Nat).flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 128/len+32*block/(2*len)+(if len=2 then 2*g else if len=1 then 4*g else g)
    let zs := if len=1 then (List.range 4).map (fun j => idx+j)
     else if len=2 then [idx,idx,idx+1,idx+1]
     else List.replicate 4 idx
    zs.map (fun z => (z,false)) ++ zs.map (fun z => (z,true))
 first ++ (List.range 8).flatMap (fun i => [(i+1,false),(i+1,true)])

def value (p : Nat × Bool) : Nat :=
 if p.2 then zetaTab p.1 * 2^31 / 8380417 else zetaTab p.1

private theorem map_if {α β : Type} (f : α → β) (p : Prop) [Decidable p] (a b : List α) :
    (if p then a else b).map f = if p then a.map f else b.map f := by
  split <;> rfl

theorem expandedVals_layout : expandedVals = layout.map value := by
  simp only [expandedVals,layout,List.map_append,List.map_flatMap,List.map_map,
    map_if,List.map_replicate,List.map_cons,List.map_nil,Function.comp_def,value,
    Bool.false_eq_true,ite_false,ite_true]

/-- The entry of `layout` at `i`, in closed form: in each block of 120, the
roots of layers 16 (8 words), 8 (16), 4 (32), 2 (32) and 1 (32), then the
hoisted roots. -/
def layoutAt (i : Nat) : Nat × Bool :=
  if i < 960 then
    let u := i / 120
    let r := i % 120
    if r < 8 then (8+u, decide (4 ≤ r%8))
    else if r < 24 then (16+2*u+(r-8)/8, decide (4 ≤ r%8))
    else if r < 56 then (32+4*u+(r-24)/8, decide (4 ≤ r%8))
    else if r < 88 then (64+8*u+2*((r-56)/8)+(r%4)/2, decide (4 ≤ r%8))
    else (128+16*u+4*((r-88)/8)+r%4, decide (4 ≤ r%8))
  else ((i-960)/2+1, decide ((i-960)%2 = 1))

/-- `layout` in closed form, compared once. -/
theorem layout_eq : layout = (List.range 976).map layoutAt :=
  eq_of_beq (by decide +kernel : (layout == (List.range 976).map layoutAt) = true)

theorem layout_get {i : Nat} (hi : i < 976) : layout[i]! = layoutAt i := by
  rw [layout_eq, getElem!_pos ((List.range 976).map layoutAt) i (by simpa using hi),
    List.getElem_map, List.getElem_range]

theorem layout_length : layout.length = 976 := by
  rw [layout_eq, List.length_map, List.length_range]

theorem expandedVals_length : expandedVals.length = 976 := by
  rw [expandedVals_layout,List.length_map,layout_length]

theorem inner4_layout : ∀ u : Fin 8, ∀ e : Fin 4,
    layout[120*u.val+e.val]! = (8+u.val,false) ∧
    layout[120*u.val+e.val+4]! = (8+u.val,true) := by
  have h : ∀ u : Fin 8, ∀ e : Fin 4,
      layoutAt (120*u.val+e.val) = (8+u.val,false) ∧
      layoutAt (120*u.val+e.val+4) = (8+u.val,true) := by
    decide +kernel
  intro u e
  rw [layout_get (by omega), layout_get (by omega)]
  exact h u e

theorem inner2_layout : ∀ u : Fin 8, ∀ g : Fin 2, ∀ e : Fin 4,
    layout[120*u.val+8+8*g.val+e.val]! = (16+2*u.val+g.val,false) ∧
    layout[120*u.val+8+8*g.val+e.val+4]! = (16+2*u.val+g.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 2, ∀ e : Fin 4,
      layoutAt (120*u.val+8+8*g.val+e.val) = (16+2*u.val+g.val,false) ∧
      layoutAt (120*u.val+8+8*g.val+e.val+4) = (16+2*u.val+g.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega), layout_get (by omega)]
  exact h u g e

theorem inner1_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+24+8*g.val+e.val]! = (32+4*u.val+g.val,false) ∧
    layout[120*u.val+24+8*g.val+e.val+4]! = (32+4*u.val+g.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+24+8*g.val+e.val) = (32+4*u.val+g.val,false) ∧
      layoutAt (120*u.val+24+8*g.val+e.val+4) = (32+4*u.val+g.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega), layout_get (by omega)]
  exact h u g e

theorem tail2_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+56+8*g.val+e.val]! = (64+8*u.val+2*g.val+e.val/2,false) ∧
    layout[120*u.val+56+8*g.val+e.val+4]! = (64+8*u.val+2*g.val+e.val/2,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+56+8*g.val+e.val) = (64+8*u.val+2*g.val+e.val/2,false) ∧
      layoutAt (120*u.val+56+8*g.val+e.val+4) = (64+8*u.val+2*g.val+e.val/2,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega), layout_get (by omega)]
  exact h u g e

theorem tail1_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+88+8*g.val+e.val]! = (128+16*u.val+4*g.val+e.val,false) ∧
    layout[120*u.val+88+8*g.val+e.val+4]! = (128+16*u.val+4*g.val+e.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+88+8*g.val+e.val) = (128+16*u.val+4*g.val+e.val,false) ∧
      layoutAt (120*u.val+88+8*g.val+e.val+4) = (128+16*u.val+4*g.val+e.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega), layout_get (by omega)]
  exact h u g e

theorem hoisted_layout : ∀ i : Fin 8,
    layout[960+2*i.val]! = (i.val+1,false) ∧
    layout[960+2*i.val+1]! = (i.val+1,true) := by
  have h : ∀ i : Fin 8,
      layoutAt (960+2*i.val) = (i.val+1,false) ∧
      layoutAt (960+2*i.val+1) = (i.val+1,true) := by
    decide +kernel
  intro i
  rw [layout_get (by omega), layout_get (by omega)]
  exact h i

end VG.Proof.MlDsa.AArch64.Optimized.TableConstants

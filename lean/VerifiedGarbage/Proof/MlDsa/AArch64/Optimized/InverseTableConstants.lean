module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Inverse

/-! ### `MlDsa.AArch64.Optimized.InverseTableLayout`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTable
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

/-- Root indices and reciprocal flags, independent of modular powers. -/
def layout : List (Nat × Bool) :=
 let first := (List.range 8).flatMap fun block =>
  ([1,2,4,8,16] : List Nat).flatMap fun len =>
   (List.range (if len<4 then 4 else 16/len)).flatMap fun g =>
    let idx := 256/len-1-(32*block)/(2*len)-(if len=1 then 4*g else if len=2 then 2*g else g)
    let zs := if len=1 then (List.range 4).map (fun j => idx-j)
     else if len=2 then [idx,idx,idx-1,idx-1]
     else List.replicate 4 idx
    zs.map (fun z => (z,false)) ++ zs.map (fun z => (z,true))
 let last := (List.range 8).map fun j => 7-j
 first ++ last.map (fun z => (z,false)) ++ last.map (fun z => (z,true))

def value (p : Nat × Bool) : Nat := if p.2 then bar (z p.1) else z p.1

private theorem map_if {α β : Type} (f : α → β) (p : Prop) [Decidable p] (a b : List α) :
    (if p then a else b).map f = if p then a.map f else b.map f := by
  split <;> rfl

theorem expandedVals_layout : expandedVals = layout.map value := by
  simp only [expandedVals,layout,List.map_append,List.map_flatMap,List.map_map,
    map_if,List.map_replicate,List.map_cons,List.map_nil,Function.comp_def,value,
    Bool.false_eq_true,ite_false,ite_true,List.append_assoc]

/-- The entry of `layout` at `i`, in closed form: in each block of 120, the
roots of layers 1 (32 words), 2 (32), 4 (32), 8 (16) and 16 (8), then the
last roots. -/
def layoutAt (i : Nat) : Nat × Bool :=
  if i < 960 then
    let u := i / 120
    let r := i % 120
    if r < 32 then (255-16*u-4*(r/8)-r%4, decide (4 ≤ r%8))
    else if r < 64 then (127-8*u-2*((r-32)/8)-(r%4)/2, decide (4 ≤ r%8))
    else if r < 96 then (63-4*u-(r-64)/8, decide (4 ≤ r%8))
    else if r < 112 then (31-2*u-(r-96)/8, decide (4 ≤ r%8))
    else (15-u, decide (4 ≤ r%8))
  else (7-(i-960)%8, decide (968 ≤ i))

/-- `layout` in closed form, compared once. -/
theorem layout_eq : layout = (List.range 976).map layoutAt :=
  eq_of_beq (by decide +kernel : (layout == (List.range 976).map layoutAt) = true)

theorem layout_get {i : Nat} (hi : i < 976) : layout[i]! = layoutAt i := by
  rw [layout_eq, getElem!_pos ((List.range 976).map layoutAt) i (by simpa using hi),
    List.getElem_map, List.getElem_range]

theorem layout_length : layout.length = 976 := by
  rw [layout_eq, List.length_map, List.length_range]

theorem expandedVals_length : expandedVals.length=976 := by
  rw [expandedVals_layout,List.length_map,layout_length]

theorem layer1_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+8*g.val+e.val]! = (255-16*u.val-4*g.val-e.val,false) ∧
    layout[120*u.val+8*g.val+e.val+4]! = (255-16*u.val-4*g.val-e.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+8*g.val+e.val) = (255-16*u.val-4*g.val-e.val,false) ∧
      layoutAt (120*u.val+8*g.val+e.val+4) = (255-16*u.val-4*g.val-e.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem layer2_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+32+8*g.val+e.val]! = (127-8*u.val-2*g.val-e.val/2,false) ∧
    layout[120*u.val+32+8*g.val+e.val+4]! = (127-8*u.val-2*g.val-e.val/2,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+32+8*g.val+e.val) = (127-8*u.val-2*g.val-e.val/2,false) ∧
      layoutAt (120*u.val+32+8*g.val+e.val+4) = (127-8*u.val-2*g.val-e.val/2,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem layer4_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+64+8*g.val+e.val]! = (63-4*u.val-g.val,false) ∧
    layout[120*u.val+64+8*g.val+e.val+4]! = (63-4*u.val-g.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+64+8*g.val+e.val) = (63-4*u.val-g.val,false) ∧
      layoutAt (120*u.val+64+8*g.val+e.val+4) = (63-4*u.val-g.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem layer8_layout : ∀ u : Fin 8, ∀ g : Fin 2, ∀ e : Fin 4,
    layout[120*u.val+96+8*g.val+e.val]! = (31-2*u.val-g.val,false) ∧
    layout[120*u.val+96+8*g.val+e.val+4]! = (31-2*u.val-g.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 2, ∀ e : Fin 4,
      layoutAt (120*u.val+96+8*g.val+e.val) = (31-2*u.val-g.val,false) ∧
      layoutAt (120*u.val+96+8*g.val+e.val+4) = (31-2*u.val-g.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem layer16_layout : ∀ u : Fin 8, ∀ e : Fin 4,
    layout[120*u.val+112+e.val]! = (15-u.val,false) ∧
    layout[120*u.val+112+e.val+4]! = (15-u.val,true) := by
  have h : ∀ u : Fin 8, ∀ e : Fin 4,
      layoutAt (120*u.val+112+e.val) = (15-u.val,false) ∧
      layoutAt (120*u.val+112+e.val+4) = (15-u.val,true) := by
    decide +kernel
  intro u e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u e

theorem tail_layout : ∀ j : Fin 8,
    layout[960+j.val]! = (7-j.val,false) ∧ layout[968+j.val]! = (7-j.val,true) := by
  have h : ∀ j : Fin 8,
      layoutAt (960+j.val) = (7-j.val,false) ∧ layoutAt (968+j.val) = (7-j.val,true) := by
    decide +kernel
  intro j
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h j

end VG.Proof.MlDsa.AArch64.Optimized.InverseTable

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTable
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

private theorem mapped_get {α β : Type} [Inhabited α] [Inhabited β]
    (xs : List α) (f : α → β) {i : Nat} (hi : i<xs.length) :
    (xs.map f)[i]! = f xs[i]! := by
  rw [getElem!_pos (xs.map f) i (by simpa only [List.length_map] using hi),
    List.getElem_map,getElem!_pos xs i hi]

theorem expanded_get {i : Nat} (hi : i<976) : expandedVals[i]! = value layout[i]! := by
  exact (congrArg (fun xs : List Nat => xs[i]!) expandedVals_layout).trans
    (mapped_get layout value (by rw [layout_length]; exact hi))

theorem value_false (k : Nat) : value (k,false) = z k := rfl

theorem value_true (k : Nat) : value (k,true) = bar (z k) := by
  simp only [value,ite_true]

theorem expanded_root {i k : Nat} (hi : i<976) (h : layout[i]! = (k,false)) :
    expandedVals[i]! = z k := by
  exact (expanded_get hi).trans ((congrArg value h).trans (value_false k))

theorem expanded_bar {i k : Nat} (hi : i<976) (h : layout[i]! = (k,true)) :
    expandedVals[i]! = bar (z k) := by
  exact (expanded_get hi).trans ((congrArg value h).trans (value_true k))

theorem layer1_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+8*g+e]! = z (255-16*u-4*g-e) ∧
    expandedVals[120*u+8*g+e+4]! = bar (z (255-16*u-4*g-e)) := by
  have h := layer1_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega_using [hu, hg, he]) h.1, expanded_bar (by omega_using [hu, hg, he]) h.2⟩

theorem layer2_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+32+8*g+e]! = z (127-8*u-2*g-e/2) ∧
    expandedVals[120*u+32+8*g+e+4]! = bar (z (127-8*u-2*g-e/2)) := by
  have h := layer2_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega_using [hu, hg, he]) h.1, expanded_bar (by omega_using [hu, hg, he]) h.2⟩

theorem layer4_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+64+8*g+e]! = z (63-4*u-g) ∧
    expandedVals[120*u+64+8*g+e+4]! = bar (z (63-4*u-g)) := by
  have h := layer4_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega_using [hu, hg, he]) h.1, expanded_bar (by omega_using [hu, hg, he]) h.2⟩

theorem layer8_values {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    expandedVals[120*u+96+8*g+e]! = z (31-2*u-g) ∧
    expandedVals[120*u+96+8*g+e+4]! = bar (z (31-2*u-g)) := by
  have h := layer8_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega_using [hu, hg, he]) h.1, expanded_bar (by omega_using [hu, hg, he]) h.2⟩

theorem layer16_values {u e : Nat} (hu : u<8) (he : e<4) :
    expandedVals[120*u+112+e]! = z (15-u) ∧
    expandedVals[120*u+112+e+4]! = bar (z (15-u)) := by
  have h := layer16_layout ⟨u,hu⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega_using [hu, he]) h.1, expanded_bar (by omega_using [hu, he]) h.2⟩

theorem tail_values {j : Nat} (hj : j<8) :
    expandedVals[960+j]! = z (7-j) ∧ expandedVals[968+j]! = bar (z (7-j)) := by
  have h := tail_layout ⟨j,hj⟩
  exact ⟨expanded_root (by omega_using [hj]) h.1, expanded_bar (by omega_using [hj]) h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.InverseTable

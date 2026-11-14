module

public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ntt
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.AArch64.Optimized.TableLayout`, which only this module used -/

section

@[expose] public section

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
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u e

theorem inner2_layout : ∀ u : Fin 8, ∀ g : Fin 2, ∀ e : Fin 4,
    layout[120*u.val+8+8*g.val+e.val]! = (16+2*u.val+g.val,false) ∧
    layout[120*u.val+8+8*g.val+e.val+4]! = (16+2*u.val+g.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 2, ∀ e : Fin 4,
      layoutAt (120*u.val+8+8*g.val+e.val) = (16+2*u.val+g.val,false) ∧
      layoutAt (120*u.val+8+8*g.val+e.val+4) = (16+2*u.val+g.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem inner1_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+24+8*g.val+e.val]! = (32+4*u.val+g.val,false) ∧
    layout[120*u.val+24+8*g.val+e.val+4]! = (32+4*u.val+g.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+24+8*g.val+e.val) = (32+4*u.val+g.val,false) ∧
      layoutAt (120*u.val+24+8*g.val+e.val+4) = (32+4*u.val+g.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem tail2_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+56+8*g.val+e.val]! = (64+8*u.val+2*g.val+e.val/2,false) ∧
    layout[120*u.val+56+8*g.val+e.val+4]! = (64+8*u.val+2*g.val+e.val/2,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+56+8*g.val+e.val) = (64+8*u.val+2*g.val+e.val/2,false) ∧
      layoutAt (120*u.val+56+8*g.val+e.val+4) = (64+8*u.val+2*g.val+e.val/2,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem tail1_layout : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
    layout[120*u.val+88+8*g.val+e.val]! = (128+16*u.val+4*g.val+e.val,false) ∧
    layout[120*u.val+88+8*g.val+e.val+4]! = (128+16*u.val+4*g.val+e.val,true) := by
  have h : ∀ u : Fin 8, ∀ g : Fin 4, ∀ e : Fin 4,
      layoutAt (120*u.val+88+8*g.val+e.val) = (128+16*u.val+4*g.val+e.val,false) ∧
      layoutAt (120*u.val+88+8*g.val+e.val+4) = (128+16*u.val+4*g.val+e.val,true) := by
    decide +kernel
  intro u g e
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h u g e

theorem hoisted_layout : ∀ i : Fin 8,
    layout[960+2*i.val]! = (i.val+1,false) ∧
    layout[960+2*i.val+1]! = (i.val+1,true) := by
  have h : ∀ i : Fin 8,
      layoutAt (960+2*i.val) = (i.val+1,false) ∧
      layoutAt (960+2*i.val+1) = (i.val+1,true) := by
    decide +kernel
  intro i
  rw [layout_get (by omega_using []), layout_get (by omega_using [])]
  exact h i

end VG.Proof.MlDsa.AArch64.Optimized.TableConstants

end

end


/-! ## From `TableConstants.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.TableConstants
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

private theorem mapped_get {α β : Type} [Inhabited α] [Inhabited β]
    (xs : List α) (f : α → β) {i : Nat} (hi : i<xs.length) :
    (xs.map f)[i]! = f xs[i]! := by
  rw [getElem!_pos (xs.map f) i (by simpa only [List.length_map] using hi),
    List.getElem_map,getElem!_pos xs i hi]

theorem expanded_get {i : Nat} (hi : i<976) : expandedVals[i]! = value layout[i]! := by
  exact (congrArg (fun xs : List Nat => xs[i]!) expandedVals_layout).trans
    (mapped_get layout value (by rw [layout_length]; exact hi))

theorem value_false (k : Nat) : value (k,false) = zetaTab k := rfl

theorem value_true (k : Nat) : value (k,true) = zetaTab k*2^31/8380417 := by
  simp only [value,ite_true]

theorem expanded_root {i k : Nat} (hi : i<976) (h : layout[i]! = (k,false)) :
    expandedVals[i]! = zetaTab k := by
  exact (expanded_get hi).trans ((congrArg value h).trans (value_false k))

theorem expanded_bar {i k : Nat} (hi : i<976) (h : layout[i]! = (k,true)) :
    expandedVals[i]! = zetaTab k*2^31/8380417 := by
  exact (expanded_get hi).trans ((congrArg value h).trans (value_true k))

theorem inner4_values {u e : Nat} (hu : u<8) (he : e<4) :
    expandedVals[120*u+e]! = zetaTab (8+u) ∧
    expandedVals[120*u+e+4]! = zetaTab (8+u)*2^31/8380417 := by
  have hi0 : 120*u+e < 976 := by omega_using [hu, he]
  have hi1 : 120*u+e+4 < 976 := by omega_using [hu, he]
  have h := inner4_layout ⟨u,hu⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+e) hi0 h.1,
    expanded_bar (i := 120*u+e+4) hi1 h.2⟩

theorem inner2_values {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    expandedVals[120*u+8+8*g+e]! = zetaTab (16+2*u+g) ∧
    expandedVals[120*u+8+8*g+e+4]! = zetaTab (16+2*u+g)*2^31/8380417 := by
  have hi0 : 120*u+8+8*g+e < 976 := by omega_using [hu, hg, he]
  have hi1 : 120*u+8+8*g+e+4 < 976 := by omega_using [hu, hg, he]
  have h := inner2_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+8+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+8+8*g+e+4) hi1 h.2⟩

theorem inner1_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+24+8*g+e]! = zetaTab (32+4*u+g) ∧
    expandedVals[120*u+24+8*g+e+4]! = zetaTab (32+4*u+g)*2^31/8380417 := by
  have hi0 : 120*u+24+8*g+e < 976 := by omega_using [hu, hg, he]
  have hi1 : 120*u+24+8*g+e+4 < 976 := by omega_using [hu, hg, he]
  have h := inner1_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+24+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+24+8*g+e+4) hi1 h.2⟩

theorem tail2_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+56+8*g+e]! = zetaTab (64+8*u+2*g+e/2) ∧
    expandedVals[120*u+56+8*g+e+4]! = zetaTab (64+8*u+2*g+e/2)*2^31/8380417 := by
  have hi0 : 120*u+56+8*g+e < 976 := by omega_using [hu, hg, he]
  have hi1 : 120*u+56+8*g+e+4 < 976 := by omega_using [hu, hg, he]
  have h := tail2_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+56+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+56+8*g+e+4) hi1 h.2⟩

theorem tail1_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+88+8*g+e]! = zetaTab (128+16*u+4*g+e) ∧
    expandedVals[120*u+88+8*g+e+4]! = zetaTab (128+16*u+4*g+e)*2^31/8380417 := by
  have hi0 : 120*u+88+8*g+e < 976 := by omega_using [hu, hg, he]
  have hi1 : 120*u+88+8*g+e+4 < 976 := by omega_using [hu, hg, he]
  have h := tail1_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+88+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+88+8*g+e+4) hi1 h.2⟩

theorem hoisted_values {i : Nat} (hi : i<8) :
    expandedVals[960+2*i]! = zetaTab (i+1) ∧
    expandedVals[960+2*i+1]! = zetaTab (i+1)*2^31/8380417 := by
  have hi0 : 960+2*i < 976 := by omega_using [hi]
  have hi1 : 960+2*i+1 < 976 := by omega_using [hi]
  have h := hoisted_layout ⟨i,hi⟩
  exact ⟨expanded_root (i := 960+2*i) hi0 h.1,
    expanded_bar (i := 960+2*i+1) hi1 h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.TableConstants

end

/-! ## From `TableWords.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.TableConstants
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem value_lt (p : Nat × Bool) : value p < 2^32 := by
  have hz : zetaTab p.1 < 8380417 := Nat.mod_lt _ (by decide)
  have hb : zetaTab p.1*2^31/8380417 < 2^31 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).2
    simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hz (show 0<2^31 by decide)
  cases h : p.2 <;> simp only [value,h,Bool.false_eq_true,ite_false,ite_true] <;> omega_using [hz]

theorem expandedVals_lt {i : Nat} (hi : i<976) : expandedVals[i]! < 2^32 := by
  rw [expanded_get hi]
  exact value_lt _

theorem pack_low (a b : Nat) (ha : a<2^32) (hb : b<2^32) :
    (BitVec.ofNat 64 (a+2^32*b)).extractLsb' 0 32 = BitVec.ofNat 32 a := by
  have hab : a+2^32*b < 2^64 := by omega_using [ha, hb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hab,
    Nat.shiftRight_zero,Nat.mod_eq_of_lt ha]
  omega_using [ha]

theorem pack_high (a b : Nat) (ha : a<2^32) (hb : b<2^32) :
    (BitVec.ofNat 64 (a+2^32*b)).extractLsb' 32 32 = BitVec.ofNat 32 b := by
  have hab : a+2^32*b < 2^64 := by omega_using [ha, hb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hab,
    Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt hb]
  omega_using [ha, hb]

theorem staticNttWords_length : staticNttWords.length = 488 := by
  simp only [staticNttWords,List.length_map,List.length_range,expandedVals_length]

private theorem range_map_get {α : Type} [Inhabited α] (f : Nat → α) {n i : Nat}
    (hi : i<n) : ((List.range n).map f)[i]! = f i := by
  rw [getElem!_pos ((List.range n).map f) i (by simpa only [List.length_map,List.length_range] using hi),
    List.getElem_map,List.getElem_range]

theorem staticNttWords_get {i : Nat} (hi : i<488) :
    staticNttWords[i]! = BitVec.ofNat 64 (expandedVals[2*i]!+2^32*expandedVals[2*i+1]!) := by
  exact range_map_get _ (by simpa only [expandedVals_length] using hi)

theorem staticNttWords_low {i : Nat} (hi : i<488) :
    (staticNttWords[i]!).extractLsb' 0 32 = BitVec.ofNat 32 expandedVals[2*i]! := by
  rw [staticNttWords_get hi]
  exact pack_low _ _ (expandedVals_lt (by omega_using [hi])) (expandedVals_lt (by omega_using [hi]))

theorem staticNttWords_high {i : Nat} (hi : i<488) :
    (staticNttWords[i]!).extractLsb' 32 32 = BitVec.ofNat 32 expandedVals[2*i+1]! := by
  rw [staticNttWords_get hi]
  exact pack_high _ _ (expandedVals_lt (by omega_using [hi])) (expandedVals_lt (by omega_using [hi]))

end VG.Proof.MlDsa.AArch64.Optimized.TableConstants

end

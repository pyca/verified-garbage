import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableLayout

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

private theorem mapped_prefix_get {α β : Type} [Inhabited α] [Inhabited β]
    (xs : List α) (f : α → β) (ys : List β) {n i : Nat} (hi : i<n) (hn : n≤xs.length) :
    ((xs.take n).map f ++ ys)[i]! = f xs[i]! := by
  have hlen : ((xs.take n).map f).length=n := by simp [Nat.min_eq_left hn]
  rw [getElem!_pos _ _ (by simp only [List.length_append,hlen]; omega),
    List.getElem_append_left (by rw [hlen]; exact hi),List.getElem_map,List.getElem_take,
    getElem!_pos xs i (by omega)]

private theorem mapped_suffix_get {α β : Type} [Inhabited α] [Inhabited β]
    (xs : List β) (ys : List α) (f : α → β) {i : Nat} (hi : i<ys.length) :
    (xs ++ ys.map f)[xs.length+i]! = f ys[i]! := by
  rw [getElem!_pos _ _ (by simp only [List.length_append,List.length_map]; omega),
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,List.getElem_map]
  rw [getElem!_pos ys i hi]

theorem expanded_first {i : Nat} (hi : i<960) :
    expandedVals[i]! = VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedVals[i]! := by
  rw [expandedVals_layout,mapped_prefix_get _ _ _ hi (by rw [InverseTable.layout_length]; decide),
    InverseTable.expanded_get (by omega)]

theorem expanded_tail {i : Nat} (hi : i<64) :
    expandedVals[960+i]! = tailValue tailLayout[i]! := by
  rw [expandedVals_layout]
  have hn : ((InverseTable.layout.take 960).map InverseTable.value).length=960 := by
    simp only [List.length_map,List.length_take,InverseTable.layout_length]; decide
  have h := mapped_suffix_get ((InverseTable.layout.take 960).map InverseTable.value)
    tailLayout tailValue (i := i) (by rw [tailLayout_length]; exact hi)
  simpa only [hn] using h

theorem tail_values {j e : Nat} (hj : j<8) (he : e<4) :
    expandedVals[960+8*j+e]! = tailRoot j ∧
    expandedVals[960+8*j+e+4]! = bar (tailRoot j) := by
  have hh := tail_layout ⟨j,hj⟩ ⟨e,he⟩
  have h0 := (expanded_tail (i := 8*j+e) (by omega)).trans (congrArg tailValue hh.1)
  have h1 := (expanded_tail (i := 8*j+e+4) (by omega)).trans (congrArg tailValue hh.2)
  constructor
  · simpa only [Nat.add_assoc,tailValue,Bool.false_eq_true,ite_false] using h0
  · simpa only [Nat.add_assoc,tailValue,ite_true] using h1


theorem layer1_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+8*g+e]! = z (255-16*u-4*g-e) ∧
    expandedVals[120*u+8*g+e+4]! = bar (z (255-16*u-4*g-e)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer1_values hu hg he

theorem layer2_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+32+8*g+e]! = z (127-8*u-2*g-e/2) ∧
    expandedVals[120*u+32+8*g+e+4]! = bar (z (127-8*u-2*g-e/2)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer2_values hu hg he

theorem layer4_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+64+8*g+e]! = z (63-4*u-g) ∧
    expandedVals[120*u+64+8*g+e+4]! = bar (z (63-4*u-g)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer4_values hu hg he

theorem layer8_values {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    expandedVals[120*u+96+8*g+e]! = z (31-2*u-g) ∧
    expandedVals[120*u+96+8*g+e+4]! = bar (z (31-2*u-g)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer8_values hu hg he

theorem layer16_values {u e : Nat} (hu : u<8) (he : e<4) :
    expandedVals[120*u+112+e]! = z (15-u) ∧
    expandedVals[120*u+112+e+4]! = bar (z (15-u)) := by
  rw [expanded_first (by omega),expanded_first (by omega)]
  exact InverseTable.layer16_values hu he

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable

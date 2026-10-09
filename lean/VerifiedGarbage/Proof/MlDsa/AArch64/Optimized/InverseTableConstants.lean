import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableLayout

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
  exact ⟨expanded_root (by omega) h.1, expanded_bar (by omega) h.2⟩

theorem layer2_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+32+8*g+e]! = z (127-8*u-2*g-e/2) ∧
    expandedVals[120*u+32+8*g+e+4]! = bar (z (127-8*u-2*g-e/2)) := by
  have h := layer2_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega) h.1, expanded_bar (by omega) h.2⟩

theorem layer4_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+64+8*g+e]! = z (63-4*u-g) ∧
    expandedVals[120*u+64+8*g+e+4]! = bar (z (63-4*u-g)) := by
  have h := layer4_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega) h.1, expanded_bar (by omega) h.2⟩

theorem layer8_values {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    expandedVals[120*u+96+8*g+e]! = z (31-2*u-g) ∧
    expandedVals[120*u+96+8*g+e+4]! = bar (z (31-2*u-g)) := by
  have h := layer8_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega) h.1, expanded_bar (by omega) h.2⟩

theorem layer16_values {u e : Nat} (hu : u<8) (he : e<4) :
    expandedVals[120*u+112+e]! = z (15-u) ∧
    expandedVals[120*u+112+e+4]! = bar (z (15-u)) := by
  have h := layer16_layout ⟨u,hu⟩ ⟨e,he⟩
  exact ⟨expanded_root (by omega) h.1, expanded_bar (by omega) h.2⟩

theorem tail_values {j : Nat} (hj : j<8) :
    expandedVals[960+j]! = z (7-j) ∧ expandedVals[968+j]! = bar (z (7-j)) := by
  have h := tail_layout ⟨j,hj⟩
  exact ⟨expanded_root (by omega) h.1, expanded_bar (by omega) h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.InverseTable

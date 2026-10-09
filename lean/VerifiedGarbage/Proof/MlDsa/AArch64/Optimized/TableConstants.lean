import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableLayout

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
  have hi0 : 120*u+e < 976 := by omega
  have hi1 : 120*u+e+4 < 976 := by omega
  have h := inner4_layout ⟨u,hu⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+e) hi0 h.1,
    expanded_bar (i := 120*u+e+4) hi1 h.2⟩

theorem inner2_values {u g e : Nat} (hu : u<8) (hg : g<2) (he : e<4) :
    expandedVals[120*u+8+8*g+e]! = zetaTab (16+2*u+g) ∧
    expandedVals[120*u+8+8*g+e+4]! = zetaTab (16+2*u+g)*2^31/8380417 := by
  have hi0 : 120*u+8+8*g+e < 976 := by omega
  have hi1 : 120*u+8+8*g+e+4 < 976 := by omega
  have h := inner2_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+8+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+8+8*g+e+4) hi1 h.2⟩

theorem inner1_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+24+8*g+e]! = zetaTab (32+4*u+g) ∧
    expandedVals[120*u+24+8*g+e+4]! = zetaTab (32+4*u+g)*2^31/8380417 := by
  have hi0 : 120*u+24+8*g+e < 976 := by omega
  have hi1 : 120*u+24+8*g+e+4 < 976 := by omega
  have h := inner1_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+24+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+24+8*g+e+4) hi1 h.2⟩

theorem tail2_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+56+8*g+e]! = zetaTab (64+8*u+2*g+e/2) ∧
    expandedVals[120*u+56+8*g+e+4]! = zetaTab (64+8*u+2*g+e/2)*2^31/8380417 := by
  have hi0 : 120*u+56+8*g+e < 976 := by omega
  have hi1 : 120*u+56+8*g+e+4 < 976 := by omega
  have h := tail2_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+56+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+56+8*g+e+4) hi1 h.2⟩

theorem tail1_values {u g e : Nat} (hu : u<8) (hg : g<4) (he : e<4) :
    expandedVals[120*u+88+8*g+e]! = zetaTab (128+16*u+4*g+e) ∧
    expandedVals[120*u+88+8*g+e+4]! = zetaTab (128+16*u+4*g+e)*2^31/8380417 := by
  have hi0 : 120*u+88+8*g+e < 976 := by omega
  have hi1 : 120*u+88+8*g+e+4 < 976 := by omega
  have h := tail1_layout ⟨u,hu⟩ ⟨g,hg⟩ ⟨e,he⟩
  exact ⟨expanded_root (i := 120*u+88+8*g+e) hi0 h.1,
    expanded_bar (i := 120*u+88+8*g+e+4) hi1 h.2⟩

theorem hoisted_values {i : Nat} (hi : i<8) :
    expandedVals[960+2*i]! = zetaTab (i+1) ∧
    expandedVals[960+2*i+1]! = zetaTab (i+1)*2^31/8380417 := by
  have hi0 : 960+2*i < 976 := by omega
  have hi1 : 960+2*i+1 < 976 := by omega
  have h := hoisted_layout ⟨i,hi⟩
  exact ⟨expanded_root (i := 960+2*i) hi0 h.1,
    expanded_bar (i := 960+2*i+1) hi1 h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.TableConstants

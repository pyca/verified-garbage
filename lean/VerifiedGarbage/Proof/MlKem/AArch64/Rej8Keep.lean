module
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec


/-! # Preserve parser constants through scalar wrappers and rejection loops -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

def keepsConstants (i : Instr) : Bool := decide
  (vdstOf i≠some .v16 ∧ vdstOf i≠some .v17 ∧ vdstOf i≠some .v19 ∧
   vdstOf i≠some .v20 ∧ vdstOf i≠some .v21)

theorem Constants.exec {c : Prog isa} {s u : State} {tr : List Leak}
    (h : Constants s) (he : Exec isa c s tr u)
    (hk : (instrs c).all keepsConstants=true) : Constants u := by
  have hv : ∀r∈[VReg.v16,.v17,.v19,.v20,.v21],u.v r=s.v r := by
    intro r hr
    apply Exec.vec (c := c) ?_ he
    intro i hi
    have hh := of_decide_eq_true (List.all_eq_true.mp hk i hi)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2.1
    · exact hh.2.2.2.1
    · exact hh.2.2.2.2
  exact ⟨by rw [hv .v16 (by simp)]; exact h.index,
    by rw [hv .v17 (by simp)]; exact h.mask,
    by rw [hv .v19 (by simp)]; exact h.q,
    by rw [hv .v20 (by simp)]; exact h.weights,
    by rw [hv .v21 (by simp)]; exact h.zero⟩

theorem WP.constants {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s Q) (hc : Constants s) (hk : (instrs c).all keepsConstants=true) :
    WP isa c s fun u => Q u ∧ Constants u := by
  obtain ⟨tr,u,he,hq⟩ := h
  exact ⟨tr,u,he,hq,hc.exec he hk⟩

end VG.Proof.MlKem.AArch64.Rej8

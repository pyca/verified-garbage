module

public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Scalar
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

/-! ### `MlKem.AArch64.Paired.Store`, which the modules that import this one used -/

section

/-! # Save a resumed sampler's output cursor and success flag -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG.Impl.MlKem.AArch64
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure SavedPostW (w16 : Bool) (L : List Zq) (aP p : Addr) (s u : State) : Prop where
  keep : Keep [] s u
  frame : Frame [⟨p,16⟩] s.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem aP L
  checkpoint : checkpointW w16 p aP L u.mem
  x3 : u.gpr .x3=cAddr w16 aP L.length
  x4 : (u.gpr .x4).toNat=256-L.length

theorem store_ok {w16 : Bool} (s : State) {r : Reg} {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    {L : List Zq} {aP : Addr} (hl : L.length≤256)
    (hc : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (h0 : InRegions s.wr (s.gpr r+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions s.wr (s.gpr r+BitVec.ofNat 64 (slot+8)) 8)
    (hd : (polyRegion aP).Disjoint ⟨s.gpr r+BitVec.ofNat 64 slot,16⟩) :
    WP isa (.block [.str .x .x3 r slot,.str .x .x4 r (slot+8)]) s
      (SavedPostW w16 L aP (s.gpr r+BitVec.ofNat 64 slot) s) := by
  refine WP.mono (store_checkpoint s ho ha h0 h1) fun u ⟨hu,_,fr,p3,p4⟩ => ?_
  refine ⟨hu,fr,?_,?_,by rw [hu.get .x3,h3],by rw [hu.get .x4,h4]⟩
  · intro i hi
    rw [coeffAtW_frame fr (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by omega_using [hl, hi])]
    exact hc i hi
  · refine ⟨by rw [p3,h3],?_⟩
    have haddr : s.gpr r+BitVec.ofNat 64 slot+8=s.gpr r+BitVec.ofNat 64 (slot+8) := by
      rw [BitVec.ofNat_add,BitVec.add_assoc]
      rfl
    rw [haddr,p4,h4]

end VG.Proof.MlKem.AArch64.Paired

end

end

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

module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue

/-! # Save a resumed sampler's output cursor and success flag -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG.Impl.MlKem.AArch64
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure SavedPostW (w16 : Bool) (L : List Zq) (aP p : Addr) (flag : Reg) (s u : State) : Prop where
  keep : Keep [flag] s u
  frame : Frame [⟨p,16⟩] s.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem aP L
  checkpoint : checkpointW w16 p aP L u.mem
  flagValue : u.gpr flag=s.gpr .x0
  x3 : u.gpr .x3=cAddr w16 aP L.length
  x4 : (u.gpr .x4).toNat=256-L.length

theorem store_ok {w16 : Bool} (s : State) {slot : Nat} (ho : slot+8<32768) (ha : slot%8=0)
    {flag : Reg} (hf : flag≠.x3 ∧ flag≠.x4 ∧ flag≠.x19)
    {L : List Zq} {aP : Addr} (hl : L.length≤256)
    (hc : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (h3 : s.gpr .x3=cAddr w16 aP L.length) (h4 : (s.gpr .x4).toNat=256-L.length)
    (h0 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8)
    (hd : (polyRegion aP).Disjoint ⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩) :
    WP isa (.block [mov flag .x0,.str .x .x3 .x19 slot,.str .x .x4 .x19 (slot+8)]) s
      (SavedPostW w16 L aP (s.gpr .x19+BitVec.ofNat 64 slot) flag s) := by
  refine wp_mov fun a ha ea => ?_
  refine WP.mono (store_checkpoint a ho ‹slot%8=0›
    (by rw [ha.wr,ha.get .x19 (by simpa using hf.2.2.symm)]; exact h0)
    (by rw [ha.wr,ha.get .x19 (by simpa using hf.2.2.symm)]; exact h1)) fun u ⟨hu,_,fr,p3,p4⟩ => ?_
  have he : a.gpr .x19=s.gpr .x19 := ha.get .x19 (by simpa using hf.2.2.symm)
  have hu3 : u.gpr .x3=cAddr w16 aP L.length := by
    rw [hu.get .x3,ha.get .x3 (by simpa using hf.1.symm),h3]
  have hu4 : (u.gpr .x4).toNat=256-L.length := by
    rw [hu.get .x4,ha.get .x4 (by simpa using hf.2.1.symm),h4]
  have fr' : Frame [⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩] s.mem u.mem := by
    simpa only [he,ha.mem] using fr
  refine ⟨(ha.keep.trans hu).mono (by simp),fr',?_,?_,by rw [hu.get flag (by simp),ea],hu3,hu4⟩
  · intro i hi
    rw [coeffAtW_frame fr' (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by omega)]
    exact hc i hi
  · refine ⟨?_,?_⟩
    · rw [he,ha.get .x3 (by simpa using hf.1.symm),h3] at p3
      exact p3
    · have haddr : s.gpr .x19+BitVec.ofNat 64 slot+8=s.gpr .x19+BitVec.ofNat 64 (slot+8) := by
        rw [BitVec.ofNat_add,BitVec.add_assoc]
        rfl
      rw [he,ha.get .x4 (by simpa using hf.2.1.symm)] at p4
      rw [haddr,p4,h4]

end VG.Proof.MlKem.AArch64.Paired

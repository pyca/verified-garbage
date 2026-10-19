module
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector

import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # One continued rejection stream and its checkpoint -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

structure ExtraPostW (w16 : Bool) (L : List Zq) (B : Nat → Byte) (aP p : Addr) (flag : Reg) (s u : State) : Prop where
  keep : Keep (flag::[.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]) s u
  frame : Frame [polyRegion aP,⟨p,16⟩] s.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem aP (sampleAfter L B 56)
  checkpoint : checkpointW w16 p aP (sampleAfter L B 56) u.mem
  x3 : u.gpr .x3=cAddr w16 aP (sampleAfter L B 56).length
  x4 : (u.gpr .x4).toNat=256-(sampleAfter L B 56).length
  flagValue : (u.gpr flag).toNat=if (sampleAfter L B 56).length=256 then 1 else 0

theorem extra_ok {w16 : Bool} (s : State) {buf slot : Nat} (hb : buf<4096)
    (ho : slot+8<32768) (halign : slot%8=0)
    {flag : Reg} (hf : flag≠.x3 ∧ flag≠.x4 ∧ flag≠.x19)
    {B : Nat → Byte} {L : List Zq} {aP : Addr}
    (hp : Rej8.EnvW w16 56 B (s.gpr .x19+BitVec.ofNat 64 buf) aP s) (hc : Rej8.Constants s)
    (hl : L.length≤256) (hcoeff : Rej8.Scalar.CoeffsW w16 s.mem aP L)
    (hcp : checkpointW w16 (s.gpr .x19+BitVec.ofNat 64 slot) aP L s.mem)
    (h0 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8)
    (hd : (polyRegion aP).Disjoint ⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩) :
    WP isa (Impl.MlKem.AArch64.Paired.extraReject buf slot flag w16) s
      (ExtraPostW w16 L B aP (s.gpr .x19+BitVec.ofNat 64 slot) flag s) := by
  refine WP.seq (WP.mono (load_checkpoint s ho halign (in_rd_wr h0) (in_rd_wr h1)) fun a ⟨ha,hv,h3,h4⟩ => ?_)
  have a3 : a.gpr .x3=cAddr w16 aP L.length := h3.trans hcp.1
  have a4 : (a.gpr .x4).toNat=256-L.length := by
    rw [h4,show s.gpr .x19+BitVec.ofNat 64 (slot+8)=s.gpr .x19+BitVec.ofNat 64 slot+8 by
      rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl]
    exact hcp.2
  have ac : Rej8.Constants a := ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
    by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,by simpa only [hv] using hc.zero⟩
  have ap : Rej8.EnvW w16 56 B (a.gpr .x19+BitVec.ofNat 64 buf) aP a := by
    rw [ha.get .x19]
    exact hp.transfer ha.mem ha.rd ha.wr (ha.get .x16)
  refine WP.ite (a.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun _ => ?_)
  · rw [eq_zero_iff,decide_eq_true_eq,a4] at hz
    have full : L.length=256 := by omega
    have eqL : sampleAfter L B 56=L := sampleAfter_full (t := 0) full 56 (by omega)
    refine wp_movz fun u hu eu => wp_nil ?_
    refine ⟨(ha.keep.trans hu.keep).mono (by simp),?_,?_,?_,?_,?_,?_⟩
    · rw [hu.mem,ha.mem]; exact Frame.refl _ _
    · rw [eqL,hu.mem,ha.mem]; exact hcoeff
    · rw [eqL,hu.mem,ha.mem]; exact hcp
    · rw [eqL,hu.get .x3 (by simpa using hf.1.symm),a3]
    · rw [eqL,hu.get .x4 (by simpa using hf.2.1.symm),a4]
    · rw [eqL,eu,ite_eq_left full]; rfl
  · have hrun := continue_ok a hb ap ac hl (by rw [ha.mem]; exact hcoeff) a3 a4
    change WP isa (.seq (.block (continueEntry buf))
      (.seq (Impl.MlKem.AArch64.Rej8.rejLoop w16) (.block _))) a _
    apply WP.assoc
    refine WP.seq (WP.mono hrun fun b ⟨kb,fb,cb,b3,b4,b0⟩ => ?_)
    have b19 : b.gpr .x19=s.gpr .x19 := (kb.get .x19).trans (ha.get .x19)
    refine WP.mono (store_ok b ho halign hf
      (sampleAfter_length_le hl B 56) cb b3 b4
      (by rw [kb.wr,ha.wr,b19]; exact h0)
      (by rw [kb.wr,ha.wr,b19]; exact h1)
      (by rw [b19]; exact hd)) fun u hu => ?_
    refine ⟨((ha.keep.trans kb).trans hu.keep).mono (by simp),?_,hu.coeffs,?_,hu.x3,hu.x4,?_⟩
    · have fb' : Frame [polyRegion aP,⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩] s.mem b.mem := by
        rw [←ha.mem]
        exact fb.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
      apply fb'.trans
      rw [b19] at hu
      exact hu.frame.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    · simpa only [b19] using hu.checkpoint
    · rw [hu.flagValue,b0]

end VG.Proof.MlKem.AArch64.Paired

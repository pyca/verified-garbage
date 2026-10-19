module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Vector
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

def initialOne (buf out slot : Nat) (flag : Reg) (w16 : Bool := false) : Prog isa :=
  .seq (Impl.MlKem.AArch64.Paired.reject buf out flag w16)
    (.block [.str .x .x3 .x19 slot,.str .x .x4 .x19 (slot+8)])

def initialWrites (p aP : Addr) : List Region := [polyRegion aP,⟨p,16⟩]

structure InitialOnePostW (w16 : Bool) (B : Nat→Byte) (aP p : Addr) (flag : Reg) (s t : State) : Prop where
  keep : Keep (flag::[.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]) s t
  frame : Frame (initialWrites p aP) s.mem t.mem
  coeffs : Rej8.Scalar.CoeffsW w16 t.mem aP (sampleAfter [] B 168)
  saved : checkpointW w16 p aP (sampleAfter [] B 168) t.mem
  flagValue : (t.gpr flag).toNat=if (sampleAfter [] B 168).length=256 then 1 else 0
  constants : Rej8.Constants t

theorem initialOne_ok {w16 : Bool} (s : State) {buf out slot : Nat} (hb : buf<4096) (ho : out<65536)
    (hslot : slot+8<32768) (halign : slot%8=0)
    {flag : Reg} (hf : flag≠.x3 ∧ flag≠.x4 ∧ flag≠.x19)
    {B : Nat→Byte}
    (hp : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 buf) (s.gpr .x28+BitVec.ofNat 64 out) s)
    (hc : Rej8.Constants s)
    (h0 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 slot) 8)
    (h1 : InRegions s.wr (s.gpr .x19+BitVec.ofNat 64 (slot+8)) 8)
    (hd : (polyRegion (s.gpr .x28+BitVec.ofNat 64 out)).Disjoint ⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩) :
    WP isa (initialOne buf out slot flag w16) s
      (InitialOnePostW w16 B (s.gpr .x28+BitVec.ofNat 64 out) (s.gpr .x19+BitVec.ofNat 64 slot) flag s) := by
  have hkeep : (instrs (Impl.MlKem.AArch64.Paired.reject buf out flag w16)).all Rej8.keepsConstants=true := by
    unfold Impl.MlKem.AArch64.Paired.reject Impl.MlKem.AArch64.ptrTo
    split <;> cases flag <;> cases w16 <;> rfl
  refine WP.seq (WP.mono (Rej8.WP.constants (reject_ok s hb ho ⟨hf.1,hf.2.1⟩ hp hc) hc hkeep) fun a ⟨ha,ca⟩ => ?_)
  have a19 : a.gpr .x19=s.gpr .x19 := ha.keep.get .x19 (by simp [hf.2.2.symm])
  refine WP.mono (store_checkpoint a hslot halign (by rw [ha.keep.wr,a19]; exact h0)
    (by rw [ha.keep.wr,a19]; exact h1)) fun t ⟨kt,vt,ft,t0,t1⟩ => ?_
  have ft' : Frame [⟨s.gpr .x19+BitVec.ofNat 64 slot,16⟩] a.mem t.mem := by simpa only [a19] using ft
  refine ⟨(ha.keep.trans kt).mono (by simp),?_,?_,?_,?_,?_⟩
  · exact (ha.frame.mono (by simp [initialWrites])).trans (ft'.mono (by simp [initialWrites]))
  · intro i hi
    have hl : (sampleAfter [] B 168).length≤256 := sampleAfter_length_le (by decide) B 168
    rw [coeffAtW_frame ft' (by intro r hr; rw [List.mem_singleton.mp hr]; exact hd) (by omega)]
    exact ha.coeffs i hi
  · refine ⟨?_,?_⟩
    · rw [a19,ha.x3] at t0
      exact t0
    · rw [a19] at t1
      rw [show s.gpr .x19+BitVec.ofNat 64 slot+8=s.gpr .x19+BitVec.ofNat 64 (slot+8) by
        rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl,t1,ha.x4]
  · rw [kt.get flag (by simp),ha.flagValue]
  · exact ⟨by rw [vt]; exact ca.index,by rw [vt]; exact ca.mask,
      by simpa only [vt] using ca.q,by simpa only [vt] using ca.weights,
      by simpa only [vt] using ca.zero⟩

end VG.Proof.MlKem.AArch64.Paired

module

public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Segment
public import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

/-! # Reject the first three paired SHAKE128 blocks -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def rejectEntry (buf out : Nat) : List Instr := ptrTo .x3 .x28 out ++
  [.addImm .x .x2 .x19 buf,.movz .x .x4 256 0,.movz .x .x5 168 0,
   .movz .x .x9 3329 0,.movz .x .x10 15 0]

theorem rejectEntry_ok {w16 : Bool} (s : State) {buf out : Nat} (hb : buf<4096) (ho : out<65536)
    {B : Nat → Byte} (hp : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 buf)
      (s.gpr .x28+BitVec.ofNat 64 out) s) (hc : Rej8.Constants s) :
    WP isa (.block (rejectEntry buf out)) s fun u =>
      Only [.x2,.x3,.x4,.x5,.x9,.x10] s u ∧
      Rej8.EntryW w16 [] 168 B (s.gpr .x19+BitVec.ofNat 64 buf) (s.gpr .x28+BitVec.ofNat 64 out) u := by
  have hw : WP isa (.block (rejectEntry buf out)) s fun u =>
      Only [.x2,.x3,.x4,.x5,.x9,.x10] s u ∧
      u.gpr .x2=s.gpr .x19+BitVec.ofNat 64 buf ∧
      u.gpr .x3=s.gpr .x28+BitVec.ofNat 64 out ∧
      (u.gpr .x4).toNat=256 ∧ (u.gpr .x5).toNat=168 ∧
      (u.gpr .x9).toNat=q ∧ (u.gpr .x10).toNat=15 := by
    refine wp_ptrTo (by decide) ho fun a ha ea => wp_addImm hb fun b hb eb =>
      wp_movz fun c hc ec => wp_movz fun d hd ed => wp_movz fun e he ee =>
      wp_movz fun u hu eu => wp_nil ?_
    refine ⟨(((((ha.trans hb).trans hc).trans hd).trans he).trans hu).mono (by decide),?_,?_,?_,?_,?_,?_⟩
    · rw [hu.get .x2,he.get .x2,hd.get .x2,hc.get .x2,eb,ha.get .x19]
    · rw [hu.get .x3,he.get .x3,hd.get .x3,hc.get .x3,hb.get .x3,ea]
    · rw [hu.get .x4,he.get .x4,hd.get .x4,ec]; rfl
    · rw [hu.get .x5,he.get .x5,ed]; rfl
    · rw [hu.get .x9,ee]; rfl
    · rw [eu]; rfl
  have hnov : (rejectEntry buf out).all (fun i => !writesV i)=true := by
    unfold rejectEntry ptrTo
    split <;> rfl
  refine WP.mono (WP.keepV hnov hw) fun u ⟨⟨hk,x2,x3,x4,x5,x9,x10⟩,hv⟩ => ⟨hk,?_⟩
  refine ⟨hp.transfer hk.mem hk.rd hk.wr (hk.get .x16),?_,by simp,
    fun _ h => False.elim (Nat.not_lt_zero _ h),x2,?_,x4,x5,x9,x10⟩
  · exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
      by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
      by simpa only [hv] using hc.zero⟩
  · simpa only [List.length_nil,cAddr,Nat.mul_zero,ptr_zero] using x3

structure RejectPostW (w16 : Bool) (B : Nat → Byte) (aP : Addr) (flag : Reg) (s u : State) : Prop where
  keep : Keep (flag::[.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15]) s u
  frame : Frame [polyRegion aP] s.mem u.mem
  coeffs : Rej8.Scalar.CoeffsW w16 u.mem aP (sampleAfter [] B 168)
  x3 : u.gpr .x3=cAddr w16 aP (sampleAfter [] B 168).length
  x4 : (u.gpr .x4).toNat=256-(sampleAfter [] B 168).length
  flagValue : (u.gpr flag).toNat=if (sampleAfter [] B 168).length=256 then 1 else 0

abbrev RejectPost := RejectPostW false

theorem reject_ok {w16 : Bool} (s : State) {buf out : Nat} (hb : buf<4096) (ho : out<65536)
    {flag : Reg} (hf : flag≠.x3 ∧ flag≠.x4)
    {B : Nat → Byte} (hp : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 buf)
      (s.gpr .x28+BitVec.ofNat 64 out) s) (hc : Rej8.Constants s) :
    WP isa (Impl.MlKem.AArch64.Paired.reject buf out flag w16) s
      (RejectPostW w16 B (s.gpr .x28+BitVec.ofNat 64 out) flag s) := by
  refine WP.seq (WP.mono (rejectEntry_ok s hb ho hp hc) fun a ⟨ha,he⟩ => ?_)
  refine WP.seq (WP.mono (Rej8.segment_ok he (by decide) (by decide)) fun b hb => ?_)
  refine wp_mov fun u hu eu => wp_nil ?_
  refine ⟨((ha.keep.trans hb.keep).trans hu.keep).mono (by simp),?_,?_,?_,?_,?_⟩
  · rw [hu.mem,←ha.mem]; exact hb.acc.frame
  · rw [hu.mem]; exact hb.acc.coeffs
  · rw [hu.get .x3 (by simpa using hf.1.symm),hb.acc.x3]
  · rw [hu.get .x4 (by simpa using hf.2.symm),hb.acc.x4]
  · rw [eu,hb.status]

end VG.Proof.MlKem.AArch64.Paired

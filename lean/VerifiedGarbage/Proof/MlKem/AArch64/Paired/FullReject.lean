module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Segment
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit

/-! # Reject the first three paired SHAKE128 blocks -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def fullEntry (buf out : Nat) : List Instr := ptrTo .x3 .x28 out ++
  [.addImm .x .x2 .x19 buf,.movz .x .x4 256 0,.movz .x .x5 280 0,
   .movz .x .x9 3329 0,.movz .x .x10 15 0]

theorem fullEntry_ok {w16 : Bool} (s : State) {buf out : Nat} (hb : buf<4096) (ho : out<65536)
    {B : Nat → Byte} (hp : Rej8.EnvW w16 280 B (s.gpr .x19+BitVec.ofNat 64 buf)
      (s.gpr .x28+BitVec.ofNat 64 out) s) (hc : Rej8.Constants s) :
    WP isa (.block (fullEntry buf out)) s fun u =>
      Only [.x2,.x3,.x4,.x5,.x9,.x10] s u ∧
      Rej8.EntryW w16 [] 280 B (s.gpr .x19+BitVec.ofNat 64 buf) (s.gpr .x28+BitVec.ofNat 64 out) u := by
  have hw : WP isa (.block (fullEntry buf out)) s fun u =>
      Only [.x2,.x3,.x4,.x5,.x9,.x10] s u ∧
      u.gpr .x2=s.gpr .x19+BitVec.ofNat 64 buf ∧
      u.gpr .x3=s.gpr .x28+BitVec.ofNat 64 out ∧
      (u.gpr .x4).toNat=256 ∧ (u.gpr .x5).toNat=280 ∧
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
  have hnov : (fullEntry buf out).all (fun i => !writesV i)=true := by
    unfold fullEntry ptrTo
    split <;> rfl
  refine WP.mono (WP.keepV hnov hw) fun u ⟨⟨hk,x2,x3,x4,x5,x9,x10⟩,hv⟩ => ⟨hk,?_⟩
  refine ⟨hp.transfer hk.mem hk.rd hk.wr (hk.get .x16),?_,by simp,
    fun _ h => False.elim (Nat.not_lt_zero _ h),x2,?_,x4,x5,x9,x10⟩
  · exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
      by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
      by simpa only [hv] using hc.zero⟩
  · simpa only [List.length_nil,cAddr,Nat.mul_zero,ptr_zero] using x3

def fullFinish (w16 : Bool := false) : Prog isa := seqs [Impl.MlKem.AArch64.Rej8.rejLoop w16,
  .block [.logic .and .x .x24 .x24 .x0],Rej8.zeroSuffix w16,
  .block [.ldr .x .x22 .x19 1848,.ldr .x .x23 .x19 1856]]

def fullFinishRegs : List Reg := [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x22,.x23,.x24]

structure FullFinishPostW (w16 : Bool) (B : Nat → Byte) (out : Addr) (flags s u : State) : Prop where
  keep : Keep fullFinishRegs s u
  frame : Frame [polyRegion out] s.mem u.mem
  coeffs : CoeffsUpToW w16 u.mem out (sampleAfter [] B 280).length (Sample.cvW w16 (sampleAfter [] B 280))
    (fun _ => 0)
  reduced : ReducedW (cw w16) u.mem out
  status : u.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] B 280).length=256 then 1 else 0)
  flag22 : u.gpr .x22=flags.gpr .x22
  flag23 : u.gpr .x23=flags.gpr .x23

theorem fullFinish_ok {w16 : Bool} {s flags : State} {p out : Addr} {B : Nat → Byte}
    (he : Rej8.EntryW w16 [] 280 B (p+400) out s)
    (hp : s.gpr .x19=p) (hf : Flags p flags s.mem)
    (hd : (flagR p).Disjoint (polyRegion out))
    (hr0 : InRegions (s.rd++s.wr) (p+1848) 8)
    (hr1 : InRegions (s.rd++s.wr) (p+1856) 8) :
    WP isa (fullFinish w16) s (FullFinishPostW w16 B out flags s) := by
  refine WP.seq (WP.mono (Rej8.segment_ok he (by decide) (by decide)) fun a ha => ?_)
  refine WP.seq (wp_and fun b hb eb => wp_nil ?_)
  refine WP.seq (WP.mono (Rej8.zeroSuffix_prefix (aP := out) (L := sampleAfter [] B 280)
    (by intro i hi; rw [hb.wr,ha.keep.wr]; exact he.env.ina i hi)
    ha.acc.len (by rw [hb.mem]; exact ha.acc.coeffs)
    (by rw [hb.get .x3]; exact ha.acc.x3)
    (by rw [hb.get .x4]; exact ha.acc.x4)) fun c ⟨kc,fc,cc⟩ => ?_)
  have frame : Frame [polyRegion out] s.mem c.mem := by
    exact ha.acc.frame.trans (by rw [←hb.mem]; exact fc)
  have flagsC := hf.frame frame (by simpa using hd)
  have h19 : c.gpr .x19=p := by rw [kc.get .x19,hb.get .x19,ha.keep.get .x19,hp]
  refine wp_ldrx (by decide) (by rw [h19])
    (by rw [kc.rd,kc.wr,hb.rd,hb.wr,ha.keep.rd,ha.keep.wr]; exact hr0) fun d kd ed =>
    wp_ldrx (by decide) (by rw [kd.get .x19,h19])
    (by rw [kd.rd,kd.wr,kc.rd,kc.wr,hb.rd,hb.wr,ha.keep.rd,ha.keep.wr]; exact hr1) fun u ku eu => wp_nil ?_
  refine ⟨((((ha.keep.trans hb.keep).trans kc).trans kd.keep).trans ku.keep).mono (by decide),
    ?_,?_,?_,?_,?_,?_⟩
  · rw [ku.mem,kd.mem]; exact frame
  · rw [ku.mem,kd.mem]; exact cc
  · rw [ku.mem,kd.mem]; exact Sample.reduced_of_coeffs cc
  · rw [ku.get .x24,kd.get .x24,kc.get .x24,eb,ha.keep.get .x24]
    apply congrArg (fun w : BitVec 64 => s.gpr .x24 &&& w)
    apply BitVec.eq_of_toNat_eq
    rw [ha.status]
    split <;> rfl
  · rw [ku.get .x22,ed]; exact flagsC.1
  · rw [eu,kd.mem]; exact flagsC.2

end VG.Proof.MlKem.AArch64.Paired

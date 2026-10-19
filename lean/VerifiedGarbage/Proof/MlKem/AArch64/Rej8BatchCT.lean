module
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Advance
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Store
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Probe
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Store
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Advance
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Impl.MlKem.AArch64.Encode
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Impl.MlKem.AArch64.Encode
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
meta import VerifiedGarbage.Proof.MlKem.Mem16Bytes

/-! # Vector rejection leaks only its public matrix candidates and cursors -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Proof.MlKem.AArch64

theorem probe_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x2])) (.block probeCode) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x2])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem storeAdvance_ct (w16 : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x7])) (.block (storeCode w16++advanceCode w16)) := by
  cases w16 <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x7])
    (fun _ _ _ _ h => h) (by taint_decide)

structure BatchPublic (s t : State) : Prop where
  cs : Constants s
  ct : Constants t
  candidates : candidatesAt s=candidatesAt t
  rs : InRegions (s.rd++s.wr) (s.gpr .x2) 16
  rt : InRegions (t.rd++t.wr) (t.gpr .x2) 16
  sp : s.sp=t.sp
  x2 : s.gpr .x2=t.gpr .x2
  x3 : s.gpr .x3=t.gpr .x3
  table : s.gpr .x16=t.gpr .x16

theorem batch_relCT (w16 : Bool) : RelCT isa BatchPublic (.block (Impl.MlKem.AArch64.Rej8.rejEight w16))
    (fun _ _ => True) := by
  have he : (.block (Impl.MlKem.AArch64.Rej8.rejEight w16) : Prog isa)=
      .block (probeCode++(storeCode w16++advanceCode w16)) := by
    cases w16 <;> rfl
  rw [he]
  apply RelCT.block_append
  intro s t tr ur s' t' hp es et
  cases es with
  | @seq _ _ _ a _ tr₁ tr₂ ep er =>
    cases et with
    | @seq _ _ _ b _ ur₁ ur₂ fp fr =>
      have htr := probe_ct s t tr₁ ur₁ a b trivial trivial
        ⟨hp.sp,fun r hr => by
          have hr' : r=.x2 := by simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_singleton] using hr
          subst r; exact hp.x2⟩ ep fp
      obtain ⟨_,a',epa,ha⟩ := probe_ok s hp.cs hp.rs
      obtain ⟨_,b',fpb,hb⟩ := probe_ok t hp.ct hp.rt
      obtain ⟨_,rfl⟩ := Exec.det ep epa
      obtain ⟨_,rfl⟩ := Exec.det fp fpb
      have hm : maskAt s=maskAt t := congrArg acceptanceMask hp.candidates
      have hrest := storeAdvance_ct w16 a b tr₂ ur₂ s' t' trivial trivial
        ⟨ha.keep.sp.trans (hp.sp.trans hb.keep.sp.symm),fun r hr => by
          have hr' : r=.x3 ∨ r=.x7 := by
            simpa only [Taint.ofRegs,RegSet.mem_ofList,List.mem_cons,List.not_mem_nil,or_false] using hr
          rcases hr' with rfl|rfl
          · rw [ha.keep.get .x3,hb.keep.get .x3,hp.x3]
          · rw [ha.index,hb.index,hp.table,hm]⟩ er fr
      exact ⟨by rw [htr,hrest],trivial⟩

end VG.Proof.MlKem.AArch64.Rej8

module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Phases
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GatherTiming
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Scalar digit extraction permits independent secret byte strings in the two runs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure DigitPublic where
 p : Parameters
 i : Nat
 size : p.k<2^31
 width : p.N≤8*p.k
 positions : i+5*Spec.Rsa.FixedBaseComb.rows p.N<2^63

def DigitReady (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (q.i+1) s

structure DigitGather (q : DigitPublic) (s : State) : Prop where
 base : s.gpr .x0=q.p.B
 regs : GatherReady ⟨q.p.src,BitVec.ofNat 64 q.p.k,BitVec.ofNat 64 q.i,
  BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N),BitVec.ofNat 64 q.p.N⟩ s
 bytes : ∃ bs, Source q.p.src bs s ∧ bs.length=q.p.k ∧ s.gpr .x16=0#64

theorem digit_ct : RelCT isa (Two DigitReady) Comb.digit (fun _ _ => True) := by
 unfold Comb.digit
 refine RelCT.seq (two_piece (Ψ:=DigitGather) [.x0] ?_ (by taint_decide) ?_) ?_
 · rintro q s t ⟨bs,E,hs⟩ ⟨bt,F,ht⟩ r hr
   have : r= .x0 := by simpa using hr
   subst r
   exact hs.power.good.x0.trans ht.power.good.x0.symm
 · rintro q s ⟨bs,E,h⟩
   refine WP.mono (digitArgs_ok h.power.good q.p.room h.controls h.counter (by have := q.positions;omega)) ?_
   rintro t ⟨⟨ptr,len,row,spacing,width,zero,mem⟩,rest⟩
   refine ⟨(rest.gpr .x0 (by decide)).trans h.power.good.x0,?_,bs,h.reads.source.of_mem mem rest,h.reads.length,zero⟩
   exact ⟨ptr,h.reads.length ▸ len,row,spacing,width⟩
 · refine RelCT.seq (two_post (Ψ:=fun q s => s.gpr .x0=q.p.B) (two_map (fun q : DigitPublic =>
    (⟨q.p.src,BitVec.ofNat 64 q.p.k,BitVec.ofNat 64 q.i,
     BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N),BitVec.ofNat 64 q.p.N⟩ : GatherPublic))
    (fun _ _ h => h.regs) gather_ct) ?_) ?_
   · intro q s h
     obtain ⟨bs,source,length,zero⟩ := h.bytes
     refine WP.mono (gather_ok s source (length ▸ q.size) (length ▸ q.width) q.positions
      h.regs.1 (length ▸ h.regs.2.1) h.regs.2.2.1 h.regs.2.2.2.2 h.regs.2.2.2.1 zero) ?_
     rintro t ⟨_,_,rest⟩
     exact (rest.gpr .x0 (by simp [gatherClobbers])).trans h.base
   · apply two_taint [.x0]
     · intro q s t hs ht r hr
       have : r= .x0 := by simpa using hr
       subst r
       exact hs.trans ht.symm
     · taint_decide

end VG.Proof.Ffdh.AArch64.Cached

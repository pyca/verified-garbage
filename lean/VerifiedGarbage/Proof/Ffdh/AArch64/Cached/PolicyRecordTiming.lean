module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyChoiceTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyStep
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Each public record has public length, cap, exact comparison, and next-record address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure RecordPublic where
 choice : ChoicePublic
 N : Nat
 fit : N<2^64

structure RecordReady (q : RecordPublic) (s : State) : Prop where
 scratch : Scr s q.choice.B q.choice.Z
 base : s.gpr .x0=q.choice.B
 source : Source q.choice.src q.choice.dom s
 record : PolicyRecordAt q.choice.B q.choice.recordPtr q.choice.g s
 domain : word s.mem q.choice.B (8*sDom)=q.choice.src
 length : word s.mem q.choice.B (8*sDL)=BitVec.ofNat 64 q.choice.dom.length
 keyLength : word s.mem q.choice.B (8*sLen)=BitVec.ofNat 64 q.choice.k
 width : word s.mem q.choice.B (8*sBits)=BitVec.ofNat 64 q.N
 pointer : s.gpr .x4=q.choice.recordPtr

structure RecordChoiceReady (q : RecordPublic) (s : State) : Prop extends ChoiceReady q.choice s where
 width : word s.mem q.choice.B (8*sBits)=BitVec.ofNat 64 q.N
 cap : s.gpr .x6=BitVec.ofNat 64 q.choice.g.bits

theorem policyRecord_ct : RelCT isa (Two RecordReady) Policy.record (fun _ _ =>True) := by
 unfold Policy.record
 refine RelCT.seq (two_piece (Ψ:=RecordChoiceReady) [.x0,.x4] (fun q s t hs ht r hr =>by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hs.base.trans ht.base.symm
  · exact hs.pointer.trans ht.pointer.symm) (by taint_decide) ?_) ?_
 · intro q s h
   refine WP.mono (policyRecordHead h.scratch q.choice.room h.base h.keyLength h.pointer h.record.readLen h.record.readBits
    h.record.length h.record.bits h.record.lenFit h.record.bitsFit) ?_
   rintro t ⟨⟨ptr,cap,test,mem⟩,rest⟩
   exact ⟨⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,h.source.of_mem mem rest,h.record.after_mem mem rest,
    mem ▸ h.domain,mem ▸ h.length,ptr,test⟩,mem ▸ h.width,cap⟩
 · refine RelCT.seq (two_post (Ψ:=fun q s =>s.gpr .x4=off q.choice.recordPtr 8)
    (two_map RecordPublic.choice (fun _ _ h =>h.toChoiceReady) policyChoice_ct) ?_)
    (two_taint [.x4] (fun q s t hs ht r hr =>by
     have eq : r= .x4 := by simpa using hr
     subst r;exact hs.trans ht.symm) (by taint_decide))
   intro q s h
   refine WP.mono (policyChoice_ok h.scratch q.choice.room h.base h.source h.record q.choice.shape q.choice.positive q.choice.size
    h.domain h.length h.width q.fit h.pointer h.cap h.test) ?_
   rintro t ⟨_,_,rest⟩
   exact (rest.gpr .x4 (by simp [choiceClobbers])).trans h.pointer

end VG.Proof.Ffdh.AArch64.Cached

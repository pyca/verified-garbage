module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyStep
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyMatchTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! ### `Ffdh.AArch64.Cached.PolicyChoiceTiming`, which only this module used -/

section

/-! Record selection branches only on the public domain width and exact public encoding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

structure ChoicePublic where
 B : Addr
 Z : Nat
 src : Addr
 recordPtr : Addr
 dom : List Byte
 g : Policy.Group
 k : Nat
 room : 256≤Z
 shape : dom.length=2*k ∨ dom.length=3*k
 positive : 0<k
 size : k<2^28

structure ChoiceReady (q : ChoicePublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 source : Source q.src q.dom s
 record : PolicyRecordAt q.B q.recordPtr q.g s
 domain : word s.mem q.B (8*sDom)=q.src
 length : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.dom.length
 pointer : s.gpr .x4=off q.recordPtr 8
 test : s.gpr .x3=BitVec.ofNat 64 q.k-BitVec.ofNat 64 q.g.len

theorem choice_eval {q : ChoicePublic} {s : State} (h : ChoiceReady q s) :
 isa.eval (.zero .x .x3) s=some (decide (q.k=q.g.len)) := by
 rw [eval_zero,h.test]
 change some (BitVec.ofNat 64 q.k-BitVec.ofNat 64 q.g.len==0#64)=_
 rw [sub_zero_iff (by have :=q.size;omega_using [this]) (by have :=h.record.lenFit;omega_using [this])]

def choiceCompare (q : ChoicePublic) (same : q.k=q.g.len) : ComparePublic :=
 ⟨q.B,q.Z,q.src,off q.recordPtr 8,q.dom,q.g.domain.take q.dom.length,q.room,
  by rw [List.length_take,policyDomain_length];have :=q.shape;omega_using [same, this],
  by have :=q.shape;have :=q.positive;omega_arith,
  by have :=q.shape;have :=q.size;omega_arith⟩

theorem choice_compare_ready {q : ChoicePublic} {s : State} (h : ChoiceReady q s) (same : q.k=q.g.len) :
 PolicyCompareReady (choiceCompare q same) s :=
 ⟨h.scratch,h.base,h.domain,h.length,h.pointer,h.source,h.record.source.take q.dom.length⟩

theorem policyChoice_ct : RelCT isa (Two ChoiceReady) Policy.recordChoice (fun _ _ =>True) := by
 change RelCT isa (fun s t =>∃ q,ChoiceReady q s ∧ ChoiceReady q t ∧ s.sp=t.sp) _ _
 apply RelCT.exists_
 intro q
 unfold Policy.recordChoice
 refine RelCT.ite (fun s t h =>(choice_eval h.1).trans (choice_eval h.2.1).symm) ?_ (RelCT.block_nil (fun _ _ _ =>trivial))
 by_cases same : q.k=q.g.len
 · exact compareChoice_ct.mono (fun s t h =>⟨choiceCompare q same,
    choice_compare_ready h.1.1 same,choice_compare_ready h.1.2.1 same,h.1.2.2⟩) (fun _ _ h =>h)
 · apply RelCT.of_false
   rintro s t ⟨⟨hs,_,_⟩,condition⟩
   rw [choice_eval hs,decide_eq_false same] at condition
   contradiction

end VG.Proof.Ffdh.AArch64.Cached

end

end


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

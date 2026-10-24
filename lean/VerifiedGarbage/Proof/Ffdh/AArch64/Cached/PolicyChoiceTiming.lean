module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyChoice
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyMatchTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

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
 rw [sub_zero_iff (by have :=q.size;omega) (by have :=h.record.lenFit;omega)]

def choiceCompare (q : ChoicePublic) (same : q.k=q.g.len) : ComparePublic :=
 ⟨q.B,q.Z,q.src,off q.recordPtr 8,q.dom,q.g.domain.take q.dom.length,q.room,
  by rw [List.length_take,policyDomain_length];have :=q.shape;omega,
  by have :=q.shape;have :=q.positive;omega,
  by have :=q.shape;have :=q.size;omega⟩

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

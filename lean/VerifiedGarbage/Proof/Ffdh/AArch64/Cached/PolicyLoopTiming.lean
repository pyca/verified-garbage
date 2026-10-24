module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyLoopTimingState
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Early policy-recognition exits are completely determined by public records and domain bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)

def PolicyLoopPair (n : Nat) (s t : State) : Prop :=
 ∃ q : PolicyLoopPublic,q.tail.length+1=n ∧ PolicyLoopReady q s ∧ PolicyLoopReady q t ∧ s.sp=t.sp

theorem policyLoop_ct : RelCT isa (Two PolicyLoopReady)
 (.loop Policy.record (.nonzero .x .x7)) (fun _ _ =>True) := by
 have step (n : Nat) : RelCT isa (PolicyLoopPair n) Policy.record fun s t =>
  isa.eval (.nonzero .x .x7) s=isa.eval (.nonzero .x .x7) t ∧
  (isa.eval (.nonzero .x .x7) s=some false→True) ∧
  (isa.eval (.nonzero .x .x7) s=some true→∃ m<n,PolicyLoopPair m s t) := by
  intro s t ts tt u v hp es et
  obtain ⟨q,length,hs,ht,sp⟩:=hp
  have ct:RelCT isa (Two PolicyLoopReady) Policy.record (fun _ _ =>True) :=
   two_map loopRecord (fun _ _ h =>h.record) policyRecord_ct
  have trace :=(ct _ _ _ _ _ _ ⟨q,hs,ht,sp⟩ es et).1
  obtain ⟨_,u',eu,ou⟩:=policyLoop_record_ok hs
  obtain ⟨_,v',ev,ov⟩:=policyLoop_record_ok ht
  obtain ⟨_,rfl⟩:=Exec.det es eu
  obtain ⟨_,rfl⟩:=Exec.det et ev
  refine ⟨trace,?_,fun _ =>trivial,?_⟩
  · rw [eval_nonzero,eval_nonzero,ou.2.1,ov.2.1]
  · intro more
    by_cases hit : recordMatches q
    · rw [eval_nonzero,ou.2.1,ite_eq_left hit] at more
      contradiction
    · cases tails : q.tail with
      | nil =>
        rw [eval_nonzero,ou.2.1,ite_eq_right hit,tails] at more
        contradiction
      | cons g tail =>
        refine ⟨tail.length+1,by rw [←length,tails];simp,policyNext q g tail (by rw [tails];simp),rfl,
         policyLoop_next hs ou hit tails,policyLoop_next ht ov hit tails,?_⟩
        rw [(Exec.rdwr es).2.2,(Exec.rdwr et).2.2]
        exact sp
 intro s t ts tt u v ⟨q,hs,ht,sp⟩ es et
 exact (RelCT.loop PolicyLoopPair step (q.tail.length+1)) _ _ _ _ _ _ ⟨q,rfl,hs,ht,sp⟩ es et

end VG.Proof.Ffdh.AArch64.Cached

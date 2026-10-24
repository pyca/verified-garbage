module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyCompareTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! The exact-match branch is public because both complete domain encodings are public. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def CompareDone (q : ComparePublic) (s : State) : Prop :=
 s.gpr .x0=q.B ∧ isa.eval (.zero .x .x11) s=some (decide (q.bs=q.cs))

theorem compareChoice_ct : RelCT isa (Two PolicyCompareReady)
 (.seq Policy.compare (.ite (.zero .x .x11) (.block Policy.matched) (.block []))) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=CompareDone) policyCompare_ct ?_) ?_
 · intro q s h
   exact WP.mono (policyCompare_agree h) (fun _ ⟨base,flag⟩ =>⟨base.symm.trans h.base,flag⟩)
 · refine RelCT.ite ?_ ?_ (RelCT.block_nil (fun _ _ _ =>trivial))
   · rintro s t ⟨q,hs,ht,_⟩
     exact hs.2.trans ht.2.symm
   · exact (two_taint [.x0] (Φ:=CompareDone) (fun q s t hs ht r hr =>by
      have eq : r= .x0 := by simpa using hr
      subst r;exact hs.1.trans ht.1.symm) (by taint_decide)).mono (fun _ _ h =>h.1) (fun _ _ h =>h)

end VG.Proof.Ffdh.AArch64.Cached

module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectScan
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Table masks may be secret. Only public pointers and loop counts control the trace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum.AArch64

/-- The row scan permits different masks and table contents in the two runs. -/
theorem selectRow_ct :
 RelCT isa (Two fun (p : Addr × Addr × BitVec 64) s =>
  s.gpr .x9=p.1 ∧ s.gpr .x8=p.2.1 ∧ s.gpr .x12=p.2.2)
 (countLoop .x12 VG.Impl.Ffdh.AArch64.Cached.Comb.selectWord) (fun _ _ => True) := by
 apply two_taint [.x9,.x8,.x12]
 · intro p s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl | rfl | rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm
 · taint_decide

/-- Loading the public header and computing a secret equality mask has no secret trace. -/
theorem selectHead_ct :
 RelCT isa (Two fun (B : Addr) s => s.gpr .x0=B)
 (.block VG.Impl.Ffdh.AArch64.Cached.Comb.selectHead) (fun _ _ => True) := by
 apply two_taint [.x0]
 · intro B s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   subst r
   exact hs.trans ht.symm
 · taint_decide

end VG.Proof.Ffdh.AArch64.Cached

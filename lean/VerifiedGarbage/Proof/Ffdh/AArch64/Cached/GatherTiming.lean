module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Gather
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Secret scalar bytes and digit accumulators never control an address or branch. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Proof.Bignum.AArch64

structure GatherPublic where
 source : Addr
 length : BitVec 64
 row : BitVec 64
 spacing : BitVec 64
 bits : BitVec 64

def GatherReady (p : GatherPublic) (s : State) : Prop :=
 s.gpr .x1=p.source ∧ s.gpr .x2=p.length ∧ s.gpr .x9=p.row ∧ s.gpr .x4=p.spacing ∧ s.gpr .x5=p.bits

/-- Neither scalar bytes nor the partial digit must agree between the runs. -/
theorem gather_ct : RelCT isa (Two GatherReady) VG.Impl.Ffdh.AArch64.Cached.Comb.gather (fun _ _ => True) := by
 apply two_taint [.x1,.x2,.x9,.x4,.x5]
 · intro p s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl | rfl | rfl | rfl | rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.1.trans ht.2.2.1.symm
   · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
   · exact hs.2.2.2.2.trans ht.2.2.2.2.symm
 · taint_decide

end VG.Proof.Ffdh.AArch64.Cached

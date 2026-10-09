import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryInnerPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Core

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The exact stored result of the complete selected machine schedule is the
standard forward NTT, represented by positive words below three times q. -/
theorem nttMemory_field {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w) :
    PosPolyIs (nttMemory m p ordinaryRoot innerRoot tailRoot) p (ntt w) := by
  have ho := outerPass_all h
  have hi := fivePassMem_field (by
    simpa only [Int.neg_mul] using ho)
  have hz : ordinaryRoot=(fun k => (zetaNat k : Int)) := rfl
  simpa only [nttMemory,hz,Traversal.traversal_ntt] using hi

end VG.Proof.MlDsa.AArch64.Optimized

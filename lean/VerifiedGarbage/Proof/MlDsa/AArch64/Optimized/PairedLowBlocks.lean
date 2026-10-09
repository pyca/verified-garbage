import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowStore2

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

/-- Proof-sized blocks in the original alternating instruction order. -/
def lowPairBlocks (g : Nat) (r q : VReg) (off : Nat) : List Instr :=
 lowLoadTwo r q off ++ reduceTwo .v24 .v25 r q ++ caddTwo .v24 .v25 r q ++
 lowHfTwo g .v24 r ++ lowWrapTwo g q ++ storeTwo .v26 .v28 .x15 off ++
 mlsTwo r ++ reduceTwo .v24 .v25 r q ++ storeTwo .v24 r .x16 off ++ normTwo r q

/-- No instruction, register reuse, or shared-flag update changes in this partition. -/
theorem r0Pair_blocks (g p j : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Pair g p j =
      lowPairBlocks g (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.vr (8*p+2*j))
        (VG.Impl.MlDsa.AArch64.Optimized.PairedBase.vr (8*p+2*j+1)) (1024*p+256*j) := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Pair
    VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane lowPairBlocks
    lowLoadTwo reduceTwo caddTwo lowHfTwo lowWrapTwo storeTwo mlsTwo normTwo
    reduceRegs lowCadd lowHf lowWrap normRegs
  by_cases hg : g==261888
  · simp only [hg,ite_true]
    rfl
  · simp only [hg]
    rfl
end VG.Proof.MlDsa.AArch64.Optimized.Paired

import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenRoundVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem primitives_ok : PrimsOk (primitives keccak.callee) 16 :=
  { prims_okWith (keccak := keccak) with
    add := CalleeOk.of_verified (by decide) AddSub.add_verified (by decide) (by dsimp only [primitives]; decide)
    power2Round := CalleeOk.of_verified (by decide) KeygenRound.power2Round_verified (by decide) (by dsimp only [primitives]; decide)
    simpleBitPack := CalleeOk.of_verified (by decide) KeygenPack.simple_verified (by decide) (by dsimp only [primitives]; decide)
    bitPack := CalleeOk.of_verified (by decide) KeygenPack.signed_verified (by decide) (by dsimp only [primitives]; decide) }

theorem two_callee : CalleeOk 16 Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
    (Spec.MlDsa.rejNTT2Contract AArch64.abi 16) :=
  CalleeOk.of_verified (by decide) ResidentRej.two_verified (by decide) (by decide)

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlDsa.RejNTT2Contract
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.PrimsOk
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem primitives_ok : PrimsOk (primitives keccak.callee) 16 :=
  prims_okWith (keccak := keccak)

theorem two_callee : CalleeOk 16 Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
    (Proof.MlDsa.rejNTT2Contract AArch64.abi 16) :=
  CalleeOk.of_verified (by decide) ResidentRej.two_verified (by decide) (by decide)

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

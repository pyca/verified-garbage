module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeApart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Traversal
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem primitives_ok : PrimsOk (primitives keccak.callee) 16 :=
  prims_okWith (keccak := keccak)

theorem two_callee : CalleeOk 16 Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
    (Spec.MlDsa.rejNTT2Contract AArch64.abi 16) :=
  CalleeOk.of_verified (by decide) ResidentRej.two_verified (by decide) (by decide)

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenVerified
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

theorem keyGen768_final (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
 (FixedHashCallers.keyGenUsing (fixedHash v.callee) lay768) keyGen768Contract :=
 keyGen768_verified v (kgG768_correct v) (kgH768_correct v)

theorem keyGen1024_final (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
 (FixedHashCallers.keyGenUsing (fixedHash v.callee) Impl.MlKem1024.AArch64.lay1024) keyGen1024Contract :=
 keyGen1024_verified v (kgG1024_correct v) (kgH1024_correct v)
end VG.Proof.MlKem.AArch64.FixedHash

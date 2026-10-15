module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenVerified
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

theorem keyGen768_final : Verified AArch64.target
 (FixedHashCallers.keyGenUsing fixedHash lay768) keyGen768Contract :=
 keyGen768_verified kgG768_correct kgH768_correct

theorem keyGen1024_final : Verified AArch64.target
 (FixedHashCallers.keyGenUsing fixedHash Impl.MlKem1024.AArch64.lay1024) keyGen1024Contract :=
 keyGen1024_verified kgG1024_correct kgH1024_correct
end VG.Proof.MlKem.AArch64.FixedHash

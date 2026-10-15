module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Depth
public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsTiming
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

theorem enA768_depth : (FixedHashCallers.enAUsing (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee) lay768).aarch64Depth≤1 := by decide +kernel

theorem enA768_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4]) (FixedHashCallers.enAUsing (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee) lay768) h).isSome=true := ⟨_,by taint_decide⟩

theorem enRest768_taint : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Impl.MlKem.AArch64.Optimized.enRestUsing prf lay768) h).isSome=true := ⟨_,by taint_decide⟩

theorem enA1024_depth : (FixedHashCallers.enAUsing (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 := by decide +kernel

theorem enA1024_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4]) (FixedHashCallers.enAUsing (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee) Impl.MlKem1024.AArch64.lay1024) h).isSome=true := ⟨_,by taint_decide⟩

theorem enRest1024_taint : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (Impl.MlKem.AArch64.Optimized.enRestUsing prf Impl.MlKem1024.AArch64.lay1024) h).isSome=true := ⟨_,by taint_decide⟩
end VG.Proof.MlKem.AArch64.FixedHash

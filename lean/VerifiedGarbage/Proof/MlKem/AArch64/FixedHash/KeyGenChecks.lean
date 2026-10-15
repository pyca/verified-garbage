module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Timing
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Depth
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Timing
meta import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashCallers
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized
abbrev fixedHash : HashFn := Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee

theorem kgA768_depth : (FixedHashCallers.kgAUsing fixedHash lay768).aarch64Depth≤1 := by decide +kernel
theorem kgA1024_depth : (FixedHashCallers.kgAUsing fixedHash Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 := by decide +kernel

theorem kgA768_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
 (FixedHashCallers.kgAUsing fixedHash lay768) h).isSome=true := ⟨_,by taint_decide⟩
theorem kgA1024_taint : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
 (FixedHashCallers.kgAUsing fixedHash Impl.MlKem1024.AArch64.lay1024) h).isSome=true := ⟨_,by taint_decide⟩

theorem kgRest768_taint : ∃h,((VectorSymbols.analysis restSymbols).check
 (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (FixedHashCallers.kgRestUsing fixedHash lay768) h).isSome=true :=
 ⟨_,by taint_decide⟩
theorem kgRest1024_taint : ∃h,((VectorSymbols.analysis restSymbols).check
 (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (FixedHashCallers.kgRestUsing fixedHash Impl.MlKem1024.AArch64.lay1024) h).isSome=true :=
 ⟨_,by taint_decide⟩
end VG.Proof.MlKem.AArch64.FixedHash

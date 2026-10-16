module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsTiming
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

theorem deStart768_depth : (FixedHashDecaps.deStartUsing fixedHash lay768).aarch64Depth≤1 := by decide +kernel
theorem deStart768_taint : ∃h,((VectorSymbols.analysis restSymbols).check
 (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashDecaps.deStartUsing fixedHash lay768) h).isSome=true :=
 ⟨_,by taint_decide⟩
theorem deRest768_taint : ∃h,((VectorSymbols.analysis restSymbols).check
 (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (FixedHashDecaps.deRestPrfUsing fixedHash prf lay768) h).isSome=true :=
 ⟨_,by taint_decide⟩

theorem deStart1024_depth : (FixedHashDecaps.deStartUsing fixedHash Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 := by decide +kernel
theorem deStart1024_taint : ∃h,((VectorSymbols.analysis restSymbols).check
 (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashDecaps.deStartUsing fixedHash Impl.MlKem1024.AArch64.lay1024) h).isSome=true :=
 ⟨_,by taint_decide⟩
theorem deRest1024_taint : ∃h,((VectorSymbols.analysis restSymbols).check
 (VectorTaint.ofRegs [.x25,.x26,.x27,.x28]) (FixedHashDecaps.deRestPrfUsing fixedHash prf Impl.MlKem1024.AArch64.lay1024) h).isSome=true :=
 ⟨_,by taint_decide⟩
end VG.Proof.MlKem.AArch64.FixedHash

module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Taints

/-! # Maximum stack depth of optimized prefixes and matrix sampling -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem kgA768_depth : (KemLay.kgAWith lay768 Sha3.AArch64.Sha3.callee).aarch64Depth≤1 := by decide

theorem deStart768_depth : (Impl.MlKem.AArch64.Optimized.deStart Sha3.AArch64.Sha3.callee lay768).aarch64Depth≤1 := by decide

theorem kgA1024_depth : (KemLay.kgAWith Impl.MlKem1024.AArch64.lay1024 Sha3.AArch64.Sha3.callee).aarch64Depth≤1 := by decide

theorem deStart1024_depth : (Impl.MlKem.AArch64.Optimized.deStart Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 := by decide

end VG.Proof.MlKem.AArch64.Optimized

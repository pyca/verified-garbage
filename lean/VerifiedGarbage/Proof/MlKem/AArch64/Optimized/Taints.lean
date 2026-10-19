module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
meta import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
meta import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps

/-! # Public-address checks for the optimized code surrounding matrix generation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Callers

theorem deStart768_taint :
    ∃h,((VectorSymbols.analysis ["VG_MLKEM_GAMMA","VG_MLKEM_NTT16_ZETAS","VG_MLKEM_INTT16_ZETAS"]).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (Impl.MlKem.AArch64.Optimized.deStart Sha3.AArch64.Sha3.callee lay768) h).isSome=true := by
  exact ⟨_, by taint_decide⟩

theorem deStart1024_taint :
    ∃h,((VectorSymbols.analysis ["VG_MLKEM_GAMMA","VG_MLKEM_NTT16_ZETAS","VG_MLKEM_INTT16_ZETAS"]).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (Impl.MlKem.AArch64.Optimized.deStart Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) h).isSome=true := by
  exact ⟨_, by taint_decide⟩

end VG.Proof.MlKem.AArch64.Optimized

module
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
meta import VerifiedGarbage.TCB.Axioms

/-! # The checks of the hashing decapsulation, for any permutation (as `KeyGenChecks`) -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

theorem deStart768_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashDecaps.deStartUsing (fixedHash v.callee) lay768).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name) (e := FixedHashDecaps.deStartUsing (fixedHash hole) lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
theorem deStart768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check
      (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashDecaps.deStartUsing (fixedHash c) lay768) h).isSome=true := by
  taint_decide_generic c := hole using hS
theorem deStart1024_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashDecaps.deStartUsing (fixedHash v.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := FixedHashDecaps.deStartUsing (fixedHash hole) Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
theorem deStart1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (FixedHashDecaps.deStartUsing (fixedHash c) Impl.MlKem1024.AArch64.lay1024) h).isSome=true := by
  taint_decide_generic c := hole using hS
end VG.Proof.MlKem.AArch64.FixedHash

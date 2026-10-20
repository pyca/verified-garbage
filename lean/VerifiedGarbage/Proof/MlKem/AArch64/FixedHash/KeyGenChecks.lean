module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms

/-!
# The checks of the hashing key generation, for any permutation

Its stack depth from that of its code with the permutation's calls erased
(`hole`), and its constant time from the analysis of its code with the calls
of any permutation `c` summarized (`Callers.sums c`, `taint_decide_generic`):
each decided once, for every Keccak backend.
-/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

/-- The summaries of the calls of the permutation of `v` for the analysis with
public table addresses, from those of the vector analysis. -/
theorem symSums (v : Proof.Sha3.AArch64.Permutation) :
    Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums v.callee) :=
  VectorSymbols.allOk_of_vector restSymbols v.callerSums

theorem kgA768_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashCallers.kgAUsing (fixedHash v.callee) lay768).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name) (e := FixedHashCallers.kgAUsing (fixedHash hole) lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
theorem kgA1024_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashCallers.kgAUsing (fixedHash v.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name) (e := FixedHashCallers.kgAUsing (fixedHash hole) Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)

theorem kgA768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk VectorTaint.taint (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (FixedHashCallers.kgAUsing (fixedHash c) lay768) h).isSome=true := by
  taint_decide_generic c := hole using hS
theorem kgA1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk VectorTaint.taint (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (FixedHashCallers.kgAUsing (fixedHash c) Impl.MlKem1024.AArch64.lay1024) h).isSome=true := by
  taint_decide_generic c := hole using hS

end VG.Proof.MlKem.AArch64.FixedHash

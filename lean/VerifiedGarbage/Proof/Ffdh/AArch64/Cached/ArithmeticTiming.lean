module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ArithmeticTimingState
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Compose public field setup with context serialization and the complete fixed-base table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64

theorem precomputeArithmetic_ct (M : Mont) : RelCT isa (Two ArithmeticReady)
 (.seq (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm))
  (.seq Precompute.storePrefix (.seq (Precompute.table M.mm) (.block [movi .x0 1])))) (fun _ _ =>True) :=
 RelCT.seq (two_post (two_map arithmeticPc (fun _ _ h =>h.pc) (precomputeField_ct M))
  (fun _ _ h =>arithmeticField_done M h))
  ((precomputeTail_ct M).mono (fun _ _ h =>arithmeticDone_two h) (fun _ _ h =>h))

end VG.Proof.Ffdh.AArch64.Cached

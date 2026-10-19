module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Impl.MlKem.AArch64.FixedHashDecaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming

/-! # The checks of the hashing decapsulation, for any permutation (as `KeyGenChecks`) -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64.Optimized

theorem deStart768_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashDecaps.deStartUsing (fixedHash v.callee) lay768).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name) (e := FixedHashDecaps.deStartUsing (fixedHash hole) lay768)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
theorem deStart1024_depth (v : Proof.Sha3.AArch64.Permutation) :
    (FixedHashDecaps.deStartUsing (fixedHash v.callee) Impl.MlKem1024.AArch64.lay1024).aarch64Depth≤1 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := FixedHashDecaps.deStartUsing (fixedHash hole) Impl.MlKem1024.AArch64.lay1024)
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)
end VG.Proof.MlKem.AArch64.FixedHash

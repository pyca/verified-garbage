module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackVerified
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.UseHintPack
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MlDsa.UseHintPack
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackVerified
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackEncode
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackCoefficients
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackEncode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackEncode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce

@[expose] public section

namespace VG.Artifacts.MlDsaUseHintPack.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.useHintPackApi 261888).artifact VG.AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (.inl rfl) },
  (Spec.MlDsa.useHintPackApi 95232).artifact VG.AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
    verified := Proof.MlDsa.AArch64.Optimized.UseHintPack.pack_verified (.inr rfl) }]

end VG.Artifacts.MlDsaUseHintPack.AArch64

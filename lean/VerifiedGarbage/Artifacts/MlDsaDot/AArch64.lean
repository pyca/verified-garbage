module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
import Std.Data.DTreeMap.Internal.Operations
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.DotInverse
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MlDsa.FusedInverse
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
public import VerifiedGarbage.Proof.MlDsa.Pack.Stream
public import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
public import VerifiedGarbage.Spec.MlDsa.PositiveNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSpecPre
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Spec.MlDsa.PositiveNtt

@[expose] public section

namespace VG.Artifacts.MlDsaDot.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.dotInverseApi 4).artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode 4
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified (.inl rfl) },
  (Spec.MlDsa.dotInverseApi 5).artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode 5
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified (.inr (.inl rfl)) },
  (Spec.MlDsa.dotInverseApi 7).artifact AArch64.target {
    consts := Impl.MlDsa.AArch64.Optimized.Inverse.inverseConsts
    code := Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode 7
    verified := Proof.MlDsa.AArch64.Optimized.Inverse.dot_verified (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaDot.AArch64

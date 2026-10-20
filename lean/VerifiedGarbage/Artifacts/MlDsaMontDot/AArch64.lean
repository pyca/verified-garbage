module

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MontDot
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.MlDsa.MontDot
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotVerified
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layers
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedStep
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotMem
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
public import VerifiedGarbage.Spec.MlDsa.PositiveNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Layers
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLayer
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Word
import VerifiedGarbage.Spec.MlDsa.PositiveNtt

@[expose] public section

namespace VG.Artifacts.MlDsaMontDot.AArch64

def artifacts : List Artifact := [
  (Spec.MlDsa.montDotApi 4).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.MontDot.dot 4
    verified := Proof.MlDsa.AArch64.Optimized.MontDot.verified (.inl rfl) },
  (Spec.MlDsa.montDotApi 5).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.MontDot.dot 5
    verified := Proof.MlDsa.AArch64.Optimized.MontDot.verified (.inr (.inl rfl)) },
  (Spec.MlDsa.montDotApi 7).artifact AArch64.target {
    code := Impl.MlDsa.AArch64.Optimized.MontDot.dot 7
    verified := Proof.MlDsa.AArch64.Optimized.MontDot.verified (.inr (.inr rfl)) }]

end VG.Artifacts.MlDsaMontDot.AArch64

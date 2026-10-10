import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Sha3.AArch64.Callers.MlKem
import VerifiedGarbage.Proof.Sha3.AArch64.Callers.MlDsa

namespace VG.Proof.Sha3.AArch64.Scalar.VectorSlots

open VG VG.AArch64

def callee : Impl.Sha3.AArch64.Callee where
  name := "vg_keccak_f1600"
  code := Impl.Sha3.AArch64.Scalar.unrolledPermute
  suffix := ""
  absorbOverride := none

/- The rounds of the permutation, from nothing public. They write every
general-purpose register but no vector register other than the temporary
lanes `v24` and `v25`, so they keep public the vectors that hold the
callee-saved registers and the pointers (`Boundary.save`). Each summary of
the permutation below uses this one rather than analysing the rounds again. -/
taint_summary VSums.rounds : VectorTaint.taint (VectorTaint.ofRegs [])
  (.block Impl.Sha3.AArch64.Scalar.unrolledRounds)
  keeping ((AArch64.Taint.ofRegs [], RegSet.ofList
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15,
      .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v26, .v27, .v28, .v29, .v30, .v31]) : VectorTaint.T)

sponge_taint_summaries VSums callee saving using VSums.rounds

/-- The summaries the sponge's callers' checks use (`Callers.sums`). -/
theorem callerSums : Taint.AllOk VectorTaint.taint (Callers.sums callee) :=
  Callers.sums_ok (by
    exact
      .cons (VSums.absorb23.weaken (by decide)) <|
      .cons (VSums.absorb24.weaken (by decide)) <|
      .cons (VSums.absorb28.weaken (by decide)) <|
      .cons (VSums.absorb27.weaken (by decide)) <|
      .cons (VSums.absorb24_26.weaken (by decide)) <|
      .cons (VSums.pad28.weaken (by decide)) <|
      .cons (VSums.pad27.weaken (by decide)) <|
      .cons (VSums.pad26.weaken (by decide)) <|
      .cons (VSums.squeeze28.weaken (by decide)) <|
      .cons (VSums.squeeze27.weaken (by decide)) <|
      .cons (VSums.squeeze26.weaken (by decide)) <|
      .cons (VSums.perm28s.weaken (by decide)) <|
      .cons (VSums.perm27s.weaken (by decide)) <|
      .cons (VSums.perm26s.weaken (by decide)) <|
      .cons (VSums.permS.weaken (by decide)) <|
      .cons (VSums.perm28.weaken (by decide)) <|
      .cons (VSums.perm27.weaken (by decide)) <|
      .cons (VSums.perm26.weaken (by decide)) <|
      .cons (VSums.perm.weaken (by decide)) <|
      .nil)

theorem absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem sampleFullTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith callee) h).isSome = true :=
  Callers.sampleFullTaint _ callerSums

theorem sampleFastTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true :=
  Callers.sampleFastTaint _ callerSums

theorem mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true :=
  Callers.mldsaNttTaint _ callerSums

theorem mldsaBoundedTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 544) h).isSome = true :=
  Callers.mldsaBoundedTaint _ callerSums

theorem mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true :=
  Callers.mldsaBallTaint _ callerSums

theorem mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true :=
  Callers.mldsaMaskTaint _ callerSums

theorem mlkemKgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith callee) h).isSome = true :=
  Callers.mlkemKgATaint _ callerSums

theorem mlkemKgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith callee) h).isSome = true :=
  Callers.mlkemKgCTaint _ callerSums

theorem mlkemEnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith callee) h).isSome = true :=
  Callers.mlkemEnATaint _ callerSums

theorem mlkemEnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith callee) h).isSome = true :=
  Callers.mlkemEnCTaint _ callerSums

theorem mlkemDeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith callee) h).isSome = true :=
  Callers.mlkemDeATaint _ callerSums

theorem mlkemDeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith callee) h).isSome = true :=
  Callers.mlkemDeCTaint _ callerSums

theorem mlkem1024KgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith callee) h).isSome = true :=
  Callers.mlkem1024KgATaint _ callerSums

theorem mlkem1024KgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith callee) h).isSome = true :=
  Callers.mlkem1024KgCTaint _ callerSums

theorem mlkem1024EnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith callee) h).isSome = true :=
  Callers.mlkem1024EnATaint _ callerSums

theorem mlkem1024EnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith callee) h).isSome = true :=
  Callers.mlkem1024EnCTaint _ callerSums

theorem mlkem1024DeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith callee) h).isSome = true :=
  Callers.mlkem1024DeATaint _ callerSums

theorem mlkem1024DeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith callee) h).isSome = true :=
  Callers.mlkem1024DeCTaint _ callerSums

theorem mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true :=
  Callers.mldsaSeedsTaint _ callerSums

theorem mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true :=
  Callers.mldsaTrHashTaint _ callerSums

theorem mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true :=
  Callers.mldsaVerifyHashTaint _ callerSums

theorem mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true :=
  Callers.mldsaSignDecodeTaint _ callerSums

theorem mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true :=
  Callers.mldsaSignCommitTaint _ callerSums

def backend : Permutation where
  callee := callee
  features := []
  ok := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_correct
  noFrames := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_noFrames
  absorbOverrideOk := by intro code h; cases h
  absorbOverrideDepth := by intro code h; cases h
  absorbTaint := absorbTaint
  padTaint := padTaint
  squeezeTaint := squeezeTaint
  sampleFullTaint := sampleFullTaint
  sampleFastTaint := sampleFastTaint
  mldsaNttTaint := mldsaNttTaint
  mldsaBoundedTaint := mldsaBoundedTaint
  mldsaBallTaint := mldsaBallTaint
  mldsaMaskTaint := mldsaMaskTaint
  mlkemKgATaint := mlkemKgATaint
  mlkemKgCTaint := mlkemKgCTaint
  mlkemEnATaint := mlkemEnATaint
  mlkemEnCTaint := mlkemEnCTaint
  mlkemDeATaint := mlkemDeATaint
  mlkemDeCTaint := mlkemDeCTaint
  mlkem1024KgATaint := mlkem1024KgATaint
  mlkem1024KgCTaint := mlkem1024KgCTaint
  mlkem1024EnATaint := mlkem1024EnATaint
  mlkem1024EnCTaint := mlkem1024EnCTaint
  mlkem1024DeATaint := mlkem1024DeATaint
  mlkem1024DeCTaint := mlkem1024DeCTaint

  mldsaSeedsTaint := mldsaSeedsTaint
  mldsaTrHashTaint := mldsaTrHashTaint
  mldsaVerifyHashTaint := mldsaVerifyHashTaint

  mldsaSignDecodeTaint := mldsaSignDecodeTaint
  mldsaSignCommitTaint := mldsaSignCommitTaint

end VG.Proof.Sha3.AArch64.Scalar.VectorSlots

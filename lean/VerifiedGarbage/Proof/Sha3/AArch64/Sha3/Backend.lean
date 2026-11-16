module

public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Sums
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3

open VG VG.AArch64

def callee : Impl.Sha3.AArch64.Callee where
  name := "vg_keccak_f1600_sha3"
  code := Impl.Sha3.AArch64.Sha3.Vector.permute
  suffix := "_sha3"
  pairedSha3 := true
  absorbOverride := none

sponge_taint_summaries Sha3Sums callee

/-- The summaries the sponge's callers' checks use (`Callers.sums`, from this backend's summaries
with their frames: `Taint.SumOk.restrict`). -/
theorem callerSums : Taint.AllOk VectorTaint.taint (Callers.sums callee) :=
  Callers.sums_ok (by
    exact
      .cons (Sha3Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.pad.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.pad.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.pad.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.squeeze.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.squeeze.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.squeeze.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sha3Sums.perm.restrict (by decide) (by decide)) <|
      .nil)

theorem absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true :=
  -- From the summary of a call of it.
  Taint.exists_check_of_sumOk_call Sha3Sums.absorb (VG.AArch64.VectorTaint.le_refl _) rfl

theorem padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true :=
  -- From the summary of a call of it.
  Taint.exists_check_of_sumOk_call Sha3Sums.pad (VG.AArch64.VectorTaint.le_refl _) rfl

theorem squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true :=
  -- From the summary of a call of it.
  Taint.exists_check_of_sumOk_call Sha3Sums.squeeze (VG.AArch64.VectorTaint.le_refl _) rfl

theorem mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true :=
  Callers.mldsaNttTaint _ callerSums

theorem mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true :=
  Callers.mldsaBallTaint _ callerSums

theorem mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true :=
  Callers.mldsaMaskTaint _ callerSums

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
  features := ["sha3"]
  ok := Vector.permute_correct
  noFrames := Vector.permute_noFrames
  noDit := by lit_decide
  callerSums := callerSums
  absorbOverrideOk := by intro code h; cases h
  absorbOverrideDepth := by intro code h; cases h
  absorbOverrideNoDit := by intro code h; cases h
  absorbTaint := absorbTaint
  padTaint := padTaint
  squeezeTaint := squeezeTaint
  mldsaNttTaint := mldsaNttTaint
  mldsaBallTaint := mldsaBallTaint
  mldsaMaskTaint := mldsaMaskTaint

  mldsaSeedsTaint := mldsaSeedsTaint
  mldsaTrHashTaint := mldsaTrHashTaint
  mldsaVerifyHashTaint := mldsaVerifyHashTaint

  mldsaSignDecodeTaint := mldsaSignDecodeTaint
  mldsaSignCommitTaint := mldsaSignCommitTaint

end VG.Proof.Sha3.AArch64.Sha3

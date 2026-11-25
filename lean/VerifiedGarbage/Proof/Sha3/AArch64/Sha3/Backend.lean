module

public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Absorb
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Lit

/-! # Keccak-f[1600] on AArch64, with FEAT_SHA3: the backend of the sponge -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

sponge_taint_summaries Sums Impl.Sha3.AArch64.Sha3.Vector.callee

theorem callerSums : Taint.AllOk VectorTaint.taint (Callers.sums Impl.Sha3.AArch64.Sha3.Vector.callee) :=
  Callers.sums_ok (by
    exact
      .cons (Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sums.absorb.restrict (by decide) (by decide)) <|
      .cons (Sums.pad.restrict (by decide) (by decide)) <|
      .cons (Sums.pad.restrict (by decide) (by decide)) <|
      .cons (Sums.pad.restrict (by decide) (by decide)) <|
      .cons (Sums.squeeze.restrict (by decide) (by decide)) <|
      .cons (Sums.squeeze.restrict (by decide) (by decide)) <|
      .cons (Sums.squeeze.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .cons (Sums.perm.restrict (by decide) (by decide)) <|
      .nil)

/-- The backend with FEAT_SHA3. -/
def backend : Permutation where
  callee := Impl.Sha3.AArch64.Sha3.Vector.callee
  features := ["sha3"]
  scrub := by lit_decide
  blocksScrub := by intro _ _ h; cases h; lit_decide
  ok := fun s h => permute_ok s h
  noFrames := by lit_decide
  noDit := by lit_decide
  callerSums := callerSums
  blocksOk := by intro _ _ h s hp; cases h; exact absorbBlocks_ok s hp
  blocksNoFrames := by intro _ _ h; cases h; lit_decide
  blocksNoDit := by intro _ _ h; cases h; lit_decide
  absorbTaint := by sponge_taint_decide Sums
  padTaint := by sponge_taint_decide Sums
  squeezeTaint := by sponge_taint_decide Sums
  mldsaNttTaint := Callers.mldsaNttTaint _ callerSums
  mldsaBallTaint := Callers.mldsaBallTaint _ callerSums
  mldsaMaskTaint := Callers.mldsaMaskTaint _ callerSums
  mldsaSeedsTaint := Callers.mldsaSeedsTaint _ callerSums
  mldsaTrHashTaint := Callers.mldsaTrHashTaint _ callerSums
  mldsaVerifyHashTaint := Callers.mldsaVerifyHashTaint _ callerSums
  mldsaSignDecodeTaint := Callers.mldsaSignDecodeTaint _ callerSums
  mldsaSignCommitTaint := Callers.mldsaSignCommitTaint _ callerSums

end VG.Proof.Sha3.AArch64.Sha3.Vector

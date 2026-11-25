module

public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Absorb
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Variant
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lit

/-! # Keccak-f[1600] on AArch64, in general registers: the backend of the sponge -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Scalar

-- The rounds keep public every vector register but the two they use.
taint_summary Sums.rounds : VectorTaint.taint (VectorTaint.ofRegs [.x28]) Impl.Sha3.AArch64.Scalar.core
  keeping ((VectorTaint.ofRegs []).1,
    RegSet.ofList [VReg.v0, .v1, .v2, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v29, .v30])

sponge_taint_summaries Sums Impl.Sha3.AArch64.Scalar.callee saving using Sums.rounds

theorem callerSums : Taint.AllOk VectorTaint.taint (Callers.sums Impl.Sha3.AArch64.Scalar.callee) :=
  Callers.sums_ok (by
    exact
      .cons (Sums.absorb23.weaken (by decide)) <|
      .cons (Sums.absorb24.weaken (by decide)) <|
      .cons (Sums.absorb28.weaken (by decide)) <|
      .cons (Sums.absorb27.weaken (by decide)) <|
      .cons (Sums.absorb24_26.weaken (by decide)) <|
      .cons (Sums.pad28.weaken (by decide)) <|
      .cons (Sums.pad27.weaken (by decide)) <|
      .cons (Sums.pad26.weaken (by decide)) <|
      .cons (Sums.squeeze28.weaken (by decide)) <|
      .cons (Sums.squeeze27.weaken (by decide)) <|
      .cons (Sums.squeeze26.weaken (by decide)) <|
      .cons (Sums.perm28s.weaken (by decide)) <|
      .cons (Sums.perm27s.weaken (by decide)) <|
      .cons (Sums.perm26s.weaken (by decide)) <|
      .cons (Sums.permS.weaken (by decide)) <|
      .cons (Sums.perm28.weaken (by decide)) <|
      .cons (Sums.perm27.weaken (by decide)) <|
      .cons (Sums.perm26.weaken (by decide)) <|
      .cons (Sums.perm.weaken (by decide)) <|
      .nil)

/-- The backend in general registers. -/
def backend : Permutation where
  callee := Impl.Sha3.AArch64.Scalar.callee
  features := []
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

end VG.Proof.Sha3.AArch64.Scalar

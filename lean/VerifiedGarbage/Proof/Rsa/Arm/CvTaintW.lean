module

public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
meta import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # `vg_rsa_crt_values` on ARMv7: the balanced key's pieces the taint analysis checks

`shapeCv` and the pieces of `midW` between its product and divisions by words
(`KeyDiv.mulLo_ct`, `KeyDiv.divW_ct`), and those functions' own pieces for the
arrays they are called on: from the stack arguments and `r7`–`r9`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.KeyDiv

/-- `midW` after the product, to the first division. -/
abbrev chunkW : List (Prog isa) := [eqS sE1 aDR aDQ aT1, eqS sE2 aZero aZero aT1] ++ invSetup ++ [
  .block primeWidth, inverse, .block ctx, eqS sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy aDQ aD, copy aDD aP, .block (clrLow aDD ++ divHdr aDQ aDR2 aDD aDT),
  copy 0 aZero, copy aDD aP, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]

theorem shapeCv_taint : ∃ hc, (VG.Taint.check taint (argTaint [] 48) (.block shapeCv) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem oddW_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [] 48) (.block (ctx ++ bitOf sPodd aP)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkW_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r7, .r8, .r9] 48) (seqs chunkW) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem setQ_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r7, .r8, .r9] 48)
    (seqs [copy aDD aQ, .block (clrLow aDD ++ VG.Impl.Rsa.Arm.KeyDiv.fixTop aDD)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mulW_taint : MulTaint aDR aP aQ :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem divW2_taint : DivTaint aD aDR2 aDD aDQ aDT aT1 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem divW3_taint : DivTaint aD aDR3 aDD aDQ aDT aT1 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.Rsa.Arm.CrtValues

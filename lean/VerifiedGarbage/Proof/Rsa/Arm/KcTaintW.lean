module

public import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
public import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Impl.Rsa.Arm.KeyCheck
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.Arm.KdDivCT
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The checks of a balanced RSA key on ARMv7: the pieces the taint analysis checks

`keyBodyW` between its products and divisions by words (`KeyDiv.mulLo_ct`,
`KeyDiv.divW_ct`), and those functions' own pieces for the arrays they are
called on: each from `r8` and `n_len` in `r11` at the start, and `r7`–`r9`
otherwise.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.KeyDiv

/-- The checks between the first product and the next: `p q = n`, `p - 1`, `q - 1`, `dP < p - 1`. -/
abbrev chunkA : List (Prog isa) := eqA aVQ aN ++
  [copy aM1 aP, .block (clrLow aM1), copy aM2 aQ, .block (clrLow aM2)] ++ ltA aDP aM1
/-- `e dP mod (p - 1) = 1`, `dQ < q - 1`. -/
abbrev chunkB : List (Prog isa) := eqA aVR aOne ++ ltA aDQ aM2
/-- `e dQ mod (q - 1) = 1`, `qInv < p`. -/
abbrev chunkC : List (Prog isa) := eqA aVR aOne ++ ltA aQI aP

/-- `shape`, from `n_len` in `r11` and the stack arguments. -/
theorem shape_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r11] (4 * 14))
    (.block (VG.Impl.Rsa.Arm.KeyDiv.shape4 12 20 28 36)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem startW_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r8, .r11]) startW hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkA_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (seqs chunkA) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkB_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (seqs chunkB) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkC_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (seqs chunkC) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem divSetP_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (seqs [copy aVD aP, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem divSetM1_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (seqs [copy aVD aM1, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem divSetM2_taint : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9])
    (seqs [copy aVD aM2, .block (VG.Impl.Rsa.Arm.KeyDiv.fixTop aVD)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunk2_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (seqs (eqA aVR aOne ++ ltA aD aN)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunk3_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (seqs (eqA aVR aDP)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunk4_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r7, .r8, .r9]) (seqs (eqA aVR aDQ)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mulVQ_taint : MulTaint aVQ aP aQ :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem mulT_taint : MulTaint aT aQI aQ :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem mulDP_taint : MulTaint aA aE aDP (some 2) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem mulDQ_taint : MulTaint aA aE aDQ (some 2) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem divA_taint : DivTaint aA aVR aVD aVT aY aX (some 2) :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem divT_taint : DivTaint aT aVR aVD aVT aY aX :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem divD_taint : DivTaint aD aVR aVD aVT aY aX :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.Rsa.Arm.KeyCheck

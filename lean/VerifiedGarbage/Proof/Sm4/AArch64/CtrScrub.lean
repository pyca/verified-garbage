module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CtrFinal

/-!
# SM4's key expansion and CTR on AArch64, without secret residue

The postconditions of `vg_sm4_expand_key`, `vg_sm4_ctr` and
`vg_sm4_ctr_final` read the memory on return only within their buffers
(`ScrubAll.ScrubAllOk`, from `Proof.Sm4`'s `*PostOut_local`): each
implementation returns with every register it may leave secret cleared, and
its whole stack zeroed, if it has one (`ScrubAll.withScrubAll`). The CTR
functions' frames, which no longer zero themselves, are among that stack.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.CtrScrub

open VG.AArch64 VG.AArch64.ScrubAll

theorem expandKeyOk : ScrubAllOk (Spec.Sm4.expandKeyContract abi) 0 (Spec.Sm4.expandKeySig.retBits abi.ptrBits) :=
  scrubAllOk_regs0 (sig := Spec.Sm4.expandKeySig) (post := Proof.Sm4.expandKeyPost abi.ptrBits) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _)

theorem ctrOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (Spec.Sm4.ctrContract abi W) W (Spec.Sm4.ctrSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := Spec.Sm4.ctrSig) (post := Proof.Sm4.ctrPost abi.ptrBits) (by decide) hW (Nat.le_refl _)
    (Proof.Sm4.ctrPostOut_local _)

theorem ctrFinalOk : ScrubAllOk (Spec.Sm4.ctrFinalContract abi 3344) 3344
    (Spec.Sm4.ctrFinalSig.retBits abi.ptrBits) := by
  rw [Proof.Sm4.ctrFinalContract_eq]
  exact scrubAllOk_regs (by decide) (by decide) (Nat.le_refl _) (Proof.Sm4.ctrFinalPostOut_local _)

end VG.Proof.Sm4.AArch64.CtrScrub

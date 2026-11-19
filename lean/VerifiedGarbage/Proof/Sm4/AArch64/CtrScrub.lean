module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public import VerifiedGarbage.Impl.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CtrFinal

/-!
# SM4's key expansion and CTR on AArch64, without secret residue

The postconditions of `vg_sm4_expand_key`, `vg_sm4_ctr` and
`vg_sm4_ctr_final` read the memory on return only within their buffers
(`ScrubAll.ScrubAllOk`, from `Proof.Sm4`'s `*PostOut_local`): each
implementation returns with every register it may leave secret cleared, and
its whole stack zeroed, if it has one (`ScrubAll.scrubAllOf`). The CTR
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

/-- The registers `vg_sm4_ctr_final` writes itself: its tail clears them
with those its `vg_sm4_ctr` writes (`CtrImpl.clear`). -/
def ctrFinalOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23],
   []⟩

/-- What `scrubAllOf` needs of `vg_sm4_ctr_final` with each `vg_sm4_ctr`:
evaluated here. -/
theorem ctrFinalSide (v : Proof.Sm4.AArch64.CtrFinal.CtrImpl) (hv : v ∈ Proof.Variants.Sm4Ctr.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 (Impl.Sm4.AArch64.ctrFinal v.name v.code))
      3344 (Spec.Sm4.ctrFinalSig.retBits abi.ptrBits) (clearUnion ctrFinalOwn v.clear) [] = true := by
  have e : (Proof.Variants.Sm4Ctr.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 (Impl.Sm4.AArch64.ctrFinal v.name v.code))
        3344 (Spec.Sm4.ctrFinalSig.retBits abi.ptrBits) (clearUnion ctrFinalOwn v.clear) []) = true := by
    lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.Sm4.AArch64.CtrScrub

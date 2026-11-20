module

public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Impl.Sm4.AArch64.Serial.Key
import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Sm4.CtrFinal

/-!
# SM4's key expansion and CTR on AArch64, without secret residue

The postconditions of `vg_sm4_expand_key`, `vg_sm4_ctr` and
`vg_sm4_ctr_final` read the memory on return only within their buffers
(`ScrubAll.ScrubAllOk`, from `Proof.Sm4`'s `*PostOut_local`): each
implementation returns with every register it may leave secret cleared, and
its whole stack zeroed, if it has one (`Impl.Residue.AArch64.scrubAll`, in the function as emitted). The CTR
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

/-! ## The functions, as emitted

`vg_sm4_expand_key`, `vg_sm4_ctr`, `vg_sm4_ctr_sm4` and `vg_sm4_ctr_final`
with their cleanup (`Impl.Sm4.AArch64.Serial.Fn`, `Impl.Sm4.AArch64.Fn`):
each meets its contract in constant time and returns without secret residue
(`VerifiedScrubbed`), which is what its registration binds. What the cleanup
needs of the code (`ScrubAll.scrubSide`) is evaluated here, by the kernel:
of `vg_sm4_ctr_final`, of its own instructions, once, with code that does
nothing in the place of `vg_sm4_ctr`, each implementation of which proves
its own where it is defined (`CtrImpl.scrub`). -/

theorem expandKey :
    VerifiedScrubbed target Impl.Sm4.AArch64.Serial.Fn.expandKey (Spec.Sm4.expandKeyContract abi) 0 :=
  verifiedScrubbed (api := Spec.Sm4.expandKeyApi)
    { code := Impl.Sm4.AArch64.Serial.expandKey, verified := Proof.Sm4.AArch64.Serial.expandKey_verified } _
    expandKeyOk (by dsimp only; lit_decide)

theorem ctrSm4 :
    VerifiedScrubbed target Impl.Sm4.AArch64.Fn.ctrSm4 (Spec.Sm4.ctrContract abi 224) 0 :=
  verifiedScrubbed (api := Spec.Sm4.ctrApi)
    { code := Impl.Sm4.AArch64.ctrFramedSm4, verified := Proof.Sm4.AArch64.Sm4e.ctr_framed } _
    (ctrOk 224) (by dsimp only; lit_decide)

theorem ctr :
    VerifiedScrubbed target Impl.Sm4.AArch64.Fn.ctr (Spec.Sm4.ctrContract abi 3264) 0 :=
  verifiedScrubbed (api := Spec.Sm4.ctrApi)
    { code := Impl.Sm4.AArch64.ctrFramed, verified := Proof.Sm4.AArch64.ctr_framed } _
    (ctrOk 3264) (by dsimp only; lit_decide)

private theorem ctrFinal_all {p : Instr → Bool} (name : String) (code : Prog isa)
    (h0 : sideAll p (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10
      (Impl.Sm4.AArch64.ctrFinal "" (.block []))) = true) (hc : sideAll p code = true) :
    sideAll p (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10
      (Impl.Sm4.AArch64.ctrFinal name code)) = true := by
  simp only [Impl.StackScratch.AArch64.withStackScratchWiped, Impl.StackScratch.AArch64.withStackScratch,
    Impl.Sm4.AArch64.ctrFinal, Impl.Sm4.AArch64.ctrFinalTail, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem ctrFinal_own :
    calleeSide (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10
      (Impl.Sm4.AArch64.ctrFinal "" (.block []))) Impl.Sm4.AArch64.Fn.ctrFinalOwn = true := by
  kernel_rfl

theorem ctrFinal_side (v : Proof.Sm4.AArch64.CtrFinal.CtrImpl) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10
      (Impl.Sm4.AArch64.ctrFinal v.name v.code)) 3344 0
      (Impl.Sm4.AArch64.Fn.ctrFinalOwn.union v.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (ctrFinal_all v.name v.code (sideAll_union_left ctrFinal_own) (sideAll_union_right v.scrub))
    (by decide)
  simp only [Impl.StackScratch.AArch64.withStackScratchWiped, Impl.StackScratch.AArch64.withStackScratch,
    Impl.Sm4.AArch64.ctrFinal, Impl.Sm4.AArch64.ctrFinalTail, Code.aarch64Depth, Instr.frameUnits,
    Nat.zero_max, Nat.max_zero, Nat.max_self, Nat.reduceDiv, Nat.mul_add, Nat.reduceMul]
  exact Nat.add_le_add_right v.depth 80

theorem ctrFinal (v : Proof.Sm4.AArch64.CtrFinal.CtrImpl) :
    VerifiedScrubbed target (Impl.Sm4.AArch64.Fn.ctrFinal v.clear v.name v.code)
      (Spec.Sm4.ctrFinalContract abi 3344) 0 :=
  verifiedScrubbed (api := Spec.Sm4.ctrFinalApi)
    { code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 (Impl.Sm4.AArch64.ctrFinal v.name v.code)
      verified := Proof.Sm4.AArch64.CtrFinal.ctrFinal_framed v } _ ctrFinalOk (ctrFinal_side v)

end VG.Proof.Sm4.AArch64.CtrScrub

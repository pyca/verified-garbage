module

public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Blake2.Scratch

/-!
# BLAKE2's streaming `update` and `finalize` on AArch64, without secret residue

Their postconditions read the memory on return only within their buffers
(`Proof/Blake2/Scratch.lean`, which RISC-V and x86-64 use too): each returns
with every register it may leave secret cleared and its stack, the frame of
its scratch space and of its return address, zeroed
(`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Blake2

theorem updateBOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (updateBContract abi W) W (updateBSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateBSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Blake2.updateBPost_out 64)

theorem finalizeBOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (finalizeBContract abi W) W (finalizeBSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := finalizeBSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Blake2.finalizeBPost_out 64)

theorem updateSOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (updateSContract abi W) W (updateSSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateSSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Blake2.updateSPost_out 64)

theorem finalizeSOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (finalizeSContract abi W) W (finalizeSSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := finalizeSSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Blake2.finalizeSPost_out 64)

end VG.Proof.Blake2.AArch64.Scrub

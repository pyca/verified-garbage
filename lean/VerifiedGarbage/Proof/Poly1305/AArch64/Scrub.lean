module

public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Poly1305.Scratch

/-!
# Poly1305's streaming `update` and `finalize` on AArch64, without secret residue

Their postconditions read the memory on return only within their buffers
(`Proof/Poly1305/Scratch.lean`): each returns with every register it may
leave secret cleared and its 128 bytes of stack, the frame of its scratch
space, zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Poly1305

theorem updateOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (updateContract abi W) W (updateSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Poly1305.updatePostOut_local 64)

theorem finalizeOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (finalizeContract abi W) W (finalizeSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := finalizeSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Poly1305.finalizePostOut_local 64)

end VG.Proof.Poly1305.AArch64.Scrub

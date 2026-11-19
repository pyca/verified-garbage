module

public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Sha3.PostOut

/-!
# SHA-3's and SHAKE's absorbing on AArch64, without secret residue

The postcondition of `vg_sha3_*_update` and `vg_shake*_update` reads the
memory on return only within the state (`Proof.Sha3.PostOut.updatePost_out`):
each returns with every register it may leave secret cleared and its whole
stack window zeroed (`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Sha3

theorem absorbOk (rate W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (updateContract abi rate W) W (updateSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sha3.PostOut.updatePost_out rate 64)

end VG.Proof.Sha3.AArch64.Scrub

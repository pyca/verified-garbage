module

public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.ChaCha20.ScrubLocal

/-!
# ChaCha20's `apply` on AArch64, without secret residue

Its postcondition reads the memory on return only within the state and the
data (`ScrubLocal.applyPost_out`, which RISC-V uses too). It has no frame
(its stack is 0), so it returns with every register it may leave secret
cleared, over any implementation of the keystream it calls
(`ScrubAll.withScrubAll`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Stream.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.ChaCha20

theorem applyOk (W : Nat) :
    ScrubAllOk (applyContract abi W) W (applySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := applySig) (post := ScrubLocal.applyPost 64) (Nat.le_of_ble_eq_true rfl)
    (ScrubLocal.applyPost_out 64 rfl)

end VG.Proof.ChaCha20.AArch64.Stream.Scrub

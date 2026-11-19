module

public import VerifiedGarbage.Spec.ChaCha20.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Stream
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.ChaCha20.ScrubLocal

/-!
# ChaCha20's `apply` on AArch64, without secret residue

Its postcondition reads the memory on return only within the state and the
data (`ScrubLocal.applyPost_out`, which RISC-V uses too). It has no frame
(its stack is 0), so it returns with every register it may leave secret
cleared, over any implementation of the keystream it calls
(`ScrubAll.scrubAllOf`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Stream.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.ChaCha20

theorem applyOk (W : Nat) :
    ScrubAllOk (applyContract abi W) W (applySig.retBits abi.ptrBits) :=
  scrubAllOk_any (sig := applySig) (post := ScrubLocal.applyPost 64) (Nat.le_of_ble_eq_true rfl)
    (ScrubLocal.applyPost_out 64 rfl)

/-- The registers `vg_chacha20_apply` writes itself: its tail clears them
with those its backend writes (`XorImpl.clear`). -/
def applyOwn : Impl.Residue.AArch64.Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17], [], []⟩

/-- What `scrubAllOf` needs of `vg_chacha20_apply` with each backend:
evaluated here. -/
theorem applySide (v : Proof.ChaCha20.AArch64.XorImpl) (hv : v ∈ Proof.Variants.ChaCha20Xor.AArch64.variants) :
    scrubSide (Impl.ChaCha20.AArch64.Stream.apply v.callee) 0 (applySig.retBits abi.ptrBits)
      (clearUnion applyOwn v.clear) [] = true := by
  have e : (Proof.Variants.ChaCha20Xor.AArch64.variants.all fun v =>
      scrubSide (Impl.ChaCha20.AArch64.Stream.apply v.callee) 0 (applySig.retBits abi.ptrBits)
        (clearUnion applyOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.ChaCha20.AArch64.Stream.Scrub

module

public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
import VerifiedGarbage.Proof.Sha3.PostOut

/-!
# SHA-3's and SHAKE's functions on AArch64, without secret residue

The postconditions of `vg_sha3_*_update`, `vg_sha3_*_absorb`,
`vg_sha3_*_finalize`, `vg_shake*_finalize` and `vg_shake*_squeeze` read the
memory on return only within their buffers (`Proof.Sha3.PostOut`, which
x86-64's `Proof/Sha3/X86_64/Scrub.lean` uses too): each returns with every
register it may leave secret cleared and its stack zeroed
(`ScrubAll.withScrubAll`).

The functions that run on a working space in their frame (`absorb`,
`finalize`, and SHAKE's `squeeze`) zero all of it: the permutation, `pad`
and `squeeze` store bytes of the state through pointers into the buffers,
which the analysis of the window's bytes (`RTaintG`) cannot tell apart
from pointers into the frame, so that it finds no byte of the window the
same in both runs on return.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Sha3

theorem updateOk (rate W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (updateContract abi rate W) W (updateSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sha3.PostOut.updatePost_out rate 64)

theorem absorbOk (rate W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (absorbContract abi rate W) W (absorbSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := absorbSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sha3.PostOut.absorbPost_out rate 64)

theorem finalizeOk (H : HashFn) (W : Nat) (hlen : H.len < 2 ^ 64 := by decide)
    (hW : 0 < W := by decide) :
    ScrubAllOk (finalizeContract abi H W) W ((finalizeSig H.len).retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := finalizeSig H.len) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sha3.PostOut.finalizePost_out H 64 hlen)

theorem xofFinalizeOk (X : Xof) (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (xofFinalizeContract abi X W) W (xofFinalizeSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := xofFinalizeSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sha3.PostOut.xofFinalizePost_out X 64)

theorem xofSqueezeOk (X : Xof) (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (xofSqueezeContract abi X W) W (xofSqueezeSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := xofSqueezeSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sha3.PostOut.xofSqueezePost_out X)

end VG.Proof.Sha3.AArch64.Scrub

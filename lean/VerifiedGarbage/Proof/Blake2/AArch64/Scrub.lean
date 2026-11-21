module

public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Verified
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.CT
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
import VerifiedGarbage.Proof.Blake2.AArch64.Lit
import VerifiedGarbage.Proof.Blake2.Scratch

/-!
# BLAKE2's streaming functions on AArch64, without secret residue

The postconditions of `update` and `finalize` read the memory on return only
within their buffers (`Proof/Blake2/Scratch.lean`, which RISC-V and x86-64 use
too): each returns with every register it may leave secret cleared and its
stack, the frame of its scratch space and of its return address, zeroed
(`Impl.Blake2.AArch64.Fn`, whose theorems are at the end).
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub VG.Spec.Blake2

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

/-! ## The functions

The code that is emitted (`Impl.Blake2.AArch64.Fn`) meets each function's
contract in constant time and returns without secret residue. -/

namespace VG.Proof.Blake2.AArch64.Fn

open VG.AArch64 VG.AArch64.Scrub VG.Spec.Blake2

theorem initB :
    VerifiedScrubbed target (Impl.Blake2.AArch64.Fn.init b) (initBContract abi) 0 :=
  ⟨Stream.initBCleared_verified, Stream.initBCleared_noResidue _⟩

theorem updateB :
    VerifiedScrubbed target (Impl.Blake2.AArch64.Fn.update b) (updateBContract abi (16 + 112)) 0 :=
  verifiedScrubbedAll (api := updateBApi)
    { code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 (Impl.Blake2.AArch64.Stream.update b),
      verified := Stream.updateB_framed }
    _ (Scrub.updateBOk 128) (by dsimp only; lit_decide)

theorem finalizeB :
    VerifiedScrubbed target (Impl.Blake2.AArch64.Fn.finalize b) (finalizeBContract abi (16 + 112)) 0 :=
  verifiedScrubbedAll (api := finalizeBApi)
    { code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 (Impl.Blake2.AArch64.Stream.finalize b),
      verified := Stream.finalizeB_framed }
    _ (Scrub.finalizeBOk 128) (by dsimp only; lit_decide)

theorem initS :
    VerifiedScrubbed target (Impl.Blake2.AArch64.Fn.init s) (initSContract abi) 0 :=
  ⟨Stream.initSCleared_verified, Stream.initSCleared_noResidue _⟩

theorem updateS :
    VerifiedScrubbed target (Impl.Blake2.AArch64.Fn.update s) (updateSContract abi (16 + 112)) 0 :=
  verifiedScrubbedAll (api := updateSApi)
    { code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 (Impl.Blake2.AArch64.Stream.update s),
      verified := Stream.updateS_framed }
    _ (Scrub.updateSOk 128) (by dsimp only; lit_decide)

theorem finalizeS :
    VerifiedScrubbed target (Impl.Blake2.AArch64.Fn.finalize s) (finalizeSContract abi (16 + 112)) 0 :=
  verifiedScrubbedAll (api := finalizeSApi)
    { code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 (Impl.Blake2.AArch64.Stream.finalize s),
      verified := Stream.finalizeS_framed }
    _ (Scrub.finalizeSOk 128) (by dsimp only; lit_decide)

end VG.Proof.Blake2.AArch64.Fn

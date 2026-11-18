module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubAll
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut

/-!
# ChaCha20-Poly1305 on AArch64, without secret residue

The postconditions of `vg_chacha20_poly1305_seal`, `vg_chacha20_poly1305_open`,
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather` read
the memory on return only within their buffers (`Proof/ChaCha20Poly1305/Scratch.lean`,
`Proof/ChaCha20Poly1305/OpenToScratch.lean`, which RISC-V uses too; given
the precondition for `open_to`): each, over any implementation of ChaCha20's
keystream, returns with every register it may leave secret cleared and its
whole stack zeroed (`ScrubAll.withScrubAll`). Their code wipes only the first
768 bytes of its working space, and keeps keystream above them.

`seal_gather` calls `seal` as emitted, scrubbed whole (`sealFnScrub`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.ChaCha20Poly1305 VG.Impl.Residue.AArch64

theorem sealOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (sealContract abi W) W (sealSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := sealSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.ChaCha20Poly1305.sealPost_out 64)

theorem openOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (openZeroContract abi W) W (openSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := openSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.ChaCha20Poly1305.openZeroPost_out 64)

theorem openToOk (W : Nat) :
    ScrubAllOk (openToContract abi W) W (openToSig.retBits abi.ptrBits) :=
  scrubAllOk_args_pre_any (sig := openToSig) (Proof.ChaCha20Poly1305.openToPost_out 64)

theorem gatherOk (W : Nat) :
    ScrubAllOk (sealGatherContract abi W) W (sealGatherSig.retBits abi.ptrBits) :=
  scrubAllOk_args_any (sig := sealGatherSig) (Proof.ChaCha20Poly1305.sealGatherPost_out 64)

/-- `scrubAll` over the 1280 bytes of `seal`'s stack keeps its frames within them. -/
theorem depth_scrubAll {c : Prog isa} (cl : Clear) (rb : Nat) (h : 16 * c.aarch64Depth ≤ 1280) :
    16 * (scrubAll 1280 rb cl c).aarch64Depth ≤ 1280 := by
  suffices hd : (scrubAll 1280 rb cl c).aarch64Depth ≤ 80 by omega
  show Code.aarch64Depth (.seq (withRet rb (.seq c (.block (clearsOf cl))))
    (scrubTailG 1280 (List.range 80))) ≤ 80
  simp only [withRet, scrubTailG, Code.aarch64Depth, Instr.frameUnits, Nat.reduceDiv, Nat.zero_add,
    Nat.max_le, Nat.zero_le, Nat.le_refl, and_true]
  omega

/-- `vg_chacha20_poly1305_seal` over the backend `v`, scrubbed whole: what
`seal_gather` calls, the code of its registration (`withScrubAll`). -/
def sealFnScrub (v : Proof.ChaCha20.AArch64.XorImpl) : Proof.ChaCha20Poly1305.AArch64.Gather.SealFn where
  name := (sealFn v).name
  code := scrubAll 1280 (sealSig.retBits abi.ptrBits) (Clear.of (sealFn v).code) (sealFn v).code
  verified := Verified.scrubAll (Clear.of_wf _) (sealFn v).verified (by decide) (by decide) (sealOk 1280)
  depth := depth_scrubAll _ _ (sealFn v).depth

end VG.Proof.ChaCha20Poly1305.AArch64.Scrub

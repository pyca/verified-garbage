module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
import VerifiedGarbage.Proof.Framework.Lit
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
whole stack zeroed (`ScrubAll.scrubAllOf`). Their code wipes only the first
768 bytes of its working space, and keeps keystream above them.

`seal_gather` calls `seal`'s code as an internal function of its own,
`vg_chacha20_poly1305_seal_core` (`sealFnCore`), so that its stack is zeroed
once, by `seal_gather`'s scrubbing, as on RISC-V.
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

/-- `vg_chacha20_poly1305_seal` over the backend `v`, as the internal
function `vg_chacha20_poly1305_seal_core` (with `v`'s suffix) that
`seal_gather` calls: the exported one zeroes its stack, which `seal_gather`'s
own scrubbing zeroes again. -/
def sealFnCore (v : Proof.ChaCha20.AArch64.XorImpl) : Proof.ChaCha20Poly1305.AArch64.Gather.SealFn :=
  { sealFn v with name := "vg_chacha20_poly1305_seal_core" ++ v.callee.suffix }

/-! ## What the tails clear

Each function's tail clears the registers its own code writes with those its
backend writes (`XorImpl.clear`); `scrubAllOf` needs `scrubSide` of each,
evaluated here with each backend. -/

/-- The registers `seal` and `seal_gather` write themselves. -/
def sealOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
    .v27, .v30, .v31],
   []⟩

/-- The registers `open` and `open_to` write themselves. -/
def openOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
    .v27, .v28, .v29, .v30, .v31],
   [.v8, .v9]⟩

/-- Of `vg_chacha20_poly1305_seal`. -/
theorem sealSide (v : Proof.ChaCha20.AArch64.XorImpl) (hv : v ∈ Proof.Variants.ChaCha20Xor.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
        (Impl.ChaCha20Poly1305.AArch64.sealCode v.callee v.stitched)) 1280
      (sealSig.retBits abi.ptrBits) (clearUnion sealOwn v.clear) [] = true := by
  have e : (Proof.Variants.ChaCha20Xor.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 1280 .x7 96
        (Impl.ChaCha20Poly1305.AArch64.sealCode v.callee v.stitched)) 1280
        (sealSig.retBits abi.ptrBits) (clearUnion sealOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of `vg_chacha20_poly1305_open`. -/
theorem openSide (v : Proof.ChaCha20.AArch64.XorImpl) (hv : v ∈ Proof.Variants.ChaCha20Xor.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 1312 .x7 96
        (Impl.ChaCha20Poly1305.AArch64.openInPlace v.callee v.stitched)) 1312
      (openSig.retBits abi.ptrBits) (clearUnion openOwn v.clear) [] = true := by
  have e : (Proof.Variants.ChaCha20Xor.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackScratchWiped 1312 .x7 96
        (Impl.ChaCha20Poly1305.AArch64.openInPlace v.callee v.stitched)) 1312
        (openSig.retBits abi.ptrBits) (clearUnion openOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of `vg_chacha20_poly1305_open_to`. -/
theorem openToSide (v : Proof.ChaCha20.AArch64.XorImpl) (hv : v ∈ Proof.Variants.ChaCha20Xor.AArch64.variants) :
    scrubSide (Impl.StackScratch.AArch64.withStackArgScratchWiped 1328 1 96
        (Impl.ChaCha20Poly1305.AArch64.openTo v.callee v.stitched)) 1328
      (openToSig.retBits abi.ptrBits) (clearUnion openOwn v.clear) [] = true := by
  have e : (Proof.Variants.ChaCha20Xor.AArch64.variants.all fun v =>
      scrubSide (Impl.StackScratch.AArch64.withStackArgScratchWiped 1328 1 96
        (Impl.ChaCha20Poly1305.AArch64.openTo v.callee v.stitched)) 1328
        (openToSig.retBits abi.ptrBits) (clearUnion openOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

/-- Of `vg_chacha20_poly1305_seal_gather`. -/
theorem gatherSide (v : Proof.ChaCha20.AArch64.XorImpl) (hv : v ∈ Proof.Variants.ChaCha20Xor.AArch64.variants) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather (sealFnCore v).name (sealFnCore v).code) 1296
      (sealGatherSig.retBits abi.ptrBits) (clearUnion sealOwn v.clear) [] = true := by
  have e : (Proof.Variants.ChaCha20Xor.AArch64.variants.all fun v =>
      scrubSide (Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather (sealFnCore v).name (sealFnCore v).code) 1296
        (sealGatherSig.retBits abi.ptrBits) (clearUnion sealOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp e v hv

end VG.Proof.ChaCha20Poly1305.AArch64.Scrub

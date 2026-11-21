module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.ChaCha20Xor.AArch64
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.ChaCha20Poly1305.GatherOut

/-!
# ChaCha20-Poly1305 on AArch64, without secret residue

The postconditions of `vg_chacha20_poly1305_seal`, `vg_chacha20_poly1305_open`,
`vg_chacha20_poly1305_open_to` and `vg_chacha20_poly1305_seal_gather` read
the memory on return only within their buffers (`Proof/ChaCha20Poly1305/Scratch.lean`,
`Proof/ChaCha20Poly1305/OpenToScratch.lean`, which RISC-V uses too; given
the precondition for `open_to`): each as it is emitted
(`Impl.ChaCha20Poly1305.AArch64.Fn`), over any implementation of ChaCha20's
keystream, returns with every register it may leave secret cleared and its
whole stack zeroed (`Fn`, below). Their code wipes only the first
768 bytes of its working space, and keeps keystream above them.

`seal_gather` calls `seal`'s code as an internal function of its own,
`vg_chacha20_poly1305_seal_core` (`sealFnCore`), so that its stack is zeroed
once, by `seal_gather`'s scrubbing, as on RISC-V.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Scrub

open VG.AArch64 VG.AArch64.Scrub VG.Spec.ChaCha20Poly1305 VG.Impl.Scrub.AArch64

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

/-! ## What the cleanup needs of the code

Of `seal`, `open` and `open_to` in their frames with the stream `v`, it is
what `v` proves where it is defined (`XorImpl.sealSide`, `openSide`,
`openToSide`); of `seal_gather`, its own instructions' and `seal`'s. -/

theorem seal_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.sealBody v.callee v.stitched) 1280 0
      (Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn.union v.callee.clear) [] = true := by
  have h := v.sealSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact scrubSide_union (by decide) h.2 (by decide) h.1 (by decide)

theorem open_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.openBody v.callee v.stitched) 1312 32
      (Impl.ChaCha20Poly1305.AArch64.Fn.openOwn.union v.callee.clear) [] = true := by
  have h := v.openSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact scrubSide_union (by decide) h.2 (by decide) h.1 (by decide)

theorem openTo_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.openToBody v.callee v.stitched) 1328 32
      (Impl.ChaCha20Poly1305.AArch64.Fn.openOwn.union v.callee.clear) [] = true := by
  have h := v.openToSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact scrubSide_union (by decide) h.2 (by decide) h.1 (by decide)

/-- `seal_gather`'s own instructions, with nothing in `seal`'s place, write
only the registers `Impl/` states (`Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn`). -/
private theorem gather_own :
    calleeSide (Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather "" (.block []))
      Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn = true := by
  kernel_rfl

theorem gather_side (v : Proof.ChaCha20.AArch64.XorImpl) :
    scrubSide (Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody v.callee v.stitched) 1296 0
      (Impl.ChaCha20Poly1305.AArch64.Fn.sealOwn.union v.callee.clear) [] = true := by
  have h := v.sealSide
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  have h0 := sideAll_union_left (b := v.callee.clear) gather_own
  refine scrubSide_union (by decide) ?_ (by decide) ?_ (by decide)
  · have hg : Impl.AesGcm.AArch64.SealGather.gather.aarch64Depth = 0 := by decide
    simp only [Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody,
      Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather, Code.aarch64Depth, Instr.frameUnits, hg,
      Nat.zero_max, Nat.max_zero, Nat.reduceDiv]
    exact Nat.le_trans (Nat.mul_add 16 _ 1 ▸ Nat.add_le_add_right h.2 16) (by decide)
  · simp only [calleeSide, Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody,
      Impl.ChaCha20Poly1305.AArch64.SealGather.sealGather, sideAll, Bool.and_eq_true] at h0 h ⊢
    simp only [h0, h.1, and_self]

end VG.Proof.ChaCha20Poly1305.AArch64.Scrub

/-! ## The functions

Of each function `Artifacts/ChaCha20Poly1305/AArch64.lean` registers, with
the stream `v`: the code that is emitted (`Impl.ChaCha20Poly1305.AArch64.Fn`)
meets the function's contract in constant time and returns without secret
residue. -/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Fn

open VG.AArch64 VG.AArch64.Scrub VG.Spec.ChaCha20Poly1305

theorem sealWhole (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.sealWhole v.callee v.stitched)
      (sealContract abi 1280) 0 :=
  verifiedScrubbedAll (api := sealApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.sealBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.seal_framed v }
    _ (Scrub.sealOk 1280) (Scrub.seal_side v)

theorem openZero (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.openZero v.callee v.stitched)
      (openZeroContract abi 1312) 32 :=
  verifiedScrubbedAll (api := openZeroApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.openBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.open_framed v }
    _ (Scrub.openOk 1312) (Scrub.open_side v)

theorem openTo (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.openTo v.callee v.stitched)
      (openToContract abi 1328) 32 :=
  verifiedScrubbedAll (api := openToApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.openToBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.openTo_framed v }
    _ (Scrub.openToOk 1328) (Scrub.openTo_side v)

theorem sealGather (v : Proof.ChaCha20.AArch64.XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20Poly1305.AArch64.Fn.sealGather v.callee v.stitched)
      (sealGatherContract abi 1296) 0 :=
  verifiedScrubbedAll (api := sealGatherApi)
    { code := Impl.ChaCha20Poly1305.AArch64.Fn.sealGatherBody v.callee v.stitched,
      verified := Proof.ChaCha20Poly1305.AArch64.Gather.sealGather_verified (Scrub.sealFnCore v) }
    _ (Scrub.gatherOk 1296) (Scrub.gather_side v)

end VG.Proof.ChaCha20Poly1305.AArch64.Fn

module

import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Init
public import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Sm3.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm3.AArch64.Stream
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Sm3.PostOut
import VerifiedGarbage.Proof.Sm3.AArch64.Lit

/-!
# SM3 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/AArch64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize`, with any implementation of the compression function
(`Compress`), keep their working space (14 words: the compression
function's 64 bytes, then the registers the streaming code saves) in a frame
of their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).

`update_scrubbed` and `finalize_scrubbed` are about the functions as emitted,
with their cleanup (`Impl.Sm3.AArch64.Stream.Fn`): their postconditions read
the memory on return only within their buffers (`Proof/Sm3/PostOut.lean`), so
they return with the registers they may write cleared and their stack zeroed.
-/

@[expose] public section

namespace VG.Proof.Sm3.AArch64.Shared

open _root_.VG.AArch64

theorem init :
    Verified AArch64.target Impl.Sm3.AArch64.Stream.init (Spec.Sm3.initContract AArch64.abi) :=
  Proof.Sm3.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.initSat] using Proof.Sm3.AArch64.Stream.initSat)

theorem updateScratch (v : Compress) :
    Verified AArch64.target v.update (Proof.Sm3.updateScratchContract AArch64.abi 14 16) :=
  v.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.Update.sat,
        MdStream.AArch64.Update.sat, Impl.Sm3.AArch64.Stream.params] using Proof.Sm3.AArch64.Stream.Update.sat)

theorem finalizeScratch (v : Compress) :
    Verified AArch64.target v.finalize (Proof.Sm3.finalizeScratchContract AArch64.abi 14 16) :=
  v.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.Finalize.sat,
        MdStream.AArch64.Finalize.sat, Impl.Sm3.AArch64.Stream.params] using Proof.Sm3.AArch64.Stream.Finalize.sat)

theorem update (v : Compress) : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 v.update)
    (Spec.Sm3.updateContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 14)
    (stack := 16) (bytes := 112)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm3.updatePostOut_local _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize (v : Compress) : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 v.finalize)
    (Spec.Sm3.finalizeContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 14)
    (stack := 16) (bytes := 112)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch v) (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Sm3.finalizePostOut_local _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))


/-- `update`'s postcondition reads the memory on return only within its buffers. -/
theorem updateOk : AArch64.ScrubAll.ScrubAllOk (Spec.Sm3.updateContract AArch64.abi (16 + 112)) (16 + 112)
    (Spec.Sm3.updateSig.retBits AArch64.abi.ptrBits) :=
  AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sm3.updateSig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Sm3.updatePost_out _)

/-- `finalize`'s postcondition reads the memory on return only within its buffers. -/
theorem finalizeOk : AArch64.ScrubAll.ScrubAllOk (Spec.Sm3.finalizeContract AArch64.abi (16 + 112)) (16 + 112)
    (Spec.Sm3.finalizeSig.retBits AArch64.abi.ptrBits) :=
  AArch64.ScrubAll.scrubAllOk_regs (sig := Spec.Sm3.finalizeSig) (by decide) (by decide) (Nat.le_refl _)
    (Proof.Sm3.finalizePost_out _)

/-! ## The functions, as emitted

`vg_sm3_update` and `vg_sm3_finalize` over `v` with their cleanup
(`Impl.Sm3.AArch64.Stream.Fn`): each meets its contract in constant time and
returns without secret residue (`VerifiedScrubbed`), which is what its
registration binds. What the cleanup needs of the code
(`ScrubAll.scrubSide`) is proved of each function's own instructions here,
once, with code that does nothing in the place of the compression function,
and of each compression function where it is defined (`Compress.scrub`). -/

open VG.AArch64.ScrubAll

private theorem update_all {p : Instr → Bool} (name : String) (code : Prog isa)
    (h0 : sideAll p (Impl.StackScratch.AArch64.withStackScratch 112 .x4
      (Impl.MdStream.AArch64.update Impl.Sm3.AArch64.Stream.params "" (.block []))) = true)
    (hc : sideAll p code = true) :
    sideAll p (Impl.StackScratch.AArch64.withStackScratch 112 .x4
      (Impl.MdStream.AArch64.update Impl.Sm3.AArch64.Stream.params name code)) = true := by
  simp only [Impl.StackScratch.AArch64.withStackScratch, Impl.MdStream.AArch64.update,
    Impl.MdStream.AArch64.updateMain, Impl.MdStream.AArch64.updateBody, Impl.MdStream.AArch64.compressN,
    Impl.MdStream.AArch64.compressWith, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem finalize_all {p : Instr → Bool} (name : String) (code : Prog isa)
    (h0 : sideAll p (Impl.StackScratch.AArch64.withStackScratch 112 .x3
      (Impl.MdStream.AArch64.finalize Impl.Sm3.AArch64.Stream.params "" (.block []))) = true)
    (hc : sideAll p code = true) :
    sideAll p (Impl.StackScratch.AArch64.withStackScratch 112 .x3
      (Impl.MdStream.AArch64.finalize Impl.Sm3.AArch64.Stream.params name code)) = true := by
  simp only [Impl.StackScratch.AArch64.withStackScratch, Impl.MdStream.AArch64.finalize,
    Impl.MdStream.AArch64.finalizeMain, Impl.MdStream.AArch64.finalizeBody, Impl.MdStream.AArch64.compressAt,
    Impl.MdStream.AArch64.compressWith, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem update_own :
    calleeSide (Impl.StackScratch.AArch64.withStackScratch 112 .x4
      (Impl.MdStream.AArch64.update Impl.Sm3.AArch64.Stream.params "" (.block [])))
      Impl.Sm3.AArch64.Stream.Fn.updateOwn = true := by
  kernel_rfl

private theorem finalize_own :
    calleeSide (Impl.StackScratch.AArch64.withStackScratch 112 .x3
      (Impl.MdStream.AArch64.finalize Impl.Sm3.AArch64.Stream.params "" (.block [])))
      Impl.Sm3.AArch64.Stream.Fn.finalizeOwn = true := by
  kernel_rfl

theorem update_side (v : Compress) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 112 .x4 v.update) 128 0
      (Impl.Sm3.AArch64.Stream.Fn.updateOwn.union v.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (update_all v.name v.code (sideAll_union_left update_own) (sideAll_union_right v.scrub)) (by decide)
  simp only [Impl.StackScratch.AArch64.withStackScratch, Compress.update, Impl.MdStream.AArch64.update,
    Code.aarch64Depth, Instr.frameUnits, v.updateDepth]
  decide

theorem finalize_side (v : Compress) :
    scrubSide (Impl.StackScratch.AArch64.withStackScratch 112 .x3 v.finalize) 128 0
      (Impl.Sm3.AArch64.Stream.Fn.finalizeOwn.union v.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (finalize_all v.name v.code (sideAll_union_left finalize_own) (sideAll_union_right v.scrub)) (by decide)
  simp only [Impl.StackScratch.AArch64.withStackScratch, Compress.finalize, Impl.MdStream.AArch64.finalize,
    Code.aarch64Depth, Instr.frameUnits, v.finalizeDepth]
  decide

/-- `vg_sm3_update` over `v` as emitted, cleanup included. -/
theorem update_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sm3.AArch64.Stream.Fn.update v.impl)
      (Spec.Sm3.updateContract AArch64.abi (16 + 112)) 0 :=
  verifiedScrubbed (api := Spec.Sm3.updateApi)
    { suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch 112 .x4 v.update
      verified := update v } _ updateOk (update_side v)

/-- `vg_sm3_finalize` over `v` as emitted, cleanup included. -/
theorem finalize_scrubbed (v : Compress) :
    VerifiedScrubbed AArch64.target (Impl.Sm3.AArch64.Stream.Fn.finalize v.impl)
      (Spec.Sm3.finalizeContract AArch64.abi (16 + 112)) 0 :=
  verifiedScrubbed (api := Spec.Sm3.finalizeApi)
    { suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratch 112 .x3 v.finalize
      verified := finalize v } _ finalizeOk (finalize_side v)

end VG.Proof.Sm3.AArch64.Shared

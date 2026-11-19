module

public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Sha3.AArch64.Instances
public import VerifiedGarbage.Impl.Sha3.AArch64.Instances
import VerifiedGarbage.Proof.Sha3.PostOut
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# SHA-3's and SHAKE's functions on AArch64, as emitted

`vg_sha3_*_update`, `vg_shake*_update`, `vg_sha3_*_finalize`,
`vg_shake*_finalize` and `vg_shake*_squeeze` are the sponge's functions with
their cleanup (`Impl.Sha3.AArch64.Fn`): each returns with every register it
may leave secret cleared and its whole stack zeroed. `Fn` below has the
theorem of each, with every implementation of the permutation: it meets its
contract in constant time (`Proof.Sha3.AArch64.Instances`) and returns
without secret residue (`VerifiedScrubbed`), which is what its registration
binds.

Their postconditions read the memory on return only within their buffers
(`Proof.Sha3.PostOut`; the `…Ok` theorems). What the cleanup needs of the
code (`ScrubAll.scrubSide`) is proved of each function's own instructions
here, once, with a permutation that does nothing in its place (`stub`), and
of each implementation where it is defined (`Permutation.scrub`): no proof
here evaluates an implementation's code.

These functions run on a working space in their frame and zero all of it:
the permutation, `pad` and `squeeze` store bytes of the state through
pointers into the buffers, which the analysis of the window's bytes
(`RTaintG`) cannot tell apart from pointers into the frame, so that it finds
no byte of the window the same in both runs on return.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Sha3
open VG.Proof.Sha3.AArch64 (Permutation)

theorem absorbOk (rate W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (updateContract abi rate W) W (updateSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Sha3.PostOut.updatePost_out rate 64)

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

/-! ## What the cleanup needs of the code

Of each function with any permutation `c`, from the same of the function
with `stub` (its own instructions), of `c`'s code, and of `c`'s absorb if it
gives one. -/

/-- A permutation that does nothing: a function's code with it has the
function's own instructions only. -/
private def stub : Impl.Sha3.AArch64.Callee :=
  { name := "", code := .block [], suffix := "", clear := ⟨[], [], []⟩ }

private theorem absorb_all {p : Instr → Bool} (c : Impl.Sha3.AArch64.Callee) (rate : Nat)
    (h0 : sideAll p (Impl.Sha3.AArch64.Instances.absorb stub rate) = true) (hc : sideAll p c.code = true)
    (ho : ∀ code, c.absorbOverride = some code → sideAll p code = true) :
    sideAll p (Impl.Sha3.AArch64.Instances.absorb c rate) = true := by
  cases h : c.absorbOverride with
  | none =>
    simp only [Impl.Sha3.AArch64.Instances.absorb, Impl.Sha3.AArch64.Instances.update,
      Impl.StackScratch.AArch64.withStackScratch, Impl.Sha3.AArch64.Stream.absorbWith, stub, h,
      Impl.Sha3.AArch64.Stream.absorbGenericWith, Impl.Sha3.AArch64.Stream.absorbMainWith,
      Impl.Sha3.AArch64.Stream.absorbBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, sideAll,
      Bool.and_eq_true] at h0 ⊢
    simp only [h0, hc, and_self]
  | some code =>
    simp only [Impl.Sha3.AArch64.Instances.absorb, Impl.Sha3.AArch64.Instances.update,
      Impl.StackScratch.AArch64.withStackScratch, Impl.Sha3.AArch64.Stream.absorbWith, stub, h,
      Impl.Sha3.AArch64.Stream.absorbGenericWith, Impl.Sha3.AArch64.Stream.absorbMainWith,
      Impl.Sha3.AArch64.Stream.absorbBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, sideAll,
      Bool.and_eq_true] at h0 ⊢
    simp only [h0, ho code h, and_self]

private theorem finalize_all {p : Instr → Bool} (c : Impl.Sha3.AArch64.Callee) (rate len : Nat)
    (h0 : sideAll p (Impl.Sha3.AArch64.Instances.finalize stub rate len) = true) (hc : sideAll p c.code = true) :
    sideAll p (Impl.Sha3.AArch64.Instances.finalize c rate len) = true := by
  simp only [Impl.Sha3.AArch64.Instances.finalize, Impl.Sha3.AArch64.Instances.finBody,
    Impl.StackScratch.AArch64.withStackScratch, Impl.Sha3.AArch64.Stream.padWith,
    Impl.Sha3.AArch64.Stream.padMainWith, Impl.Sha3.AArch64.Stream.squeezeWith,
    Impl.Sha3.AArch64.Stream.squeezeMainWith, Impl.Sha3.AArch64.Stream.squeezeBodyWith,
    Impl.Sha3.AArch64.Stream.permuteAtWith, stub, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem xofFinalize_all {p : Instr → Bool} (c : Impl.Sha3.AArch64.Callee) (rate : Nat)
    (h0 : sideAll p (Impl.Sha3.AArch64.Instances.xofFinalize stub rate) = true) (hc : sideAll p c.code = true) :
    sideAll p (Impl.Sha3.AArch64.Instances.xofFinalize c rate) = true := by
  simp only [Impl.Sha3.AArch64.Instances.xofFinalize, Impl.StackScratch.AArch64.withStackScratch,
    Impl.Sha3.AArch64.Stream.padWith, Impl.Sha3.AArch64.Stream.padMainWith, stub, sideAll,
    Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem xofSqueeze_all {p : Instr → Bool} (c : Impl.Sha3.AArch64.Callee) (rate : Nat)
    (h0 : sideAll p (Impl.Sha3.AArch64.Instances.xofSqueeze stub rate) = true) (hc : sideAll p c.code = true) :
    sideAll p (Impl.Sha3.AArch64.Instances.xofSqueeze c rate) = true := by
  simp only [Impl.Sha3.AArch64.Instances.xofSqueeze, Impl.StackScratch.AArch64.withStackScratch,
    Impl.Sha3.AArch64.Stream.squeezeWith, Impl.Sha3.AArch64.Stream.squeezeMainWith,
    Impl.Sha3.AArch64.Stream.squeezeBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, stub,
    sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

/-! The functions' own instructions write only the registers `Impl/` states
(`Impl.Sha3.AArch64.Fn.updateOwn`, `Impl.Sha3.AArch64.Fn.finalizeOwn`, `Impl.Sha3.AArch64.Fn.xofFinalizeOwn`), at any rate. -/

private theorem absorb_own (rate : Nat) :
    calleeSide (Impl.Sha3.AArch64.Instances.absorb stub rate) Impl.Sha3.AArch64.Fn.updateOwn = true := by
  kernel_rfl

private theorem finalize_own (rate len : Nat) :
    calleeSide (Impl.Sha3.AArch64.Instances.finalize stub rate len) Impl.Sha3.AArch64.Fn.finalizeOwn = true := by
  kernel_rfl

private theorem xofFinalize_own (rate : Nat) :
    calleeSide (Impl.Sha3.AArch64.Instances.xofFinalize stub rate) Impl.Sha3.AArch64.Fn.xofFinalizeOwn = true := by
  kernel_rfl

private theorem xofSqueeze_own (rate : Nat) :
    calleeSide (Impl.Sha3.AArch64.Instances.xofSqueeze stub rate) Impl.Sha3.AArch64.Fn.finalizeOwn = true := by
  kernel_rfl

theorem update_side (v : Permutation) (rate : Nat) :
    scrubSide (Impl.Sha3.AArch64.Instances.absorb v.callee rate) 656 64
      (Impl.Sha3.AArch64.Fn.updateOwn.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (absorb_all v.callee rate (sideAll_union_left (absorb_own rate)) (sideAll_union_right v.scrub)
      v.absorbOverrideScrub) (by decide)
  simp only [Impl.Sha3.AArch64.Instances.absorb, Impl.Sha3.AArch64.Instances.update,
    Impl.StackScratch.AArch64.withStackScratch, Code.aarch64Depth, Instr.frameUnits,
    v.absorb_depth]
  decide

theorem finalize_side (v : Permutation) (rate len : Nat) :
    scrubSide (Impl.Sha3.AArch64.Instances.finalize v.callee rate len) 688 0
      (Impl.Sha3.AArch64.Fn.finalizeOwn.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (finalize_all v.callee rate len (sideAll_union_left (finalize_own rate len))
      (sideAll_union_right v.scrub)) (by decide)
  simp only [Impl.Sha3.AArch64.Instances.finalize, Impl.Sha3.AArch64.Instances.finBody,
    Impl.StackScratch.AArch64.withStackScratch, Code.aarch64Depth, Instr.frameUnits, v.pad_depth,
    v.squeeze_depth]
  decide

theorem xofFinalize_side (v : Permutation) (rate : Nat) :
    scrubSide (Impl.Sha3.AArch64.Instances.xofFinalize v.callee rate) 656 0
      (Impl.Sha3.AArch64.Fn.xofFinalizeOwn.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (xofFinalize_all v.callee rate (sideAll_union_left (xofFinalize_own rate))
      (sideAll_union_right v.scrub)) (by decide)
  simp only [Impl.Sha3.AArch64.Instances.xofFinalize, Impl.StackScratch.AArch64.withStackScratch,
    Code.aarch64Depth, Instr.frameUnits, v.pad_depth]
  decide

theorem xofSqueeze_side (v : Permutation) (rate : Nat) :
    scrubSide (Impl.Sha3.AArch64.Instances.xofSqueeze v.callee rate) 656 64
      (Impl.Sha3.AArch64.Fn.finalizeOwn.union v.callee.clear) [] = true := by
  refine scrubSide_union (by decide) ?_ (by decide)
    (xofSqueeze_all v.callee rate (sideAll_union_left (xofSqueeze_own rate))
      (sideAll_union_right v.scrub)) (by decide)
  simp only [Impl.Sha3.AArch64.Instances.xofSqueeze, Impl.StackScratch.AArch64.withStackScratch,
    Code.aarch64Depth, Instr.frameUnits, v.squeeze_depth]
  decide

end VG.Proof.Sha3.AArch64.Scrub

/-! ## The functions

Of each function `Artifacts/Sha3/AArch64.lean` registers, with the
implementation `v` of the permutation: the code that is emitted
(`Impl.Sha3.AArch64.Fn`) meets the function's contract in constant time and
returns without secret residue. -/

namespace VG.Proof.Sha3.AArch64.Fn

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Sha3
open VG.Proof.Sha3.AArch64 (Permutation)

theorem update_sha3_224 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.update v.callee hashSha3_224.rate)
      (updateContract abi hashSha3_224.rate 656) 64 :=
  verifiedScrubbed (api := updateSha3_224Api)
    { code := Impl.Sha3.AArch64.Instances.absorb v.callee hashSha3_224.rate,
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_224 v }
    _ (Scrub.absorbOk _ 656) (Scrub.update_side v _)

theorem finalize_sha3_224 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.finalize v.callee hashSha3_224.rate hashSha3_224.len)
      (finalizeContract abi hashSha3_224 (16 + 672)) 0 :=
  verifiedScrubbed (api := finalizeSha3_224Api)
    { code := Impl.Sha3.AArch64.Instances.finalize v.callee hashSha3_224.rate hashSha3_224.len,
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_224 v }
    _ (Scrub.finalizeOk hashSha3_224 (16 + 672)) (Scrub.finalize_side v _ _)

theorem update_sha3_256 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.update v.callee hashSha3_256.rate)
      (updateContract abi hashSha3_256.rate 656) 64 :=
  verifiedScrubbed (api := updateSha3_256Api)
    { code := Impl.Sha3.AArch64.Instances.absorb v.callee hashSha3_256.rate,
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_256 v }
    _ (Scrub.absorbOk _ 656) (Scrub.update_side v _)

theorem finalize_sha3_256 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.finalize v.callee hashSha3_256.rate hashSha3_256.len)
      (finalizeContract abi hashSha3_256 (16 + 672)) 0 :=
  verifiedScrubbed (api := finalizeSha3_256Api)
    { code := Impl.Sha3.AArch64.Instances.finalize v.callee hashSha3_256.rate hashSha3_256.len,
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_256 v }
    _ (Scrub.finalizeOk hashSha3_256 (16 + 672)) (Scrub.finalize_side v _ _)

theorem update_sha3_384 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.update v.callee hashSha3_384.rate)
      (updateContract abi hashSha3_384.rate 656) 64 :=
  verifiedScrubbed (api := updateSha3_384Api)
    { code := Impl.Sha3.AArch64.Instances.absorb v.callee hashSha3_384.rate,
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_384 v }
    _ (Scrub.absorbOk _ 656) (Scrub.update_side v _)

theorem finalize_sha3_384 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.finalize v.callee hashSha3_384.rate hashSha3_384.len)
      (finalizeContract abi hashSha3_384 (16 + 672)) 0 :=
  verifiedScrubbed (api := finalizeSha3_384Api)
    { code := Impl.Sha3.AArch64.Instances.finalize v.callee hashSha3_384.rate hashSha3_384.len,
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_384 v }
    _ (Scrub.finalizeOk hashSha3_384 (16 + 672)) (Scrub.finalize_side v _ _)

theorem update_sha3_512 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.update v.callee hashSha3_512.rate)
      (updateContract abi hashSha3_512.rate 656) 64 :=
  verifiedScrubbed (api := updateSha3_512Api)
    { code := Impl.Sha3.AArch64.Instances.absorb v.callee hashSha3_512.rate,
      verified := Proof.Sha3.AArch64.Instances.absorb_sha3_512 v }
    _ (Scrub.absorbOk _ 656) (Scrub.update_side v _)

theorem finalize_sha3_512 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.finalize v.callee hashSha3_512.rate hashSha3_512.len)
      (finalizeContract abi hashSha3_512 (16 + 672)) 0 :=
  verifiedScrubbed (api := finalizeSha3_512Api)
    { code := Impl.Sha3.AArch64.Instances.finalize v.callee hashSha3_512.rate hashSha3_512.len,
      verified := Proof.Sha3.AArch64.Instances.finalize_sha3_512 v }
    _ (Scrub.finalizeOk hashSha3_512 (16 + 672)) (Scrub.finalize_side v _ _)

theorem update_shake128 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.update v.callee xofShake128.rate)
      (updateContract abi xofShake128.rate 656) 64 :=
  verifiedScrubbed (api := updateShake128Api)
    { code := Impl.Sha3.AArch64.Instances.absorb v.callee xofShake128.rate,
      verified := Proof.Sha3.AArch64.Instances.absorb_shake128 v }
    _ (Scrub.absorbOk _ 656) (Scrub.update_side v _)

theorem finalize_shake128 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.xofFinalize v.callee xofShake128.rate)
      (xofFinalizeContract abi xofShake128 (16 + 640)) 0 :=
  verifiedScrubbed (api := finalizeShake128Api)
    { code := Impl.Sha3.AArch64.Instances.xofFinalize v.callee xofShake128.rate,
      verified := Proof.Sha3.AArch64.Instances.finalize_shake128 v }
    _ (Scrub.xofFinalizeOk xofShake128 (16 + 640)) (Scrub.xofFinalize_side v _)

theorem squeeze_shake128 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.xofSqueeze v.callee xofShake128.rate)
      (xofSqueezeContract abi xofShake128 (16 + 640)) 64 :=
  verifiedScrubbed (api := squeezeShake128Api)
    { code := Impl.Sha3.AArch64.Instances.xofSqueeze v.callee xofShake128.rate,
      verified := Proof.Sha3.AArch64.Instances.squeeze_shake128 v }
    _ (Scrub.xofSqueezeOk xofShake128 (16 + 640)) (Scrub.xofSqueeze_side v _)

theorem finalize_shake256 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.xofFinalize v.callee xofShake256.rate)
      (xofFinalizeContract abi xofShake256 (16 + 640)) 0 :=
  verifiedScrubbed (api := finalizeShake256Api)
    { code := Impl.Sha3.AArch64.Instances.xofFinalize v.callee xofShake256.rate,
      verified := Proof.Sha3.AArch64.Instances.finalize_shake256 v }
    _ (Scrub.xofFinalizeOk xofShake256 (16 + 640)) (Scrub.xofFinalize_side v _)

theorem squeeze_shake256 (v : Permutation) :
    VerifiedScrubbed target (Impl.Sha3.AArch64.Fn.xofSqueeze v.callee xofShake256.rate)
      (xofSqueezeContract abi xofShake256 (16 + 640)) 64 :=
  verifiedScrubbed (api := squeezeShake256Api)
    { code := Impl.Sha3.AArch64.Instances.xofSqueeze v.callee xofShake256.rate,
      verified := Proof.Sha3.AArch64.Instances.squeeze_shake256 v }
    _ (Scrub.xofSqueezeOk xofShake256 (16 + 640)) (Scrub.xofSqueeze_side v _)

end VG.Proof.Sha3.AArch64.Fn

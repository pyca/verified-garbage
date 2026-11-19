module

public import VerifiedGarbage.Spec.Sha3.Instances
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64
public import VerifiedGarbage.Impl.Sha3.AArch64.Instances
import VerifiedGarbage.Proof.Sha3.PostOut

/-!
# SHA-3's and SHAKE's functions on AArch64, without secret residue

The postconditions of `vg_sha3_*_update`, `vg_shake*_update`, `vg_sha3_*_finalize`,
`vg_shake*_finalize` and `vg_shake*_squeeze` read the memory on return only
within their buffers (`Proof.Sha3.PostOut`): each returns with every register
it may leave secret cleared and its whole stack window zeroed
(`ScrubAll.scrubAllOf`, with the `…Own` registers and `…Side` theorems
below).

These functions run on a working space in their frame and zero all of it:
the permutation, `pad` and `squeeze` store bytes of the state through
pointers into the buffers, which the analysis of the window's bytes
(`RTaintG`) cannot tell apart from pointers into the frame, so that it finds
no byte of the window the same in both runs on return.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Sha3

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

/-! What `scrubAllOf` needs of each function with each implementation of the
permutation: the registers its tail clears are those the function writes
with every implementation (`absorbOwn`, `finalizeOwn`, `xofFinalizeOwn`) and
those the implementation states its permutation writes (`Permutation.clear`),
and `scrubSide` of that is evaluated here, once for every instance
registered. -/

open VG.Impl.Residue.AArch64 (Clear)
open VG.Proof.Sha3.AArch64 (Permutation)

/-- The registers `absorb` writes with every implementation of the permutation. -/
def absorbOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x9, .x10, .x11, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v24, .v25, .v30,
   .v31],
   []⟩

/-- Those `finalize` and `xofSqueeze` write. -/
def finalizeOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v24, .v25, .v30, .v31],
   []⟩

/-- Those `xofFinalize` writes. -/
def xofFinalizeOwn : Clear :=
  ⟨[.x1, .x2, .x3, .x4, .x9, .x10, .x11, .x16, .x17],
   [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v24, .v25, .v30, .v31],
   []⟩

/-- Of `absorb` at each rate. -/
theorem absorbSide {rate : Nat} (v : Permutation) (hv : v ∈ Proof.Variants.Keccak.AArch64.variants)
    (h : rate ∈ [hashSha3_224.rate, hashSha3_256.rate, hashSha3_384.rate, hashSha3_512.rate, xofShake128.rate] := by decide) :
    scrubSide (Impl.Sha3.AArch64.Instances.absorb v.callee rate) 656 (updateSig.retBits abi.ptrBits)
      (clearUnion absorbOwn v.clear) [] = true := by
  have e : ([hashSha3_224.rate, hashSha3_256.rate, hashSha3_384.rate, hashSha3_512.rate, xofShake128.rate].all fun rate => Proof.Variants.Keccak.AArch64.variants.all fun v =>
      scrubSide (Impl.Sha3.AArch64.Instances.absorb v.callee rate) 656 (updateSig.retBits abi.ptrBits)
        (clearUnion absorbOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp (List.all_eq_true.mp e _ h) v hv

/-- Of `finalize` for each hash function, by its rate and its length. -/
theorem finalizeSide {rate len : Nat} (v : Permutation) (hv : v ∈ Proof.Variants.Keccak.AArch64.variants)
    (h : (rate, len) ∈ [(hashSha3_224.rate, hashSha3_224.len), (hashSha3_256.rate, hashSha3_256.len),
      (hashSha3_384.rate, hashSha3_384.len), (hashSha3_512.rate, hashSha3_512.len)] := by decide) :
    scrubSide (Impl.Sha3.AArch64.Instances.finalize v.callee rate len) (16 + 672) ((finalizeSig len).retBits abi.ptrBits)
      (clearUnion finalizeOwn v.clear) [] = true := by
  have e : ([(hashSha3_224.rate, hashSha3_224.len), (hashSha3_256.rate, hashSha3_256.len),
      (hashSha3_384.rate, hashSha3_384.len), (hashSha3_512.rate, hashSha3_512.len)].all fun rl => Proof.Variants.Keccak.AArch64.variants.all fun v =>
      scrubSide (Impl.Sha3.AArch64.Instances.finalize v.callee rl.1 rl.2) (16 + 672) ((finalizeSig rl.2).retBits abi.ptrBits)
        (clearUnion finalizeOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp (List.all_eq_true.mp e _ h) v hv

/-- Of `xofFinalize` at each rate. -/
theorem xofFinalizeSide {rate : Nat} (v : Permutation) (hv : v ∈ Proof.Variants.Keccak.AArch64.variants)
    (h : rate ∈ [xofShake128.rate, xofShake256.rate] := by decide) :
    scrubSide (Impl.Sha3.AArch64.Instances.xofFinalize v.callee rate) (16 + 640) (xofFinalizeSig.retBits abi.ptrBits)
      (clearUnion xofFinalizeOwn v.clear) [] = true := by
  have e : ([xofShake128.rate, xofShake256.rate].all fun rate => Proof.Variants.Keccak.AArch64.variants.all fun v =>
      scrubSide (Impl.Sha3.AArch64.Instances.xofFinalize v.callee rate) (16 + 640) (xofFinalizeSig.retBits abi.ptrBits)
        (clearUnion xofFinalizeOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp (List.all_eq_true.mp e _ h) v hv

/-- Of `xofSqueeze` at each rate. -/
theorem xofSqueezeSide {rate : Nat} (v : Permutation) (hv : v ∈ Proof.Variants.Keccak.AArch64.variants)
    (h : rate ∈ [xofShake128.rate, xofShake256.rate] := by decide) :
    scrubSide (Impl.Sha3.AArch64.Instances.xofSqueeze v.callee rate) (16 + 640) (xofSqueezeSig.retBits abi.ptrBits)
      (clearUnion finalizeOwn v.clear) [] = true := by
  have e : ([xofShake128.rate, xofShake256.rate].all fun rate => Proof.Variants.Keccak.AArch64.variants.all fun v =>
      scrubSide (Impl.Sha3.AArch64.Instances.xofSqueeze v.callee rate) (16 + 640) (xofSqueezeSig.retBits abi.ptrBits)
        (clearUnion finalizeOwn v.clear) []) = true := by lit_decide
  exact List.all_eq_true.mp (List.all_eq_true.mp e _ h) v hv

end VG.Proof.Sha3.AArch64.Scrub

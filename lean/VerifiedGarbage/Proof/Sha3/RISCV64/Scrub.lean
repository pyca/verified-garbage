module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.RISCV64.Instances
public import VerifiedGarbage.Proof.Sha3.PostOut

/-!
# SHA-3 and SHAKE on RISC-V, without secret residue

Each instance's `update` and `finalize`, and SHAKE's `squeeze`, followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`), which clears the
caller-saved registers and the stack its frames used. Their postconditions
read the memory on return only within their buffers
(`Proof/Sha3/PostOut.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG.RISCV64 VG.RISCV64.Scrub

theorem updateOut (rate stack : Nat) :
    PostOut (Spec.Sha3.updateContract RISCV64.abi rate stack) (Spec.Sha3.updateSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.updatePost_out rate 64)

theorem finalizeOut (H : Spec.Sha3.HashFn) (stack : Nat) (hlen : H.len < 2 ^ 64) :
    PostOut (Spec.Sha3.finalizeContract RISCV64.abi H stack) ((Spec.Sha3.finalizeSig H.len).retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.finalizePost_out H 64 hlen)

theorem xofFinalizeOut (X : Spec.Sha3.Xof) (stack : Nat) :
    PostOut (Spec.Sha3.xofFinalizeContract RISCV64.abi X stack) (Spec.Sha3.xofFinalizeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofFinalizePost_out X 64)

theorem xofSqueezeOut (X : Spec.Sha3.Xof) (stack : Nat) :
    PostOut (Spec.Sha3.xofSqueezeContract RISCV64.abi X stack) (Spec.Sha3.xofSqueezeSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.PostOut.xofSqueezePost_out X)

/-- `vg_sha3_224_update`. -/
def updateSha3_224Reg : Registration Spec.Sha3.updateSha3_224Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_224.rate, verified := Proof.Sha3.RISCV64.Instances.update_sha3_224 }
    (updateOut Spec.Sha3.hashSha3_224.rate _)

/-- `vg_sha3_224_finalize`. -/
def finalizeSha3_224Reg : Registration Spec.Sha3.finalizeSha3_224Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_224 }
    (finalizeOut Spec.Sha3.hashSha3_224 _ (by decide))

/-- `vg_sha3_256_update`. -/
def updateSha3_256Reg : Registration Spec.Sha3.updateSha3_256Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_256.rate, verified := Proof.Sha3.RISCV64.Instances.update_sha3_256 }
    (updateOut Spec.Sha3.hashSha3_256.rate _)

/-- `vg_sha3_256_finalize`. -/
def finalizeSha3_256Reg : Registration Spec.Sha3.finalizeSha3_256Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_256 }
    (finalizeOut Spec.Sha3.hashSha3_256 _ (by decide))

/-- `vg_sha3_384_update`. -/
def updateSha3_384Reg : Registration Spec.Sha3.updateSha3_384Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_384.rate, verified := Proof.Sha3.RISCV64.Instances.update_sha3_384 }
    (updateOut Spec.Sha3.hashSha3_384.rate _)

/-- `vg_sha3_384_finalize`. -/
def finalizeSha3_384Reg : Registration Spec.Sha3.finalizeSha3_384Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_384 }
    (finalizeOut Spec.Sha3.hashSha3_384 _ (by decide))

/-- `vg_sha3_512_update`. -/
def updateSha3_512Reg : Registration Spec.Sha3.updateSha3_512Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.hashSha3_512.rate, verified := Proof.Sha3.RISCV64.Instances.update_sha3_512 }
    (updateOut Spec.Sha3.hashSha3_512.rate _)

/-- `vg_sha3_512_finalize`. -/
def finalizeSha3_512Reg : Registration Spec.Sha3.finalizeSha3_512Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len, verified := Proof.Sha3.RISCV64.Instances.finalize_sha3_512 }
    (finalizeOut Spec.Sha3.hashSha3_512 _ (by decide))

/-- `vg_shake128_update`. -/
def updateShake128Reg : Registration Spec.Sha3.updateShake128Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.update Spec.Sha3.xofShake128.rate, verified := Proof.Sha3.RISCV64.Instances.update_shake128 }
    (updateOut Spec.Sha3.xofShake128.rate _)

/-- `vg_shake128_finalize`. -/
def finalizeShake128Reg : Registration Spec.Sha3.finalizeShake128Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake128.rate, verified := Proof.Sha3.RISCV64.Instances.finalize_shake128 }
    (xofFinalizeOut Spec.Sha3.xofShake128 _)

/-- `vg_shake128_squeeze`. -/
def squeezeShake128Reg : Registration Spec.Sha3.squeezeShake128Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake128.rate, verified := Proof.Sha3.RISCV64.Instances.squeeze_shake128 }
    (xofSqueezeOut Spec.Sha3.xofShake128 _)

/-- `vg_shake256_finalize`. -/
def finalizeShake256Reg : Registration Spec.Sha3.finalizeShake256Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.xofFinalize Spec.Sha3.xofShake256.rate, verified := Proof.Sha3.RISCV64.Instances.finalize_shake256 }
    (xofFinalizeOut Spec.Sha3.xofShake256 _)

/-- `vg_shake256_squeeze`. -/
def squeezeShake256Reg : Registration Spec.Sha3.squeezeShake256Api RISCV64.target :=
  withScrub { code := Impl.Sha3.RISCV64.Instances.xofSqueeze Spec.Sha3.xofShake256.rate, verified := Proof.Sha3.RISCV64.Instances.squeeze_shake256 }
    (xofSqueezeOut Spec.Sha3.xofShake256 _)

end VG.Proof.Sha3.RISCV64

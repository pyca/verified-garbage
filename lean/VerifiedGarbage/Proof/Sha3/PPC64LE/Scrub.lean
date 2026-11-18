module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Instances
public import VerifiedGarbage.Proof.Sha3.Instances
public import VerifiedGarbage.Proof.Sha3.PostOut

/-!
# SHA-3 and SHAKE on PPC64LE, without secret residue

Each instance's `update` and `finalize`, and SHAKE's `squeeze`, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.withScrub`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers: the state, through
`stateAt` (`Proof/Sha3/PostOut.lean`, `Proof/Sha3/Instances.lean`), and the
output. HMAC-free: SHA-3's callers (ML-KEM, ML-DSA, Ed448) call their own
internal copies of the code, not these.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub

def updateSha3_224Reg : Registration Spec.Sha3.updateSha3_224Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_224.rate
      verified := Proof.Sha3.PPC64LE.Instances.update_sha3_224 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.updatePostOut_local Spec.Sha3.hashSha3_224.rate 64))

def finalizeSha3_224Reg : Registration Spec.Sha3.finalizeSha3_224Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_224.rate Spec.Sha3.hashSha3_224.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_224 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_224))

def updateSha3_256Reg : Registration Spec.Sha3.updateSha3_256Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_256.rate
      verified := Proof.Sha3.PPC64LE.Instances.update_sha3_256 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.updatePostOut_local Spec.Sha3.hashSha3_256.rate 64))

def finalizeSha3_256Reg : Registration Spec.Sha3.finalizeSha3_256Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_256.rate Spec.Sha3.hashSha3_256.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_256 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_256))

def updateSha3_384Reg : Registration Spec.Sha3.updateSha3_384Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_384.rate
      verified := Proof.Sha3.PPC64LE.Instances.update_sha3_384 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.updatePostOut_local Spec.Sha3.hashSha3_384.rate 64))

def finalizeSha3_384Reg : Registration Spec.Sha3.finalizeSha3_384Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_384.rate Spec.Sha3.hashSha3_384.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_384 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_384))

def updateSha3_512Reg : Registration Spec.Sha3.updateSha3_512Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.hashSha3_512.rate
      verified := Proof.Sha3.PPC64LE.Instances.update_sha3_512 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.updatePostOut_local Spec.Sha3.hashSha3_512.rate 64))

def finalizeSha3_512Reg : Registration Spec.Sha3.finalizeSha3_512Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.finalize Spec.Sha3.hashSha3_512.rate Spec.Sha3.hashSha3_512.len
      verified := Proof.Sha3.PPC64LE.Instances.finalize_sha3_512 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.finalizePostOut_local 64 Spec.Sha3.hashSha3_512))

def updateShake128Reg : Registration Spec.Sha3.updateShake128Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.update Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.PPC64LE.Instances.update_shake128 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.updatePostOut_local Spec.Sha3.xofShake128.rate 64))

def finalizeShake128Reg : Registration Spec.Sha3.finalizeShake128Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.xofFinalize Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.PPC64LE.Instances.finalize_shake128 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofFinalizePostOut_local 64 Spec.Sha3.xofShake128))

def squeezeShake128Reg : Registration Spec.Sha3.squeezeShake128Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.xofSqueeze Spec.Sha3.xofShake128.rate
      verified := Proof.Sha3.PPC64LE.Instances.squeeze_shake128 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofSqueezePostOut_local 64 Spec.Sha3.xofShake128))

def finalizeShake256Reg : Registration Spec.Sha3.finalizeShake256Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.xofFinalize Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.PPC64LE.Instances.finalize_shake256 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofFinalizePostOut_local 64 Spec.Sha3.xofShake256))

def squeezeShake256Reg : Registration Spec.Sha3.squeezeShake256Api PPC64LE.target :=
  withScrub {
      code := Impl.Sha3.PPC64LE.Instances.xofSqueeze Spec.Sha3.xofShake256.rate
      verified := Proof.Sha3.PPC64LE.Instances.squeeze_shake256 }
    (by exact postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha3.Instances.xofSqueezePostOut_local 64 Spec.Sha3.xofShake256))

end VG.Proof.Sha3.PPC64LE.Scrub

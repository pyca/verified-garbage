module

public import VerifiedGarbage.Proof.Sha512.X86.Shared
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Impl.Sha512.X86.Stream
public import VerifiedGarbage.Impl.Sha512.X86.Digest
import VerifiedGarbage.Proof.Sha512.PostOut
import VerifiedGarbage.Proof.Sha512.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha512.X86.Shared
meta import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sha512.Contract
meta import VerifiedGarbage.Impl.Sha512.X86.Stream
meta import VerifiedGarbage.Impl.Sha512.X86.Digest
meta import VerifiedGarbage.Proof.Sha512.PostOut
meta import VerifiedGarbage.Proof.Sha512.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# The SHA-512 family's functions on x86 (32-bit), without secret residue

The functions as emitted (`Impl.Sha512.X86.Fn`): the `init`s of SHA-384,
SHA-512, SHA-512/224 and SHA-512/256, which call nothing and have no frame,
followed by the clearing of the registers a callee may change
(`X86.Scrub.verifiedScrubbed`); `update`, the `finalize`s and the one-shot
digests, whose working space is in a frame of their own, with the stack they
and their callees use zeroed first (`X86.Scrub.verifiedScrubbedF`), given that their
postconditions read the memory on return only within the buffers
(`Proof.Sha512.PostOut`). HMAC, PBKDF2, the digests and Ed25519 call the
`init`s' code as the internal `vg_<hash>_init_core`
(`Proof.Pbkdf2.Stream.X86.sha512H`), and Ed25519 the digest's as
`vg_sha512_digest_core`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86.Scrub

open VG.Spec.Sha512 VG.X86 VG.X86.Scrub
open VG.Impl.MdStream.X86.Digest (digest dframe)

theorem updateOut (stack : Nat) : PostOut (updateContract X86.abi stack) (updateSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha512.updatePost_out 32)

theorem finalizeOut (stack : Nat) : PostOut (finalizeContract X86.abi stack) (finalizeSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha512.finalizePost_out 32)

theorem finalizeDigestOut (iv : HashValue) (D : Nat) (dg : List Byte → List Byte) (hD : D < 2 ^ 64)
    (stack : Nat) :
    PostOut (finalizeDigestContract X86.abi iv D dg stack) ((finalizeDigestSig D).retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha512.finalizeDigestPost_out iv D dg 32 hD)

theorem digestOut (D : Nat) (dg : List Byte → List Byte) (hD : D < 2 ^ 64) (stack : Nat) :
    PostOut (digestContract X86.abi D dg stack) ((digestSig D).retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha512.digestPost_out D dg 32 hD)

/-! ## `init` -/

/-- `vg_sha384_init` as emitted (`Impl.Sha512.X86.Fn.init`) meets its contract in constant time
and returns without secret residue. -/
theorem init384_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.init H0_384) (initContract X86.abi H0_384) 0 :=
  verifiedScrubbed (api := init384Api)
    { code := Impl.Sha512.X86.Stream.init H0_384, verified := Shared.init H0_384 }

/-- `vg_sha512_init` as emitted (`Impl.Sha512.X86.Fn.init`) meets its contract in constant time
and returns without secret residue. -/
theorem init512_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.init H0_512) (initContract X86.abi H0_512) 0 :=
  verifiedScrubbed (api := init512Api)
    { code := Impl.Sha512.X86.Stream.init H0_512, verified := Shared.init H0_512 }

/-- `vg_sha512_224_init` as emitted (`Impl.Sha512.X86.Fn.init`) meets its contract in constant time
and returns without secret residue. -/
theorem init512_224_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.init H0_512_224) (initContract X86.abi H0_512_224) 0 :=
  verifiedScrubbed (api := init512_224Api)
    { code := Impl.Sha512.X86.Stream.init H0_512_224, verified := Shared.init H0_512_224 }

/-- `vg_sha512_256_init` as emitted (`Impl.Sha512.X86.Fn.init`) meets its contract in constant time
and returns without secret residue. -/
theorem init512_256_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.init H0_512_256) (initContract X86.abi H0_512_256) 0 :=
  verifiedScrubbed (api := init512_256Api)
    { code := Impl.Sha512.X86.Stream.init H0_512_256, verified := Shared.init H0_512_256 }

/-! ## `update` and `finalize` -/

/-- `vg_sha512_update` as emitted (`Impl.Sha512.X86.Fn.update`) meets its contract in constant
time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed target Impl.Sha512.X86.Fn.update (updateContract X86.abi (20 + 1404)) 0 :=
  verifiedScrubbedF (api := updateApi)
    { code := Impl.StackScratch.X86.withStackScratch 1404 5 Impl.Sha512.X86.Stream.update
      stack := 20 + 1404
      verified := Shared.update }
    (updateOut _)

/-- `vg_sha512_finalize` as emitted (`Impl.Sha512.X86.Fn.finalize`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed target Impl.Sha512.X86.Fn.finalize (finalizeContract X86.abi (20 + 1400)) 0 :=
  verifiedScrubbedF (api := finalizeApi)
    { code := Impl.StackScratch.X86.withStackScratch 1400 4 Impl.Sha512.X86.Stream.finalize
      stack := 20 + 1400
      verified := Shared.finalize }
    (finalizeOut _)

/-- `vg_sha384_finalize` as emitted (`Impl.Sha512.X86.Fn.finalizeDigest`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize384_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.finalizeDigest Impl.Sha512.X86.Stream.params384)
      (finalizeDigestContract X86.abi H0_384 48 sha384 (20 + 1400)) 0 :=
  verifiedScrubbedF (api := finalize384Api)
    { code := Impl.StackScratch.X86.withStackScratch 1400 4
        (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params384)
      stack := 20 + 1400
      verified := Shared.finalize384 }
    (finalizeDigestOut _ _ _ (by decide) _)

/-- `vg_sha512_256_finalize` as emitted (`Impl.Sha512.X86.Fn.finalizeDigest`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize512_256_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.finalizeDigest Impl.Sha512.X86.Stream.params512_256)
      (finalizeDigestContract X86.abi H0_512_256 32 sha512_256 (20 + 1400)) 0 :=
  verifiedScrubbedF (api := finalize512_256Api)
    { code := Impl.StackScratch.X86.withStackScratch 1400 4
        (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_256)
      stack := 20 + 1400
      verified := Shared.finalize512_256 }
    (finalizeDigestOut _ _ _ (by decide) _)

/-- `vg_sha512_224_finalize` as emitted (`Impl.Sha512.X86.Fn.finalizeDigest`) meets its contract in
constant time and returns without secret residue. -/
theorem finalize512_224_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.finalizeDigest Impl.Sha512.X86.Stream.params512_224)
      (finalizeDigestContract X86.abi H0_512_224 28 sha512_224 (20 + 1400)) 0 :=
  verifiedScrubbedF (api := finalize512_224Api)
    { code := Impl.StackScratch.X86.withStackScratch 1400 4
        (Impl.Sha512.X86.Stream.finalizeDigest Impl.Sha512.X86.Stream.params512_224)
      stack := 20 + 1400
      verified := Shared.finalize512_224 }
    (finalizeDigestOut _ _ _ (by decide) _)

/-! ## The one-shot digests -/

/-- `vg_sha384_digest` as emitted (`Impl.Sha512.X86.Fn.digest`) meets its contract in constant
time and returns without secret residue. -/
theorem digest384_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.digest 48 "vg_sha384_init_core" H0_384)
      (digestContract X86.abi 48 sha384 (48 + dframe Proof.Pbkdf2.Stream.X86.sha384H)) 0 :=
  verifiedScrubbedF (api := digest384Api)
    { code := digest Proof.Pbkdf2.Stream.X86.sha384H
      stack := 48 + dframe Proof.Pbkdf2.Stream.X86.sha384H
      verified := Proof.MdStream.X86.Digest.sha384_digest
      spSafe := Proof.MdStream.X86.Digest.sha384_digestSp }
    (digestOut _ _ (by decide) _)

/-- `vg_sha512_digest` as emitted (`Impl.Sha512.X86.Fn.digest`) meets its contract in constant
time and returns without secret residue. -/
theorem digest512_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.digest 64 "vg_sha512_init_core" H0_512)
      (digestContract X86.abi 64 sha512 (48 + dframe Proof.Pbkdf2.Stream.X86.sha512H')) 0 :=
  verifiedScrubbedF (api := digest512Api)
    { code := digest Proof.Pbkdf2.Stream.X86.sha512H'
      stack := 48 + dframe Proof.Pbkdf2.Stream.X86.sha512H'
      verified := Proof.MdStream.X86.Digest.sha512_digest
      spSafe := Proof.MdStream.X86.Digest.sha512_digestSp }
    (digestOut _ _ (by decide) _)

/-- `vg_sha512_224_digest` as emitted (`Impl.Sha512.X86.Fn.digest`) meets its contract in constant
time and returns without secret residue. -/
theorem digest512_224_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.digest 28 "vg_sha512_224_init_core" H0_512_224)
      (digestContract X86.abi 28 sha512_224 (48 + dframe Proof.Pbkdf2.Stream.X86.sha512_224H)) 0 :=
  verifiedScrubbedF (api := digest512_224Api)
    { code := digest Proof.Pbkdf2.Stream.X86.sha512_224H
      stack := 48 + dframe Proof.Pbkdf2.Stream.X86.sha512_224H
      verified := Proof.MdStream.X86.Digest.sha512_224_digest
      spSafe := Proof.MdStream.X86.Digest.sha512_224_digestSp }
    (digestOut _ _ (by decide) _)

/-- `vg_sha512_256_digest` as emitted (`Impl.Sha512.X86.Fn.digest`) meets its contract in constant
time and returns without secret residue. -/
theorem digest512_256_scrubbed :
    VerifiedScrubbed target (Impl.Sha512.X86.Fn.digest 32 "vg_sha512_256_init_core" H0_512_256)
      (digestContract X86.abi 32 sha512_256 (48 + dframe Proof.Pbkdf2.Stream.X86.sha512_256H)) 0 :=
  verifiedScrubbedF (api := digest512_256Api)
    { code := digest Proof.Pbkdf2.Stream.X86.sha512_256H
      stack := 48 + dframe Proof.Pbkdf2.Stream.X86.sha512_256H
      verified := Proof.MdStream.X86.Digest.sha512_256_digest
      spSafe := Proof.MdStream.X86.Digest.sha512_256_digestSp }
    (digestOut _ _ (by decide) _)

end VG.Proof.Sha512.X86.Scrub

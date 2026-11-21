module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Init
public import VerifiedGarbage.Impl.Sha512.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha512.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sha512.Scratch
public import VerifiedGarbage.Proof.Sha512.Digest
public import VerifiedGarbage.Proof.MdStream.DigestScratch
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha512_256
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-384, SHA-512, SHA-512/224 and SHA-512/256 on PPC64LE, without secret residue

The streaming functions with frames and the one-shot digests, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Sha512/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha512.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sha512_update` as emitted (`Impl.Sha512.PPC64LE.Fn.update`) meets its
contract in constant time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.update
      (Spec.Sha512.updateContract PPC64LE.abi (0 + 1408)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.updateApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r7 Impl.Sha512.PPC64LE.Stream.update
      verified := Shared.update }
    1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.updatePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sha512_finalize` as emitted (`Impl.Sha512.PPC64LE.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.finalize
      (Spec.Sha512.finalizeContract PPC64LE.abi (0 + 1408)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sha384_finalize` as emitted (`Impl.Sha512.PPC64LE.Fn.finalize384`) meets
its contract in constant time and returns without secret residue. -/
theorem finalize384_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.finalize384
      (Spec.Sha512.finalizeDigestContract PPC64LE.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 (0 + 1408)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalize384Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize384
      verified := Shared.finalize384 }
    1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPostOut_local Spec.Sha512.H0_384 48 Spec.Sha512.sha384 64))
    (by dsimp only; lit_decide)

/-- `vg_sha512_224_finalize` as emitted (`Impl.Sha512.PPC64LE.Fn.finalize512_224`)
meets its contract in constant time and returns without secret residue. -/
theorem finalize512_224_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.finalize512_224
      (Spec.Sha512.finalizeDigestContract PPC64LE.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 (0 + 1408)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalize512_224Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_224
      verified := Shared.finalize512_224 }
    1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPostOut_local Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224 64))
    (by dsimp only; lit_decide)

/-- `vg_sha512_256_finalize` as emitted (`Impl.Sha512.PPC64LE.Fn.finalize512_256`)
meets its contract in constant time and returns without secret residue. -/
theorem finalize512_256_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.finalize512_256
      (Spec.Sha512.finalizeDigestContract PPC64LE.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 (0 + 1408)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.finalize512_256Api) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 1408 .r6 Impl.Sha512.PPC64LE.Stream.finalize512_256
      verified := Shared.finalize512_256 }
    1408 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha512.finalizeDigestPostOut_local Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256 64))
    (by dsimp only; lit_decide)

/-- `vg_sha384_digest` as emitted (`Impl.Sha512.PPC64LE.Fn.digest384`) meets its
contract in constant time and returns without secret residue. -/
theorem digest384_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.digest384
      (Spec.Sha512.digestContract PPC64LE.abi 48 Spec.Sha512.sha384 (96 + Impl.MdStream.PPC64LE.Digest.frameBytes Impl.Hmac.Stream.PPC64LE.sha384Hash)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest384Api) {
      code := Impl.MdStream.PPC64LE.Digest.code Impl.Hmac.Stream.PPC64LE.sha384Hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha384.digest }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 48 Spec.Sha512.sha384 64))
    (by dsimp only; lit_decide)

/-- `vg_sha512_digest` as emitted (`Impl.Sha512.PPC64LE.Fn.digest512`) meets its
contract in constant time and returns without secret residue. -/
theorem digest512_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.digest512
      (Spec.Sha512.digestContract PPC64LE.abi 64 Spec.Sha512.sha512 (96 + Impl.MdStream.PPC64LE.Digest.frameBytes Impl.Hmac.Stream.PPC64LE.sha512Hash)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest512Api) {
      code := Impl.MdStream.PPC64LE.Digest.code Impl.Hmac.Stream.PPC64LE.sha512Hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha512.digest }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 64 Spec.Sha512.sha512 64))
    (by dsimp only; lit_decide)

/-- `vg_sha512_224_digest` as emitted (`Impl.Sha512.PPC64LE.Fn.digest512_224`) meets its
contract in constant time and returns without secret residue. -/
theorem digest512_224_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.digest512_224
      (Spec.Sha512.digestContract PPC64LE.abi 28 Spec.Sha512.sha512_224 (96 + Impl.MdStream.PPC64LE.Digest.frameBytes Impl.Hmac.Stream.PPC64LE.sha512_224Hash)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest512_224Api) {
      code := Impl.MdStream.PPC64LE.Digest.code Impl.Hmac.Stream.PPC64LE.sha512_224Hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha512_224.digest }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 28 Spec.Sha512.sha512_224 64))
    (by dsimp only; lit_decide)

/-- `vg_sha512_256_digest` as emitted (`Impl.Sha512.PPC64LE.Fn.digest512_256`) meets its
contract in constant time and returns without secret residue. -/
theorem digest512_256_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha512.PPC64LE.Fn.digest512_256
      (Spec.Sha512.digestContract PPC64LE.abi 32 Spec.Sha512.sha512_256 (96 + Impl.MdStream.PPC64LE.Digest.frameBytes Impl.Hmac.Stream.PPC64LE.sha512_256Hash)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha512.digest512_256Api) {
      code := Impl.MdStream.PPC64LE.Digest.code Impl.Hmac.Stream.PPC64LE.sha512_256Hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha512_256.digest }
    656 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 32 Spec.Sha512.sha512_256 64))
    (by dsimp only; lit_decide)

/-- SHA-512's `init` from the initial hash value `iv` needs no cleanup: it reads no memory, so what it leaves is a function of its
arguments. It meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed (iv : Spec.Sha512.HashValue) :
    VerifiedScrubbed PPC64LE.target (Impl.Sha512.PPC64LE.Stream.init iv)
      (Spec.Sha512.initContract PPC64LE.abi iv) 0 :=
  ⟨Proof.Sha512.PPC64LE.Shared.init iv, Proof.Sha512.PPC64LE.Stream.init_noResidue _ _ _⟩

end VG.Proof.Sha512.PPC64LE

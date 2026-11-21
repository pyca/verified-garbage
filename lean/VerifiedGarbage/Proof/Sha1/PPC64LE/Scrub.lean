module

public import VerifiedGarbage.Impl.Hmac.Stream.PPC64LE.Fn
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Stream.Init
public import VerifiedGarbage.Impl.Sha1.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha1.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sha1.Scratch
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha1
public import VerifiedGarbage.Proof.MdStream.DigestScratch
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-1 on PPC64LE, without secret residue

The streaming functions with frames and the one-shot digest, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.verifiedScrubbedAll`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers. HMAC, PBKDF2 and the
other functions built on the hash call their code as internal functions of
their own (`*_scratch`), not these. The `init` functions read no memory, and
need no clearing (`Proof/Sha1/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha1.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sha1_update` as emitted (`Impl.Sha1.PPC64LE.Fn.update`) meets its contract
in constant time and returns without secret residue. -/
theorem update_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha1.PPC64LE.Fn.update
      (Spec.Sha1.updateContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha1.updateApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sha1.PPC64LE.Stream.update
      verified := Shared.update }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.updatePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sha1_finalize` as emitted (`Impl.Sha1.PPC64LE.Fn.finalize`) meets its
contract in constant time and returns without secret residue. -/
theorem finalize_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha1.PPC64LE.Fn.finalize
      (Spec.Sha1.finalizeContract PPC64LE.abi (48 + 192)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha1.finalizeApi) {
      code := Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sha1.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    240 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha1.finalizePostOut_local 64))
    (by dsimp only; lit_decide)

/-- `vg_sha1_digest` as emitted (`Impl.Sha1.PPC64LE.Fn.digest`) meets its
contract in constant time and returns without secret residue. -/
theorem digest_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha1.PPC64LE.Fn.digest
      (Spec.Sha1.digestContract PPC64LE.abi
        (96 + Impl.MdStream.PPC64LE.Digest.frameBytes Impl.Hmac.Stream.PPC64LE.sha1Hash)) 0 :=
  verifiedScrubbedAll (api := Spec.Sha1.digestApi) {
      code := Impl.MdStream.PPC64LE.Digest.code Impl.Hmac.Stream.PPC64LE.sha1Hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha1.digest }
    496 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false, []⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.MdStream.Digest.digestPostOut_local 20 Spec.Sha1.hash 64))
    (by dsimp only; lit_decide)

/-- `vg_sha1_init` needs no cleanup: it reads no memory, so what it leaves is a function of its
arguments. It meets its contract in constant time and returns without secret residue. -/
theorem init_scrubbed :
    VerifiedScrubbed PPC64LE.target Impl.Sha1.PPC64LE.Stream.init
      (Spec.Sha1.initContract PPC64LE.abi) 0 :=
  ⟨Proof.Sha1.PPC64LE.Shared.init, Proof.Sha1.PPC64LE.Stream.init_noResidue _ _⟩

end VG.Proof.Sha1.PPC64LE

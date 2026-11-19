module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Shared
public import VerifiedGarbage.Proof.Sha256.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Sha224
public import VerifiedGarbage.Proof.Sha256.PostOut
import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-224 and SHA-256 on PPC64LE, without secret residue

The streaming functions with frames and the one-shot functions, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers and the stack their frames used. Their postconditions
read the memory on return only within their buffers
(`Proof/Sha256/PostOut.lean`). HMAC, PBKDF2 and RSA call their code as
internal functions of their own (`vg_sha256_update_scratch`, …), not these.
The `init` functions read no memory, and need no clearing
(`Proof/Sha256/PPC64LE/Stream/Init.lean`).
-/

@[expose] public section

namespace VG.Proof.Sha256.PPC64LE

open VG.PPC64LE VG.PPC64LE.Scrub

/-- `vg_sha256_update`, which SHA-224 shares. -/
def updateReg : Registration Spec.Sha256.updateApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r7 Impl.Sha256.PPC64LE.Stream.update
      verified := Shared.update }
    688 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.updatePost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_sha256_finalize`. -/
def finalizeReg : Registration Spec.Sha256.finalizeApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize
      verified := Shared.finalize }
    688 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalizePost_out 64))
    (by dsimp only; lit_decide)

/-- `vg_sha224_finalize`. -/
def finalize224Reg : Registration Spec.Sha256.finalize224Api PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 640 .r6 Impl.Sha256.PPC64LE.Stream.finalize224
      verified := Shared.finalize224 }
    688 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain (Proof.Sha256.finalize224Post_out 64))
    (by dsimp only; lit_decide)

/-- `vg_sha256_digest`. -/
def digest256Reg : Registration Spec.Sha256.digest256Api PPC64LE.target :=
  scrubOf {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha256.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha256.digest }
    512 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 32 Spec.Sha256.hash 64 (by decide)))
    (by dsimp only; lit_decide)

/-- `vg_sha224_digest`. -/
def digest224Reg : Registration Spec.Sha256.digest224Api PPC64LE.target :=
  scrubOf {
      code := Impl.MdStream.PPC64LE.Digest.code Proof.Hmac.Stream.PPC64LE.Sha224.hash
      verified := Proof.Hmac.Stream.PPC64LE.Sha224.digest }
    512 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15, .v16,
       .v17, .v18, .v19]⟩
    (postOut_of_local (leak := none) ScrubAbi.plain
      (Proof.Sha256.digestPost_out 28 Spec.Sha256.sha224 64 (by decide)))
    (by dsimp only; lit_decide)

end VG.Proof.Sha256.PPC64LE

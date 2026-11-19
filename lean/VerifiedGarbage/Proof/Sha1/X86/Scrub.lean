module

public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.PostOut
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Shared
meta import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
meta import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Sha1.PostOut
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-1's `init` and one-shot digest on x86 (32-bit), without secret residue

`vg_sha1_init`, which calls nothing and has no frame, followed by the
clearing of the registers a callee may change (`X86.Scrub.scrubOf`); the
one-shot digest, for every backend, whose working space is in a frame of its
own, with the stack it and its callees use zeroed first
(`X86.Scrub.scrubFOf`), given that its postcondition reads the memory on
return only within the buffers (`Proof.Sha1.PostOut`). What the scrub needs
of the digest's code is evaluated where its backend is defined
(`Backend.digestScrub`), as are the streaming `update` and `finalize`
(`StreamFn.reg`). HMAC, PBKDF2 and the digest call `vg_sha1_init`'s code as
the internal `vg_sha1_init_core` (`Variants.hmacHash`).
-/

@[expose] public section

namespace VG.Proof.Sha1.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Sha1.X86.Variants (Backend)

/-- `vg_sha1_init`. -/
def initReg : Registration Spec.Sha1.initApi target :=
  scrubOf { code := Impl.Sha1.X86.Stream.init, verified := Proof.Sha1.X86.Shared.init }

theorem digestOut (stack : Nat) :
    PostOut (Spec.Sha1.digestContract X86.abi stack) (Spec.Sha1.digestSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha1.digestPost_out 32)

/-- `vg_sha1_digest` with the backend `v`, whose definition evaluates what
the scrub needs of its code (`Backend.digestScrub`). -/
def digestReg (v : Backend) : Registration Spec.Sha1.digestApi target :=
  scrubFOf {
      suffix := v.suffix
      code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha1H v.stream)
      verified := Proof.MdStream.X86.Digest.sha1_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha1_digestSp v.stream }
    (digestOut _) _ v.digestScrub

end VG.Proof.Sha1.X86.Scrub

module

public import VerifiedGarbage.Proof.Sha256.X86.Shared
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.PostOut
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Shared
meta import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
meta import VerifiedGarbage.Proof.MdStream.X86.DigestInstances
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Sha256.PostOut
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-224's and SHA-256's `init` and one-shot digest on x86 (32-bit), without secret residue

The `init`s of SHA-224 and SHA-256, which call nothing and have no frame,
followed by the clearing of the registers a callee may change
(`X86.Scrub.scrubOf`); the one-shot digests, for every backend, whose working
space is in a frame of their own, with the stack they and their callees use
zeroed first (`X86.Scrub.scrubFOf`), given that their postconditions read the
memory on return only within the buffers (`Proof.Sha256.PostOut`). What the
scrub needs of a digest's code is evaluated where its backend is defined
(`Backend.digestScrub`), as are the streaming `update` and `finalize`
(`StreamFn.reg`). HMAC, PBKDF2, RSA and the digests call the `init`s' code as
the internal `vg_sha224_init_core` and `vg_sha256_init_core`
(`Variants.hmacHash`).
-/

@[expose] public section

namespace VG.Proof.Sha256.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Sha256.X86.Variants (Backend)

/-- `vg_sha224_init`. -/
def init224Reg : Registration Spec.Sha256.init224Api target :=
  scrubOf { code := Impl.Sha256.X86.Stream.init224, verified := Proof.Sha256.X86.Shared.init224 }

/-- `vg_sha256_init`. -/
def initReg : Registration Spec.Sha256.initApi target :=
  scrubOf { code := Impl.Sha256.X86.Stream.init, verified := Proof.Sha256.X86.Shared.init }

theorem digestOut (D : Nat) (dg : List Byte → List Byte) (hD : D < 2 ^ 64) (stack : Nat) :
    PostOut (Spec.Sha256.digestContract X86.abi D dg stack) ((Spec.Sha256.digestSig D).retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Sha256.digestPost_out D dg 32 hD)

/-- `vg_sha256_digest` with the backend `v`, whose definition evaluates what
the scrub needs of its code (`Backend.digestScrub`). -/
def digestReg (v : Backend) : Registration Spec.Sha256.digest256Api target :=
  scrubFOf {
      suffix := v.suffix
      code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha256H v.stream)
      stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha256H v.stream)
      verified := Proof.MdStream.X86.Digest.sha256_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha256_digestSp v.stream }
    (digestOut _ _ (by decide) _) _ v.digestScrub

/-- `vg_sha224_digest` with the backend `v` (`Backend.digest224Scrub`). -/
def digest224Reg (v : Backend) : Registration Spec.Sha256.digest224Api target :=
  scrubFOf {
      suffix := v.suffix
      code := Impl.MdStream.X86.Digest.digest (Proof.Pbkdf2.Stream.X86.sha224H v.stream)
      stack := 48 + Impl.MdStream.X86.Digest.dframe (Proof.Pbkdf2.Stream.X86.sha224H v.stream)
      verified := Proof.MdStream.X86.Digest.sha224_digest v.stream
      spSafe := Proof.MdStream.X86.Digest.sha224_digestSp v.stream }
    (digestOut _ _ (by decide) _) _ v.digest224Scrub

end VG.Proof.Sha256.X86.Scrub

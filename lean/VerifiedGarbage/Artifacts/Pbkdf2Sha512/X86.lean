module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Sha512
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Lit
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Instances
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant

/-!
# PBKDF2-HMAC-SHA-512 (RFC 8018) on x86: the iteration and the whole derivation

The iteration is the one for every Merkle–Damgård hash function
(`Impl/Pbkdf2/Md/X86.lean`): each step is two calls of SHA-512's verified
compression function, on a block laid out once, word by word, in `scratch`
(`U`, its padding and length), starting from the key's inner and outer hash
values.

The whole derivation, `pbkdf2`, is the one for every streaming hash function
(`Impl/Pbkdf2/Whole/X86.lean`), calling the hash function's streaming
functions, HMAC's `init` and `finalize` and the iteration above, in a frame
holding its working space (`Proof.Pbkdf2.Whole.X86.pbkFramed`). `stack` is
that of the shared contracts: 48 bytes for the iteration, and 76 for
`pbkdf2`'s code, which pushes up to 24 bytes of arguments for the functions
it calls, and their return address, then its frame.
-/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha512.X86

open VG.Proof.Pbkdf2.Stream.X86

def artifacts : List Artifact := [
  Spec.Hmac.sha512I.iterateApi.artifact X86.target {
    code := Proof.Pbkdf2.Md.X86.sha512M'.iterate
    stack := 48
    verified := Proof.Pbkdf2.Md.X86.Instances.sha512_iterate },
  Spec.Hmac.sha512I.pbkdf2Api.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratch (Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha512I) 7
      Proof.Pbkdf2.Whole.X86.sha512F.pbkdf2
    stack := 76 + Proof.Pbkdf2.Whole.X86.pbkFrame Spec.Hmac.sha512I
    verified := Proof.Pbkdf2.Whole.X86.pbkFramed Proof.Pbkdf2.Whole.X86.sha512
      Proof.Pbkdf2.Whole.X86.sha512_pbkFrameSat }]

end VG.Artifacts.Pbkdf2Sha512.X86

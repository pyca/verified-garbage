module

public import VerifiedGarbage.Proof.Sha256.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha256.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Sha256.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-224's and SHA-256's `init` on x86 (32-bit), without secret residue

The `init`s of SHA-224 and SHA-256, which call nothing and have no frame,
each followed by the clearing of the registers a callee may change
(`X86.Scrub.scrubOf`). HMAC, PBKDF2, RSA and the one-shot digests call their
code as the internal `vg_sha224_init_core` and `vg_sha256_init_core`
(`Variants.hmacHash`), whose code is not scrubbed.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- `vg_sha224_init`. -/
def init224Reg : Registration Spec.Sha256.init224Api target :=
  scrubOf { code := Impl.Sha256.X86.Stream.init224, verified := Proof.Sha256.X86.Shared.init224 }

/-- `vg_sha256_init`. -/
def initReg : Registration Spec.Sha256.initApi target :=
  scrubOf { code := Impl.Sha256.X86.Stream.init, verified := Proof.Sha256.X86.Shared.init }

end VG.Proof.Sha256.X86.Scrub

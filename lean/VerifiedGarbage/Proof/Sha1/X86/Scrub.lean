module

public import VerifiedGarbage.Proof.Sha1.X86.Shared
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Sha1.Contract
import VerifiedGarbage.Proof.Sha1.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha1.X86.Shared
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Sha1.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# SHA-1's `init` on x86 (32-bit), without secret residue

`vg_sha1_init`, which calls nothing and has no frame, followed by the
clearing of the registers a callee may change (`X86.Scrub.scrubOf`). HMAC,
PBKDF2 and the one-shot digest call its code as the internal
`vg_sha1_init_core` (`Variants.hmacHash`), whose code is not scrubbed.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- `vg_sha1_init`. -/
def initReg : Registration Spec.Sha1.initApi target :=
  scrubOf { code := Impl.Sha1.X86.Stream.init, verified := Proof.Sha1.X86.Shared.init }

end VG.Proof.Sha1.X86.Scrub

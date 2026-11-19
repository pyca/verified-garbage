module

public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RSA key generation on x86 (32-bit), without secret residue

`vg_rsa_generate_init`, which calls nothing and has no frame, followed by
the tail that clears the registers (`X86.Scrub.scrubOf`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- `Spec.RsaKeyGen.keyInitApi`. -/
def keyInitReg : Registration Spec.RsaKeyGen.keyInitApi X86.target :=
  scrubOf {
    code := Impl.RsaKeyGen.X86.KeyInit.init
    verified := Proof.RsaKeyGen.X86.KeyInit.init_verified }

end VG.Proof.RsaKeyGen.X86.Scrub

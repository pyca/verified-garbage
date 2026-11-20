module

public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Fn
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Impl.RsaKeyGen.X86.Fn
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# RSA key generation on x86 (32-bit), without secret residue

`vg_rsa_generate_init`, which calls nothing and has no frame, is emitted
with the tail that clears the registers (`Impl.RsaKeyGen.X86.Fn.generateInit`),
and returns without secret residue (`generateInit_scrubbed`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Scrub

open VG.X86 VG.X86.Scrub

/-- `vg_rsa_generate_init`, with its cleanup, returns without secret residue. -/
theorem generateInit_scrubbed :
    VerifiedScrubbed target Impl.RsaKeyGen.X86.Fn.generateInit (Spec.RsaKeyGen.keyInitContract abi) 32 :=
  verifiedScrubbed (api := Spec.RsaKeyGen.keyInitApi) {
    code := Impl.RsaKeyGen.X86.KeyInit.init
    verified := Proof.RsaKeyGen.X86.KeyInit.init_verified }

end VG.Proof.RsaKeyGen.X86.Scrub

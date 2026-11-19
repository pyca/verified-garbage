module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Verified
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Verified
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# What the cleanup of RSASSA-PKCS1-v1_5 signing needs of its code (x86, 32-bit)

`vg_rsa_pkcs1_sign_precomputed` is generic over the implementation of the
RSA private key operation (`CrtImpl`, `Proof/Variants/RsaPrivateCrt/X86.lean`),
of which it calls the public precomputation and check (`CrtImpl.pc`,
`CrtImpl.pd`). Its deepest path is the CRT, not those, so its stub gives
each its own budget (`holeStub 96`, the stack `pcStack` and `pdStack`
bound) rather than adding it to the whole (`FillB`, `scrubFSide_of_fillB`):
`scrubFSide` of the stub over the contract's 4584 bytes, which the kernel
evaluates once (`sign_side`), holds of the code with every implementation
(`sign_scrub`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86.Scrub

open VG.X86 VG.X86.Scrub
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCodeP crtPBaseline)

/-- `vg_rsa_pkcs1_sign_precomputed` with the public precomputation and
check holes of 96 bytes. -/
def signStub : Prog isa :=
  Impl.RsaPkcs1Sig.X86.Sign.code ""
    (Impl.Rsa.X86.PrivChecked.codeP crtPBaseline.name crtPBaseline.code "" (holeStub 96) "" (holeStub 96))
    Impl.RsaPkcs1Sig.X86.Sign.callArgsP

-- The stub as a literal, for the kernel's evaluation.
materialize_code signStub

theorem sign_side : scrubFSide signStub [] 4584 = true := by lit_decide

theorem sign_fill (v : CrtImpl) (hc : calleeSide v.pc 96 = true) (hd : calleeSide v.pd 96 = true) :
    FillB signStub (Impl.RsaPkcs1Sig.X86.Sign.code (Proof.RsaPkcs1Sig.X86.Sgn.privNameP v)
      (privCodeP v crtPBaseline) Impl.RsaPkcs1Sig.X86.Sign.callArgsP) := by
  unfold signStub
  fillB_calls

/-- `scrubFSide` of `vg_rsa_pkcs1_sign_precomputed`, whatever the
implementation of the private key operation. -/
theorem sign_scrub (v : CrtImpl) :
    scrubFSide (Impl.RsaPkcs1Sig.X86.Sign.code (Proof.RsaPkcs1Sig.X86.Sgn.privNameP v)
      (privCodeP v crtPBaseline) Impl.RsaPkcs1Sig.X86.Sign.callArgsP) [] 4584 = true :=
  scrubFSide_of_fillB (sign_fill v (calleeSide_of_le v.pcStack v.pcScrub)
    (calleeSide_of_le v.pdStack v.pdScrub)) sign_side

end VG.Proof.RsaPkcs1Sig.X86.Scrub

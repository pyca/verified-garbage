module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Sign
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed
public import VerifiedGarbage.Impl.Rsa.AArch64.PrivChecked
public import VerifiedGarbage.Impl.Scrub.AArch64.WritesL

/-! # RSASSA-PKCS1-v1_5 with a precomputed key on AArch64: the functions as emitted

Each function's code, then its cleanup: the registers the code may write
cleared, and its stack zeroed (`scrubOf`, `scrubOfL`). -/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.AArch64.Fn

open VG VG.AArch64
open VG.Impl.Scrub.AArch64 (scrubOf scrubOfL)
open VG.Impl.Rsa.AArch64.PrivChecked (Crt)

/-- `vg_rsa_pkcs1_sign_precomputed` with the implementation `c` of the
private-key operation: its frame of 1152 bytes over the 3248 of
`vg_rsa_private_checked_precomputed`. -/
def signPrecomputed (c : Crt) : Prog isa := scrubOfL 4400 32 (Sign.codeP c.privPName c.privP)

/-- `vg_rsa_pkcs1_verify_precomputed` calling the public-key operation
`pub`: its frame of 2128 bytes, and the two words of arguments it passes on
the stack. -/
def verifyPrecomputed (pubName : String) (pub : Prog isa) : Prog isa :=
  scrubOf 2144 32 (Precomputed.code pubName pub)

/-- `vg_rsa_pkcs1_recover_precomputed` calling the public-key operation
`pub`, with the stack of `verifyPrecomputed`. -/
def recoverPrecomputed (pubName : String) (pub : Prog isa) : Prog isa :=
  scrubOf 2144 32 (RecoverPrecomputed.code pubName pub)

end VG.Impl.RsaPkcs1Sig.AArch64.Fn

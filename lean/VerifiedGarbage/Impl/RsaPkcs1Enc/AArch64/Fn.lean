module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-! # RSAES-PKCS1-v1_5 on AArch64: encryption as emitted

`vg_rsa_pkcs1_encrypt_random`'s code, then its cleanup: the registers the code may write
cleared, and its stack zeroed (`scrubOf`). -/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.AArch64.Fn

open VG VG.AArch64
open VG.Impl.Scrub.AArch64 (scrubOf)

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
made with the public-key operation `pub`, named `pubName` (its name ends in
`suffix`): its frames of 2192 bytes, and the two words of arguments the
public-key operation is passed on the stack. -/
def encryptRandom (suffix pubName : String) (pub : Prog isa) : Prog isa :=
  scrubOf 2208 32 (Random.code ("vg_rsa_pkcs1_encrypt_precomputed" ++ suffix) (Precomputed.code pubName pub))

end VG.Impl.RsaPkcs1Enc.AArch64.Fn

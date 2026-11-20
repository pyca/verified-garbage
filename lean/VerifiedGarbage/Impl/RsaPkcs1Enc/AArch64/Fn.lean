module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Decrypt
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Random
public import VerifiedGarbage.Impl.Rsa.AArch64.PrivChecked
public import VerifiedGarbage.Impl.Scrypt.AArch64.Scrypt
public import VerifiedGarbage.Impl.Residue.AArch64.Writes

/-! # RSAES-PKCS1-v1_5 on AArch64: the functions as emitted

Each function's code, then its cleanup: the registers the code may write
cleared, and its stack zeroed (`scrubOf`). -/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.AArch64.Fn

open VG VG.AArch64
open VG.Impl.Residue.AArch64 (scrubOf)
open VG.Impl.Rsa.AArch64.PrivChecked (Crt)

/-- `vg_rsa_pkcs1_decrypt_precomputed` over SHA-256's compression function
`code`, named `name` (the names of the hash functions made with it end in
`suffix`), with the implementation `c` of the private-key operation: its
frame of 240 bytes over the 3248 of `vg_rsa_private_checked_precomputed`. -/
def decryptPrecomputed (name suffix : String) (code : Prog isa) (c : Crt) : Prog isa :=
  scrubOf 3488 32 (Decrypt.codeP (Impl.Scrypt.AArch64.sha256 name suffix code) c.privPName c.privP)

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
made with the public-key operation `pub`, named `pubName` (its name ends in
`suffix`): its frames of 2192 bytes, and the two words of arguments the
public-key operation is passed on the stack. -/
def encryptRandom (suffix pubName : String) (pub : Prog isa) : Prog isa :=
  scrubOf 2208 32 (Random.code ("vg_rsa_pkcs1_encrypt_precomputed" ++ suffix) (Precomputed.code pubName pub))

end VG.Impl.RsaPkcs1Enc.AArch64.Fn

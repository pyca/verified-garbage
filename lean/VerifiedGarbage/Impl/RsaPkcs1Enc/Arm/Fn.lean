module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Decrypt
public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Random
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# RSAES-PKCS1-v1_5 on ARMv7, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.Arm.scrubAll`):
the stack its contract reserves zeroed, where its frames and those of the
functions it calls kept the key's values, the encoded message and the
padding, then the registers a callee may change set to constants, but the
32 bits of the result, and the flags. Each takes the functions it calls, as
its registration maps over their implementations. Their frames use 3592
and 2360 bytes, which are not frame sizes of the model, so their contracts
reserve, and the cleanup zeroes, the next ones, 3648 and 2368.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_rsa_pkcs1_decrypt_precomputed`, calling the SHA-256 and HMAC
functions `H` and `vg_rsa_private_checked_precomputed` (`priv`, by its name
`privN`). -/
def decryptPrecomputed (H : Decrypt.Fns) (privN : String) (priv : Prog isa) : Prog isa :=
  scrubAll 32 3648 (Decrypt.code H true privN priv)

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
(`enc`, by its name `encName`). -/
def encryptRandom (encName : String) (enc : Prog isa) : Prog isa :=
  scrubAll 32 2368 (Random.code encName enc)

end VG.Impl.RsaPkcs1Enc.Arm.Fn

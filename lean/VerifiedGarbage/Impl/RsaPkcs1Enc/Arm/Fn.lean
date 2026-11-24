module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.Arm.Random
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# RSAES-PKCS1-v1_5 on ARMv7, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.Arm.scrubAll`):
the stack its contract reserves zeroed, where its frames and those of the
functions it calls kept the key's values and the padding, then the
registers a callee may change set to constants, but the 32 bits of the
result, and the flags. Each takes the functions it calls, as its
registration maps over their implementations. The frames of
`vg_rsa_pkcs1_encrypt_random` use 2360 bytes, which is not a frame size of
the model, so its contract reserves, and the cleanup zeroes, the next one,
2368. (`vg_rsa_pkcs1_decrypt_precomputed` is in
`Impl/RsaPkcs1Enc/Arm/Front.lean`.)
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_rsa_pkcs1_encrypt_random`, calling `vg_rsa_pkcs1_encrypt_precomputed`
(`enc`, by its name `encName`). -/
def encryptRandom (encName : String) (enc : Prog isa) : Prog isa :=
  scrubAll 32 2368 (Random.code encName enc)

end VG.Impl.RsaPkcs1Enc.Arm.Fn

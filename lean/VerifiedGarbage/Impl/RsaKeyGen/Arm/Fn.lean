module

public import VerifiedGarbage.Impl.RsaKeyGen.Arm.KeyInit
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Generate
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# RSA key generation on ARMv7, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.Arm`): the
registers a callee may change set to constants, but the 32 bits of the
result, and the flags. `vg_rsa_generate_init` has no frame (`scrub`);
`vg_rsa_generate` first zeroes the 304 bytes of stack its contract reserves,
where its frames and those of the prime search, the candidate test and the
key's assembly kept the candidates and the key (`scrubAll`). It takes the code
it calls, the prime search over an implementation of the Miller–Rabin round,
as its registration maps over them.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_rsa_generate_init`. -/
def generateInit : Prog isa := scrub 32 KeyInit.init

/-- `vg_rsa_generate`, calling the prime search `search` and the key's
assembly `key`. -/
def generate (search key : Prog isa) : Prog isa := scrubAll 32 304 (Generate.code search key)

end VG.Impl.RsaKeyGen.Arm.Fn

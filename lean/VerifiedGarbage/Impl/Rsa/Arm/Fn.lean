module

public import VerifiedGarbage.Impl.Rsa.Arm.CheckKey
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Impl.Rsa.Arm.RecoverDet
public import VerifiedGarbage.Impl.Bignum.Arm.PrivPreFn
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# RSA's key functions on ARMv7, as emitted

Each function is its code, then its cleanup (`Impl.Scrub.Arm`): the
registers a callee may change set to constants, but the 32 bits of the
result, and the flags. `vg_rsa_check_key` and `vg_rsa_crt_values` have no
frame (`scrub`); `vg_rsa_recover_primes_det`, `vg_rsa_public_precompute` and
`vg_rsa_private_precompute` first zero the stack their contracts reserve,
56, 56 and 168 bytes, where their frames kept the key's values (`scrubAll`).
`vg_rsa_public_precompute` is the code of an implementation of the private
CRT's interface (`Proof.Rsa.Arm.CrtImpl.pc`), which it takes.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_rsa_check_key`. -/
def checkKey : Prog isa := scrub 32 CheckKey.code

/-- `vg_rsa_check_key_umaal`. -/
def checkKeyU : Prog isa := scrub 32 CheckKey.codeU

/-- `vg_rsa_crt_values` (`um = false`) or `vg_rsa_crt_values_umaal`. -/
def crtValues (um : Bool) : Prog isa := scrub 32 (CrtValues.codeFor um)

/-- `vg_rsa_recover_primes_det` (`um = false`) or
`vg_rsa_recover_primes_det_umaal`. -/
def recoverPrimesDet (um : Bool) : Prog isa := scrubAll 32 56 (RecoverDet.codeFor um)

/-- `vg_rsa_private_precompute`. -/
def privatePrecompute : Prog isa := scrubAll 32 168 Impl.Bignum.Arm.PrivPreFn.code

/-- `vg_rsa_private_precompute_umaal`. -/
def privatePrecomputeU : Prog isa := scrubAll 32 168 Impl.Bignum.Arm.PrivPreFn.codeU

/-- `vg_rsa_public_precompute`, of an implementation's code `pc`. -/
def publicPrecompute (pc : Prog isa) : Prog isa := scrubAll 32 56 pc

end VG.Impl.Rsa.Arm.Fn

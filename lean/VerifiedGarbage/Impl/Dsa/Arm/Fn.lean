module

public import VerifiedGarbage.Impl.Dsa.Arm.GenerateKey
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Impl.Dsa.Arm.Generation
public import VerifiedGarbage.Impl.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.Arm.Prevalidated
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# DSA's functions on ARMv7, as emitted

Each function is its code, with either multiplication (`umaal`), then its
cleanup (`Impl/Residue/Arm.lean`): the registers a callee may change set to
constants, but the 32 bits of its result. The validations, the verification,
the key derivation and the initialization of the parameter search have no
frames (`scrub`); signing and key generation, which call the entropy function
from a frame, first zero the 144 bytes of stack their contracts reserve
(`scrubF`).
-/

@[expose] public section

namespace VG.Impl.Dsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_dsa_validate_private_key`. -/
def validatePrivateKey (umaal : Bool) : Prog isa := scrub 32 (PrevalidatedSign.validate umaal)

/-- `vg_dsa_derive_key`. -/
def deriveKey (umaal : Bool) : Prog isa := scrub 32 (Generate.deriveKey umaal)

/-- `vg_dsa_validate_public_key`. -/
def validatePublicKey (umaal : Bool) : Prog isa := scrub 32 (Prevalidated.validate umaal)

/-- `vg_dsa_verify_prevalidated`. -/
def verifyPrevalidated (umaal : Bool) : Prog isa := scrub 32 (Prevalidated.verify umaal)

/-- `vg_dsa_parameter_init`. -/
def parameterInit : Prog isa := scrub 32 Generation.init

/-- `vg_dsa_random_sign_prevalidated`, calling its signer as the internal
function `PrevalidatedSign.signerName umaal`. -/
def randomSignPrevalidated (umaal : Bool) : Prog isa :=
  scrubF 32 144 (RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal))

/-- `vg_dsa_generate_key`, calling the check of the parameters and the
derivation as the internal functions `Generate.checkName umaal` and
`Generate.deriveName umaal`. -/
def generateKey (umaal : Bool) : Prog isa :=
  scrubF 32 144 (GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
    (Generate.checkParameters umaal) (Generate.deriveChecked umaal))

end VG.Impl.Dsa.Arm.Fn

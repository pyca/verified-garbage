module

public import VerifiedGarbage.Impl.Dsa.Arm.GenerateKey
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
public import VerifiedGarbage.Impl.Dsa.Arm.Generation
public import VerifiedGarbage.Impl.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.Arm.Prevalidated
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Impl.Scrub.Arm
public import VerifiedGarbage.Impl.Dsa.Arm.Pow
public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime

/-!
# DSA's functions on ARMv7, as emitted

Each function is its code, with either multiplication (`umaal`), then its
cleanup (`Impl/Scrub/Arm.lean`): the registers a callee may change set to
constants, but the 32 bits of its result. The validations, the verification,
the key derivation and the initialization of the parameter search have no
frames (`scrub`); signing and key generation, which call the entropy function
from a frame, first zero the 144 bytes of stack their contracts reserve
(`scrubAll`), and the parameter search the 352 of its own.

The parameter search calls the Miller–Rabin round of a variant (its
`suffix` and `round` code) through the probable-prime test: `geo` is its
geometry for each modulus width.
-/

@[expose] public section

namespace VG.Impl.Dsa.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

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
  scrubAll 32 144 (RandomSign.code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal))

/-- `vg_dsa_generate_key`, calling the check of the parameters and the
derivation as the internal functions `Generate.checkName umaal` and
`Generate.deriveName umaal`. -/
def generateKey (umaal : Bool) : Prog isa :=
  scrubAll 32 144 (GenerateKey.code (Generate.checkName umaal) (Generate.deriveName umaal)
    (Generate.checkParameters umaal) (Generate.deriveChecked umaal))

/-- The geometry of the parameter search for `(pLen, qLen)`, hashing with
`G`, testing with the probable-prime function over the Miller–Rabin round
`round` of the variant `suffix` and the Montgomery product `op`, and
exponentiating with `vg_dsa_pow_{pLen/8}_{e}`. -/
@[reducible] def geo (umaal : Bool) (pLen qLen : Nat) (G : Generation.Hash) (suffix : String)
    (round : Prog isa) (op : Nat → Nat → Nat → Prog isa) : Generation.Geo where
  pLen := pLen
  qLen := qLen
  e := (8 * pLen - 8 * qLen) / 32 + 1
  G := G
  qName := "vg_dsa_probable_prime" ++ suffix
  qCode := ProbablePrime.code ("vg_miller_rabin_round" ++ suffix) round op
  pName := "vg_dsa_probable_prime" ++ suffix
  pCode := ProbablePrime.code ("vg_miller_rabin_round" ++ suffix) round op
  powName := Pow.name umaal (pLen / 8) ((8 * pLen - 8 * qLen) / 32 + 1)
  powCode := Pow.body umaal (pLen / 8) ((8 * pLen - 8 * qLen) / 32 + 1)
  powMod := Mont.Arm.Dynamic.modS (pLen / 8)
  powBase := Mont.Arm.Dynamic.baseS (pLen / 8)
  powExp := Mont.Arm.Dynamic.expS (pLen / 8)
  powRes := Mont.Arm.Dynamic.resS (pLen / 8)
  checkName := Generate.checkName umaal
  checkCode := Generate.checkParameters umaal

/-- The parameter search's code, for the three modulus widths, over the
Miller–Rabin round `round` of the variant `suffix` and the product `op`. -/
def search (umaal : Bool) (suffix : String) (round : Prog isa) (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  Generation.code (geo umaal 128 20 Generation.sha1 suffix round op)
    (geo umaal 256 32 Generation.sha256 suffix round op) (geo umaal 384 32 Generation.sha256 suffix round op)

/-- `vg_dsa_parameter_search`, its working space in a frame that is then
zeroed. -/
def parameterSearch (umaal : Bool) (suffix : String) (round : Prog isa) (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubAll 32 352 (search umaal suffix round op)

end VG.Impl.Dsa.Arm.Fn

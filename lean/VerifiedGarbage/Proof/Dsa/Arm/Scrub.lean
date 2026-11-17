module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Dsa.Arm.ValidatePrivateVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.GenerateVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified
meta import VerifiedGarbage.Proof.Dsa.Arm.Gen.Init
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Dsa.Arm.Leaves

/-!
# DSA on ARMv7, without secret residue

DSA's validations, its verification, its key derivation and the
initialization of its parameter search have no frames: they keep the
registers they save in their scratch space, a buffer. Each is registered
scrubbed (`Arm.Scrub.scrubReg`): followed by instructions that set the
registers a callee may change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Scrub

open VG VG.Arm VG.Impl.Dsa.Arm

def validatePrivateKeyReg : Registration Spec.Dsa.validatePrivateKeyApi target :=
  Arm.Scrub.scrubReg { code := PrevalidatedSign.validate, verified := validating_private_verified }
    (by lit_decide)

def deriveKeyReg : Registration Spec.Dsa.deriveKeyApi target :=
  Arm.Scrub.scrubReg { code := Generate.deriveKey, verified := derive_verified } (by lit_decide)

def validatePublicKeyReg : Registration Spec.Dsa.validatePublicKeyApi target :=
  Arm.Scrub.scrubReg { code := Prevalidated.validate, verified := validate_verified } (by lit_decide)

def verifyPrevalidatedReg : Registration Spec.Dsa.verifyPrevalidatedApi target :=
  Arm.Scrub.scrubReg { code := Prevalidated.verify, verified := prevalidated_verified } (by lit_decide)

def parameterInitReg : Registration Spec.Dsa.parameterInitApi target :=
  Arm.Scrub.scrubReg { code := Generation.init, verified := Gen.Init.init_verified } (by lit_decide)

end VG.Proof.Dsa.Arm.Scrub

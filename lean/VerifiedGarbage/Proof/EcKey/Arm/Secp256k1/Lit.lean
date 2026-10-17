module

public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
public import VerifiedGarbage.Impl.EcKey.Secp256k1.Arm
meta import VerifiedGarbage.Impl.EcKey.Secp256k1.Arm
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# secp256k1 public keys on 32-bit ARM: the code as a literal

As for the signature (`Proof/Ecdsa/Arm/Lit.lean`): the literal of the code is
checked once here, rather than rebuilt in every check that evaluates it.
-/

@[expose] public section

namespace VG

materialize_code Impl.EcKey.Arm.publicKeySecp256k1

end VG

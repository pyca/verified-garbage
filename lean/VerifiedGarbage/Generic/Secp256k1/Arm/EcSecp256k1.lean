module

public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.NatPairs
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombVerified -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# secp256k1 public keys (FIPS 186-5 §A.2) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.EcKey.Secp256k1.publicKeyApi.artifact Arm.target {
    notes := ["Generator multiplication reuses the shared signed 7-bit comb: 37 additions \
      with complete Renes–Costello–Batina formulas and a 151552-byte Montgomery table. Each \
      digit scans all 64 entries in its public row and selects coordinates by masks. Field \
      arithmetic uses sixteen 16-bit Montgomery digits. The final inversion is Fermat's; \
      invalid scalars select a zero result. Memory access and control flow depend only on pointers."]
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    code := Impl.Ecdsa.Arm.publicKeySecp256k1Comb
    verified := Proof.EcKey.Arm.Secp256k1.combPk_verified h.law }]

end VG.Generic.Secp256k1.Arm.EcSecp256k1

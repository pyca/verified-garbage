module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
public import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombVerified
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombVerified -- shake: keep (proof binding in exposed artifacts)
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ECDSA over secp256k1 (FIPS 186-5) on 32-bit ARM

A generic file (see `TCB/Emit.lean`) over secp256k1's group law `h`, the variant
`Variants/Secp256k1/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.Arm.EcdsaSecp256k1

def artifacts (h : Proof.Weierstrass.HasLaw Spec.Secp256k1.curve) : List Artifact := [
  Spec.Ecdsa.Secp256k1.signApi.artifact Arm.target {
    notes := ["Generator multiplication uses the shared signed 7-bit comb: 37 complete \
      Renes–Costello–Batina additions and a 151552-byte Montgomery table. Each digit scans all \
      64 entries in its public row and selects coordinates by masks. Field elements and scalars \
      use sixteen 16-bit Montgomery digits. Inversions modulo p and n use Fermat's theorem. \
      Invalid inputs select a zero signature; memory access and control flow depend only on pointers."]
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    code := Impl.Ecdsa.Arm.signSecp256k1Comb
    verified := Proof.Ecdsa.Arm.Secp256k1.combSign_verified h.law },
  Spec.Ecdsa.Secp256k1.verifyApi.artifact Arm.target {
    notes := ["The generator term [u]G uses the same signed 7-bit comb as signing, scanning \
      each complete 64-entry table row. The variable-base term [v]Q retains the 256-bit \
      double-and-add ladder. Both use complete Renes–Costello–Batina addition formulas. \
      Public-key validation, scalar checks and Fermat inversions are shared with the original \
      implementation; the result combines all checks as a mask."]
    consts := Impl.Weierstrass.Arm.secp256k1CombConsts
    code := Impl.Ecdsa.Arm.verifySecp256k1Comb
    verified := Proof.Ecdsa.Verify.Arm.Secp256k1.combVerify_verified h.law }]

end VG.Generic.Secp256k1.Arm.EcdsaSecp256k1

module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.EcKey.PPC64LE.Scrub.Out
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.Ecdsa.PPC64LE.VerifyHash
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.P192.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.P224.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.P521.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.PPC64LE
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Verified
public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Verified
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224
public import VerifiedGarbage.Spec.Ecdsa.Verify.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP256r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# ECDSA verification on PPC64LE, without secret residue

For every curve, `vg_ecdsa_<curve>_verify`, followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers and the stack its frames used. Its postcondition does not
read the memory on return (`Proof/EcKey/PPC64LE/Scrub/Out.lean`). Each takes
the curve's group law (`Weierstrass.Law`), which its registration file gives.
`scrubOf`'s side condition (`scrubSide`) is proved at each registration, by
the kernel's evaluation of it when this module is built.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub
open VG.Proof.Weierstrass (Law)

/-- `Spec.Ecdsa.P192.verifyHashApi`. -/
def p192Verify (hL : Law Spec.P192.curve) : Registration Spec.Ecdsa.P192.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyP192
      verified := Proof.Ecdsa.Verify.PPC64LE.P192.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ [] Spec.Ecdsa.P192.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.P224.verifyHashApi`. -/
def p224Verify (hL : Law Spec.P224.curve) : Registration Spec.Ecdsa.P224.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyP224
      verified := Proof.Ecdsa.Verify.PPC64LE.P224.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.p224CombConsts Spec.Ecdsa.P224.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.P256.verifyHashApi`. -/
def p256Verify (hL : Law Spec.P256.curve) : Registration Spec.Ecdsa.P256.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyP256
      verified := Proof.Ecdsa.Verify.PPC64LE.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.p256CombConsts Spec.Ecdsa.P256.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.P384.verifyHashApi`. -/
def p384Verify (hL : Law Spec.P384.curve) : Registration Spec.Ecdsa.P384.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyP384
      verified := Proof.Ecdsa.Verify.PPC64LE.P384.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.p384CombConsts Spec.Ecdsa.P384.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.P521.verifyHashApi`. -/
def p521Verify (hL : Law Spec.P521.curve) : Registration Spec.Ecdsa.P521.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true
        Impl.Ecdsa.Verify.PPC64LE.verifyP521
      verified := Proof.Ecdsa.Verify.PPC64LE.P521.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.p521CombConsts Spec.Ecdsa.P521.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.Secp256k1.verifyHashApi`. -/
def secp256k1Verify (hL : Law Spec.Secp256k1.curve) : Registration Spec.Ecdsa.Secp256k1.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifySecp256k1
      verified := Proof.Ecdsa.Verify.PPC64LE.Secp256k1.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.secp256k1CombConsts Spec.Ecdsa.Secp256k1.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.BrainpoolP256r1.verifyHashApi`. -/
def brainpoolp256r1Verify (hL : Law Spec.BrainpoolP256r1.curve) : Registration Spec.Ecdsa.BrainpoolP256r1.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP256r1
      verified := Proof.Ecdsa.Verify.PPC64LE.BrainpoolP256r1.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.brainpoolp256r1CombConsts Spec.Ecdsa.BrainpoolP256r1.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.BrainpoolP320r1.verifyHashApi`. -/
def brainpoolp320r1Verify (hL : Law Spec.BrainpoolP320r1.curve) : Registration Spec.Ecdsa.BrainpoolP320r1.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP320r1
      verified := Proof.Ecdsa.Verify.PPC64LE.BrainpoolP320r1.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.brainpoolp320r1CombConsts Spec.Ecdsa.BrainpoolP320r1.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.BrainpoolP384r1.verifyHashApi`. -/
def brainpoolp384r1Verify (hL : Law Spec.BrainpoolP384r1.curve) : Registration Spec.Ecdsa.BrainpoolP384r1.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP384r1
      verified := Proof.Ecdsa.Verify.PPC64LE.BrainpoolP384r1.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.brainpoolp384r1CombConsts Spec.Ecdsa.BrainpoolP384r1.inst)
    (by dsimp only; lit_decide)

/-- `Spec.Ecdsa.BrainpoolP512r1.verifyHashApi`. -/
def brainpoolp512r1Verify (hL : Law Spec.BrainpoolP512r1.curve) : Registration Spec.Ecdsa.BrainpoolP512r1.verifyHashApi PPC64LE.target :=
  scrubOf {
      code := Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false
        Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP512r1
      verified := Proof.Ecdsa.Verify.PPC64LE.BrainpoolP512r1.verifyHash_verified hL }
    112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v18, .v19]⟩
    (Proof.EcKey.PPC64LE.Scrub.verifyHashOut _ Impl.Weierstrass.PPC64LE.brainpoolp512r1CombConsts Spec.Ecdsa.BrainpoolP512r1.inst)
    (by dsimp only; lit_decide)

end VG.Proof.Ecdsa.Verify.PPC64LE.Scrub

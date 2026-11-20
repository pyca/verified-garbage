module

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
public import VerifiedGarbage.Impl.Scrub.PPC64LE
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP320r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.BrainpoolP512r1
public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.P192
public import VerifiedGarbage.Spec.Ecdsa.P224
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.P384
public import VerifiedGarbage.Spec.Ecdsa.P521
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
public import VerifiedGarbage.Spec.Weierstrass

/-!
# Ecdsa Verify on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Ecdsa/Verify/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `Spec.Ecdsa.P192.verifyHashApi`'s function, as emitted. -/
def p192Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyP192)

/-- `Spec.Ecdsa.P224.verifyHashApi`'s function, as emitted. -/
def p224Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyP224)

/-- `Spec.Ecdsa.P256.verifyHashApi`'s function, as emitted. -/
def p256Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyP256)

/-- `Spec.Ecdsa.P384.verifyHashApi`'s function, as emitted. -/
def p384Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyP384)

/-- `Spec.Ecdsa.P521.verifyHashApi`'s function, as emitted. -/
def p521Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true Impl.Ecdsa.Verify.PPC64LE.verifyP521)

/-- `Spec.Ecdsa.Secp256k1.verifyHashApi`'s function, as emitted. -/
def secp256k1Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifySecp256k1)

/-- `Spec.Ecdsa.BrainpoolP256r1.verifyHashApi`'s function, as emitted. -/
def brainpoolp256r1Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP256r1.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP256r1)

/-- `Spec.Ecdsa.BrainpoolP320r1.verifyHashApi`'s function, as emitted. -/
def brainpoolp320r1Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP320r1.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP320r1)

/-- `Spec.Ecdsa.BrainpoolP384r1.verifyHashApi`'s function, as emitted. -/
def brainpoolp384r1Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP384r1)

/-- `Spec.Ecdsa.BrainpoolP512r1.verifyHashApi`'s function, as emitted. -/
def brainpoolp512r1Verify : Prog isa :=
  scrub 32 112 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v18, .v19]⟩
    (Impl.Ecdsa.PPC64LE.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false Impl.Ecdsa.Verify.PPC64LE.verifyBrainpoolP512r1)

end VG.Impl.Ecdsa.Verify.PPC64LE.Fn

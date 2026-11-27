module

public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.P192.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.P256.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.P521.PPC64LE
public import VerifiedGarbage.Impl.EcKey.Compressed.Secp256k1.PPC64LE
public import VerifiedGarbage.Impl.EcKey.P192.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LEComb
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.PPC64LEComb
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# EcKey on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/EcKey/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `Spec.EcKey.P192.publicKeyApi`'s function, as emitted. -/
def p192PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.PPC64LE.publicKeyP192)

/-- `Spec.EcKey.P192.inst.compressPublicKeyApi`'s function, as emitted. -/
def p192Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressP192)

/-- `Spec.EcKey.P192.inst.decompressPublicKeyApi`'s function, as emitted. -/
def p192Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressP192)

/-- `Spec.EcKey.P224.publicKeyApi`'s function, as emitted. -/
def p224PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyP224Comb)

/-- `Spec.EcKey.P224.inst.compressPublicKeyApi`'s function, as emitted. -/
def p224Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressP224)

/-- `Spec.EcKey.P224.inst.decompressPublicKeyApi`'s function, as emitted. -/
def p224Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressP224)

/-- `Spec.EcKey.P256.publicKeyApi`'s function, as emitted. -/
def p256PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyP256Comb)

/-- `Spec.EcKey.P256.inst.compressPublicKeyApi`'s function, as emitted. -/
def p256Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressP256)

/-- `Spec.EcKey.P256.inst.decompressPublicKeyApi`'s function, as emitted. -/
def p256Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressP256)

/-- `Spec.EcKey.P384.publicKeyApi`'s function, as emitted. -/
def p384PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyP384Comb)

/-- `Spec.EcKey.P384.inst.compressPublicKeyApi`'s function, as emitted. -/
def p384Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressP384)

/-- `Spec.EcKey.P384.inst.decompressPublicKeyApi`'s function, as emitted. -/
def p384Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressP384)

/-- `Spec.EcKey.P521.publicKeyApi`'s function, as emitted. -/
def p521PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyP521Comb)

/-- `Spec.EcKey.P521.inst.compressPublicKeyApi`'s function, as emitted. -/
def p521Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressP521)

/-- `Spec.EcKey.P521.inst.decompressPublicKeyApi`'s function, as emitted. -/
def p521Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressP521)

/-- `Spec.EcKey.Secp256k1.publicKeyApi`'s function, as emitted. -/
def secp256k1PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeySecp256k1Comb)

/-- `Spec.EcKey.Secp256k1.inst.compressPublicKeyApi`'s function, as emitted. -/
def secp256k1Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressSecp256k1)

/-- `Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi`'s function, as emitted. -/
def secp256k1Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressSecp256k1)

/-- `Spec.EcKey.BrainpoolP256r1.publicKeyApi`'s function, as emitted. -/
def brainpoolp256r1PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyBrainpoolP256r1Comb)

/-- `Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi`'s function, as emitted. -/
def brainpoolp256r1Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP256r1)

/-- `Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi`'s function, as emitted. -/
def brainpoolp256r1Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP256r1)

/-- `Spec.EcKey.BrainpoolP320r1.publicKeyApi`'s function, as emitted. -/
def brainpoolp320r1PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyBrainpoolP320r1Comb)

/-- `Spec.EcKey.BrainpoolP384r1.publicKeyApi`'s function, as emitted. -/
def brainpoolp384r1PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyBrainpoolP384r1Comb)

/-- `Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi`'s function, as emitted. -/
def brainpoolp320r1Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP320r1)

/-- `Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi`'s function, as emitted. -/
def brainpoolp384r1Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP384r1)

/-- `Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi`'s function, as emitted. -/
def brainpoolp320r1Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP320r1)

/-- `Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi`'s function, as emitted. -/
def brainpoolp384r1Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP384r1)

/-- `Spec.EcKey.BrainpoolP512r1.publicKeyApi`'s function, as emitted. -/
def brainpoolp512r1PublicKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v18, .v19]⟩
    (Impl.EcKey.PPC64LE.publicKeyBrainpoolP512r1Comb)

/-- `Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi`'s function, as emitted. -/
def brainpoolp512r1Compress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.compressBrainpoolP512r1)

/-- `Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi`'s function, as emitted. -/
def brainpoolp512r1Decompress : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.EcKey.Compressed.PPC64LE.decompressBrainpoolP512r1)

end VG.Impl.EcKey.PPC64LE.Fn

module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P192.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P224.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P256.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P384.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.P521.PPC64LE
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Ecdh on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Ecdh/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `Spec.Ecdh.P192.exchangeApi`'s function, as emitted. -/
def p192Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeP192)

/-- `Spec.Ecdh.P224.exchangeApi`'s function, as emitted. -/
def p224Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeP224)

/-- `Spec.Ecdh.P256.exchangeApi`'s function, as emitted. -/
def p256Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeP256)

/-- `Spec.Ecdh.P384.exchangeApi`'s function, as emitted. -/
def p384Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeP384)

/-- `Spec.Ecdh.P521.exchangeApi`'s function, as emitted. -/
def p521Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeP521)

/-- `Spec.Ecdh.Secp256k1.exchangeApi`'s function, as emitted. -/
def secp256k1Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeSecp256k1)

/-- `Spec.Ecdh.BrainpoolP256r1.exchangeApi`'s function, as emitted. -/
def brainpoolp256r1Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeBrainpoolP256r1)

/-- `Spec.Ecdh.BrainpoolP320r1.exchangeApi`'s function, as emitted. -/
def brainpoolp320r1Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeBrainpoolP320r1)

/-- `Spec.Ecdh.BrainpoolP384r1.exchangeApi`'s function, as emitted. -/
def brainpoolp384r1Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeBrainpoolP384r1)

/-- `Spec.Ecdh.BrainpoolP512r1.exchangeApi`'s function, as emitted. -/
def brainpoolp512r1Exchange : Prog isa :=
  scrub 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Ecdh.PPC64LE.exchangeBrainpoolP512r1)

end VG.Impl.Ecdh.PPC64LE.Fn

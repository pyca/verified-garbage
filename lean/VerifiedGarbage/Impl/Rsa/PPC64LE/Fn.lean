module

public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PrivPre
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CheckKey
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Impl.Rsa.PPC64LE.RecoverDet
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# Rsa on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/Rsa/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_rsa_public_precompute`, as emitted. -/
def publicPrecompute : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Bignum.PPC64LE.Precompute.precompute)

/-- `vg_rsa_private_precompute`, as emitted. -/
def privatePrecompute : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.Bignum.PPC64LE.PrivPre.code)

/-- `vg_rsa_crt_values`, as emitted. -/
def crtValues : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Rsa.PPC64LE.CrtValues.code)

/-- `vg_rsa_check_key`, as emitted. -/
def checkKey : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Rsa.PPC64LE.CheckKey.code)

/-- `vg_rsa_recover_primes_det`, as emitted. -/
def recoverPrimesDet : Prog isa :=
  scrubAll 32 0 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, []⟩
    (Impl.Rsa.PPC64LE.RecoverDet.code)

end VG.Impl.Rsa.PPC64LE.Fn

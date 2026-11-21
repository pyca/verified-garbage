module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Sign
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# RsaPkcs1Sig on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrubAll`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/RsaPkcs1Sig/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Sig.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)

/-- `vg_rsa_pkcs1_verify_precomputed`, as emitted. -/
def verifyPrecomputed : Prog isa :=
  scrubAll 32 2224 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.RsaPkcs1Sig.PPC64LE.Precomputed.code)

/-- `vg_rsa_pkcs1_recover_precomputed`, as emitted. -/
def recoverPrecomputed : Prog isa :=
  scrubAll 32 2224 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.RsaPkcs1Sig.PPC64LE.RecoverPrecomputed.code)

/-- `vg_rsa_pkcs1_sign_precomputed`, as emitted. -/
def signPrecomputed : Prog isa :=
  scrubAll 32 4608 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.RsaPkcs1Sig.PPC64LE.Sign.codeP)

end VG.Impl.RsaPkcs1Sig.PPC64LE.Fn

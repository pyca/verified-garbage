module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Decrypt
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Random
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-!
# RsaPkcs1Enc on PPC64LE: the functions as emitted

Each function followed by its cleanup (`Impl.Scrub.PPC64LE.scrub`): the
result's bits, the bytes of stack its frames use, which the cleanup zeroes
(none for a function that wipes its own frame before it releases it), and the
volatile registers it writes, which the cleanup clears, so that it returns
without secret residue (`Proof/RsaPkcs1Enc/PPC64LE/Scrub.lean`).
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.PPC64LE.Fn

open VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrub)

/-- `vg_rsa_pkcs1_decrypt_precomputed`, as emitted. -/
def decryptPrecomputed : Prog isa :=
  scrub 32 3648 Impl.Scrub.PPC64LE.Clear.all
    (Impl.RsaPkcs1Enc.PPC64LE.Decrypt.codeP)

/-- `vg_rsa_pkcs1_encrypt_random`, as emitted. -/
def encryptRandom : Prog isa :=
  scrub 32 3440 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], true, [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10]⟩
    (Impl.RsaPkcs1Enc.PPC64LE.Random.code)

end VG.Impl.RsaPkcs1Enc.PPC64LE.Fn

module

public import VerifiedGarbage.Proof.Variants.Sha256.X86.Scalar

/-!
# SHA-256 on x86: the scalar compression function

A variant of `Sha256` on x86 (see `TCB/Emit.lean`): `vg_sha256_compress`, in
the baseline ISA, the streaming `update` and `finalize` made with it, which
HMAC's and PBKDF2's functions call (`Generic/Sha256/X86/`), and SHA-224's
`finalize`.
-/

@[expose] public section

namespace VG.Variants.Sha256.X86.Scalar

def variant : Proof.Sha256.X86.Variants.Backend := Proof.Variants.Sha256.X86.Scalar.variant

end VG.Variants.Sha256.X86.Scalar

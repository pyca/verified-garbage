module

public import VerifiedGarbage.Proof.Variants.Sha1.X86.Scalar

/-!
# SHA-1 on x86: the scalar compression function

A variant of `Sha1` on x86 (see `TCB/Emit.lean`): `vg_sha1_compress`, in the
baseline ISA, and the streaming `update` and `finalize` made with it, which
HMAC's and PBKDF2's functions call (`Generic/Sha1/X86/`).
-/

@[expose] public section

namespace VG.Variants.Sha1.X86.Scalar

def variant : Proof.Sha1.X86.Variants.Backend := Proof.Variants.Sha1.X86.Scalar.variant

end VG.Variants.Sha1.X86.Scalar

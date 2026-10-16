module

public import VerifiedGarbage.Proof.Variants.Sha256.X86.ShaNi

/-!
# SHA-256 on x86 with the SHA extensions

A variant of `Sha256` on x86 (see `TCB/Emit.lean`): `vg_sha256_compress_shani`,
which needs the SHA extensions and SSSE3, and the streaming `update` and
`finalize` made with it, which HMAC's and PBKDF2's functions call
(`Generic/Sha256/X86/`), and SHA-224's `finalize`.
-/

@[expose] public section

namespace VG.Variants.Sha256.X86.ShaNi

def variant : Proof.Sha256.X86.Variants.Backend := Proof.Variants.Sha256.X86.ShaNi.variant

end VG.Variants.Sha256.X86.ShaNi

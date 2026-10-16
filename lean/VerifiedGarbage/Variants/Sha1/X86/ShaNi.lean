module

public import VerifiedGarbage.Proof.Variants.Sha1.X86.ShaNi

/-!
# SHA-1 on x86 with the SHA extensions

A variant of `Sha1` on x86 (see `TCB/Emit.lean`): `vg_sha1_compress_shani`,
which needs the SHA extensions and SSSE3, and the streaming `update` and
`finalize` made with it, which HMAC's and PBKDF2's functions call
(`Generic/Sha1/X86/`).
-/

@[expose] public section

namespace VG.Variants.Sha1.X86.ShaNi

def variant : Proof.Sha1.X86.Variants.Backend := Proof.Variants.Sha1.X86.ShaNi.variant

end VG.Variants.Sha1.X86.ShaNi

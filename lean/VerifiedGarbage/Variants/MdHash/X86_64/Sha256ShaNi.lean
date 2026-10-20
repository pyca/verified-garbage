module

public import VerifiedGarbage.Proof.Variants.MdHash.X86_64.Sha256ShaNi

/-!
# SHA-256 on x86-64 with the SHA extensions

A variant of `MdHash` on x86-64 (see `TCB/Emit.lean`): SHA-256, with `vg_sha256_compress_shani`, which needs the SHA extensions and SSSE3.
-/

@[expose] public section

namespace VG.Variants.MdHash.X86_64.Sha256ShaNi

def variant : Proof.Pbkdf2.Md.X86_64.MdHash := Proof.Variants.MdHash.X86_64.Sha256ShaNi.variant

end VG.Variants.MdHash.X86_64.Sha256ShaNi

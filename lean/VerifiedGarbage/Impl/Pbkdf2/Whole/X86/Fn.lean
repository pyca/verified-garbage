module

public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# PBKDF2 on x86 (32-bit): the functions as emitted

`vg_pbkdf2_hmac_<hash>`, the whole of PBKDF2 over the functions `F` it calls
(`Impl.Pbkdf2.Whole.X86.Fns.pbkdf2`) with its working space in a frame of its
own (`withStackScratch`), followed by its cleanup (`Impl.Scrub.X86.scrubF 0 W`):
the `W` bytes of stack below `esp` that it and the functions it calls use
zeroed, and the registers a callee may change cleared, so that it returns
without secret residue. It returns no result. The frame and `W` depend only on
the hash function's sizes: one definition serves SHA-224 and SHA-256, and one
the SHA-512 family.
-/

@[expose] public section

namespace VG.Impl.Pbkdf2.Whole.X86.Fn

open VG.X86
open VG.Impl.StackScratch.X86 (withStackScratch)

/-- `vg_pbkdf2_hmac_md5`, as emitted. -/
def md5 (F : Fns) : Prog isa := Impl.Scrub.X86.scrubF 0 1136 (withStackScratch 1060 7 F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha1`, as emitted. -/
def sha1 (F : Fns) : Prog isa := Impl.Scrub.X86.scrubF 0 1232 (withStackScratch 1156 7 F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha224` and `vg_pbkdf2_hmac_sha256`, as emitted. -/
def sha256 (F : Fns) : Prog isa := Impl.Scrub.X86.scrubF 0 1712 (withStackScratch 1636 7 F.pbkdf2)

/-- `vg_pbkdf2_hmac_sha384`, `vg_pbkdf2_hmac_sha512`, `vg_pbkdf2_hmac_sha512_224` and
`vg_pbkdf2_hmac_sha512_256`, as emitted. -/
def sha512 (F : Fns) : Prog isa := Impl.Scrub.X86.scrubF 0 3520 (withStackScratch 3444 7 F.pbkdf2)

end VG.Impl.Pbkdf2.Whole.X86.Fn

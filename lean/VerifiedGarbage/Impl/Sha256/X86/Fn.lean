module

public import VerifiedGarbage.Impl.Sha256.X86.Stream
public import VerifiedGarbage.Impl.MdStream.X86.Digest
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# SHA-224 and SHA-256 on x86 (32-bit): the functions as emitted

`vg_sha224_init` and `vg_sha256_init`, which call nothing and have no frame,
followed by the clearing of the registers a callee may change
(`Impl.Scrub.X86.scrub 0`); `vg_sha224_digest` and `vg_sha256_digest`, the
one-shot digest (`Impl.MdStream.X86.Digest`) over a backend's streaming
functions `H`, followed by the zeroing of the stack below `esp` that it and
its callees use, its frame (`dframe H`) and 48 bytes more, and that clearing
(`Impl.Scrub.X86.scrubAll 0`), so that each returns without secret residue;
and `vg_sha256_update`, `vg_sha256_finalize` and `vg_sha224_finalize`, a
backend's streaming functions in a frame of working space
(`Impl.StackScratch.X86.withStackScratch`), followed by the zeroing of the
stack they and their callees use and that clearing.
-/

@[expose] public section

namespace VG.Impl.Sha256.X86.Fn

open VG.X86

/-- `vg_sha224_init`, as emitted. -/
def init224 : Prog isa := Impl.Scrub.X86.scrub 0 Stream.init224

/-- `vg_sha256_init`, as emitted. -/
def init : Prog isa := Impl.Scrub.X86.scrub 0 Stream.init

/-- `vg_sha224_digest` and `vg_sha256_digest` over the streaming functions `H`, as
emitted. -/
def digest (H : Impl.Pbkdf2.Stream.X86.Hash) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 (48 + Impl.MdStream.X86.Digest.dframe H) (Impl.MdStream.X86.Digest.digest H)

/-- `vg_sha256_update` over a backend's streaming `update` `c`, as emitted. -/
def update (c : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 (20 + 636) (Impl.StackScratch.X86.withStackScratch 636 5 c)

/-- `vg_sha256_finalize` over a backend's streaming `finalize` `c`, as emitted. -/
def finalize (c : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 (20 + 632) (Impl.StackScratch.X86.withStackScratch 632 4 c)

/-- `vg_sha224_finalize` over a backend's compression function `cmpN`/`cmpC`, as
emitted. -/
def finalize224 (cmpN : String) (cmpC : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 (20 + 632)
    (Impl.StackScratch.X86.withStackScratch 632 4 (Stream.finalize224 cmpN cmpC))

end VG.Impl.Sha256.X86.Fn

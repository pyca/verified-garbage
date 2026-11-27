module

public import VerifiedGarbage.Impl.Sha1.X86.Stream
public import VerifiedGarbage.Impl.MdStream.X86.Digest
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Impl.Scrub.X86.Sel
public import VerifiedGarbage.Impl.StackScratch.X86

/-!
# SHA-1 on x86 (32-bit): the functions as emitted

`vg_sha1_init`, which calls nothing and has no frame, followed by the
clearing of the registers a callee may change (`Impl.Scrub.X86.scrub 0`);
`vg_sha1_digest`, the one-shot digest (`Impl.MdStream.X86.Digest`) over a
backend's streaming functions `H`, followed by the zeroing of the doublewords
of the stack below `esp` (its frame, `dframe H`, and 48 bytes more) that the
residue analysis finds it may leave secret
(`Impl.MdStream.X86.Digest.selWords`), and that clearing
(`Impl.Scrub.X86.scrubSel 0`), so that each returns without secret residue.
`vg_sha1_update` and `vg_sha1_finalize`, a backend's streaming `update` and
`finalize` in a frame of working space (`Impl.StackScratch.X86.withStackScratch`),
followed by the zeroing of the stack they and their callees use and that
clearing.
-/

@[expose] public section

namespace VG.Impl.Sha1.X86.Fn

open VG.X86

/-- `vg_sha1_init`, as emitted. -/
def init : Prog isa := Impl.Scrub.X86.scrub 0 Stream.init

/-- `vg_sha1_digest` over the streaming functions `H`, as emitted. -/
def digest (H : Impl.Pbkdf2.Stream.X86.Hash) : Prog isa :=
  Impl.Scrub.X86.scrubSel 0 (48 + Impl.MdStream.X86.Digest.dframe H) Impl.MdStream.X86.Digest.selWords
    (Impl.MdStream.X86.Digest.digest H)

/-- `vg_sha1_update` over a backend's streaming `update` `c`, as emitted. -/
def update (c : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 (20 + 188) (Impl.StackScratch.X86.withStackScratch 188 5 c)

/-- `vg_sha1_finalize` over a backend's streaming `finalize` `c`, as emitted. -/
def finalize (c : Prog isa) : Prog isa :=
  Impl.Scrub.X86.scrubAll 0 (20 + 184) (Impl.StackScratch.X86.withStackScratch 184 4 c)

end VG.Impl.Sha1.X86.Fn

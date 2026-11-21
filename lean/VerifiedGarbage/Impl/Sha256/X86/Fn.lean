module

public import VerifiedGarbage.Impl.Sha256.X86.Stream
public import VerifiedGarbage.Impl.MdStream.X86.Digest
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# SHA-224 and SHA-256 on x86 (32-bit): the functions as emitted

`vg_sha224_init` and `vg_sha256_init`, which call nothing and have no frame,
followed by the clearing of the registers a callee may change
(`Impl.Scrub.X86.scrub 0`); `vg_sha224_digest` and `vg_sha256_digest`, the
one-shot digest (`Impl.MdStream.X86.Digest`) over a backend's streaming
functions `H`, followed by the zeroing of the stack below `esp` that it and
its callees use, its frame (`dframe H`) and 48 bytes more, and that clearing
(`Impl.Scrub.X86.scrubAll 0`), so that each returns without secret residue. The
streaming `update` and `finalize` of each backend are registered by the
backend's interface (`Proof.Sha256.X86.Variants.StreamFn.reg`).
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

end VG.Impl.Sha256.X86.Fn

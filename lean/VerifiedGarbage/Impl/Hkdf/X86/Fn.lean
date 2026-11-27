module

public import VerifiedGarbage.Impl.Hkdf.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # HKDF on x86 (32-bit): the functions as emitted

Each function's code, which calls HMAC through its table (the functions `f`
an indirect call of the table's may reach), then its cleanup
(`Impl.Scrub.X86.scrubAll`): the registers a callee may change cleared
(they return nothing), and the stack its contract gives it zeroed: its
frame, and the bytes below it that the functions it calls use. -/

@[expose] public section

namespace VG.Impl.Hkdf.X86.Fn

open VG VG.X86
open VG.Impl.Scrub.X86 (scrubAll)
open VG.Impl.Ecdsa.Rfc6979.X86 (Fns)

/-- `vg_hkdf_key` as emitted: its frame and the 100 bytes `init` uses below it. -/
def key (f : Fns) : Prog isa := scrubAll 0 (kFr + 100) (Impl.Hkdf.X86.key f)

/-- `vg_hkdf_extract` as emitted: its frame and the 100 bytes `init` uses
below it. -/
def extract (f : Fns) : Prog isa := scrubAll 0 (xFr + 100) (Impl.Hkdf.X86.extract f)

/-- `vg_hkdf_expand` as emitted: its frame and the 76 bytes `finalize` uses
below it. -/
def expand (f : Fns) : Prog isa := scrubAll 0 (eFr + 76) (Impl.Hkdf.X86.expand f)

end VG.Impl.Hkdf.X86.Fn

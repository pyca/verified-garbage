module

public import VerifiedGarbage.Impl.Hkdf.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # HKDF on x86-64: the functions as emitted

Each function's code, which calls HMAC through its table (the functions `f`
an indirect call of the table's may reach), then its cleanup
(`Impl.Scrub.X86_64.scrubAll`, at the level `sse` of the baseline ISA): the
caller-saved registers cleared (they return nothing), and the stack its
contract gives it zeroed: its frame, and the bytes below it that the
functions it calls use. -/

@[expose] public section

namespace VG.Impl.Hkdf.X86_64.Fn

open VG VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-- `vg_hkdf_key` as emitted: its frame, its return address and the 24 bytes
`init` uses below its own. -/
def key (f : Fns) : Prog isa := scrubAll .sse 0 (kFr + 32) (Impl.Hkdf.X86_64.key f)

/-- `vg_hkdf_extract` as emitted: its frame, its return address and the 24
bytes `init` uses below its own. -/
def extract (f : Fns) : Prog isa := scrubAll .sse 0 (xFr + 32) (Impl.Hkdf.X86_64.extract f)

/-- `vg_hkdf_expand` as emitted: its frame, its return address and the 24
bytes the functions it calls use below their own. -/
def expand (f : Fns) : Prog isa := scrubAll .sse 0 (eFr + 32) (Impl.Hkdf.X86_64.expand f)

end VG.Impl.Hkdf.X86_64.Fn

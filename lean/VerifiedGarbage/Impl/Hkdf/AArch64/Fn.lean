module

public import VerifiedGarbage.Impl.Hkdf.AArch64
public import VerifiedGarbage.Impl.Scrub.AArch64.Writes

/-! # HKDF on AArch64: the functions as emitted

Each function's code, which calls HMAC through its table (the functions `f`
an indirect call of the table's may reach), then its cleanup (`scrubOf`):
the registers the code may write cleared, the functions it calls included
(they return nothing), and the stack it uses zeroed: the return address it
pushes, its frame, and the 16 bytes below it that the functions it calls
use. -/

@[expose] public section

namespace VG.Impl.Hkdf.AArch64.Fn

open VG VG.AArch64
open VG.Impl.Scrub.AArch64 (scrubOf)
open VG.Impl.RsaOaep.AArch64.Mgf1.Table (Fns)

/-- `vg_hkdf_key` as emitted. -/
def key (f : Fns) : Prog isa := scrubOf (kFr + 32) 0 (Impl.Hkdf.AArch64.key f)

/-- `vg_hkdf_extract` as emitted. -/
def extract (f : Fns) : Prog isa := scrubOf (xFr + 32) 0 (Impl.Hkdf.AArch64.extract f)

/-- `vg_hkdf_expand` as emitted. -/
def expand (f : Fns) : Prog isa := scrubOf (eFr + 32) 0 (Impl.Hkdf.AArch64.expand f)

end VG.Impl.Hkdf.AArch64.Fn

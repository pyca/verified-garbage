module

public import VerifiedGarbage.Impl.Hkdf.PPC64LE
public import VerifiedGarbage.Impl.Scrub.PPC64LE

/-! # HKDF on PPC64LE: the functions as emitted

Each function's code, which calls HMAC through its table (the functions `f`
an indirect call of the table's may reach), then its cleanup
(`Impl.Scrub.PPC64LE.scrubAll`): the volatile registers cleared (they return
nothing), and the stack its frame and the functions it calls use zeroed:
for `key` and `extract`, the frame and the 144 bytes below it that HMAC's
`init` for a key of any length uses (for a key longer than a block); for
`expand`, the frame and the 96 bytes HMAC's `finalize` uses. -/

@[expose] public section

namespace VG.Impl.Hkdf.PPC64LE.Fn

open VG VG.PPC64LE
open VG.Impl.Scrub.PPC64LE (scrubAll)
open VG.Impl.RsaOaep.PPC64LE (Fns)

/-- `vg_hkdf_key` as emitted. -/
def key (f : Fns) : Prog isa := scrubAll 0 (kFr + 144) .all (Impl.Hkdf.PPC64LE.key f)

/-- `vg_hkdf_extract` as emitted. -/
def extract (f : Fns) : Prog isa := scrubAll 0 (xFr + 144) .all (Impl.Hkdf.PPC64LE.extract f)

/-- `vg_hkdf_expand` as emitted. -/
def expand (f : Fns) : Prog isa := scrubAll 0 (eFr + 96) .all (Impl.Hkdf.PPC64LE.expand f)

end VG.Impl.Hkdf.PPC64LE.Fn

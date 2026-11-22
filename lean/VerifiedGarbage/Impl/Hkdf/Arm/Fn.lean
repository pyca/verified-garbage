module

public import VerifiedGarbage.Impl.Hkdf.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-! # HKDF on 32-bit ARM: the functions as emitted

Each function's code, which calls HMAC through its table (the functions `f`
an indirect call of the table's may reach), then the instructions that zero
the stack its contract reserves (its frame and the 32 bytes below it that
the functions it calls use) and set the registers a callee may change and
the flags to constants (`Impl.Scrub.Arm.scrubAll`). -/

@[expose] public section

namespace VG.Impl.Hkdf.Arm.Fn

open VG VG.Arm
open VG.Impl.Scrub.Arm (scrubAll)
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)

/-- `vg_hkdf_key` as emitted. -/
def key (f : Fns) : Prog isa := scrubAll 0 (kFr + 32) (Impl.Hkdf.Arm.key f)

/-- `vg_hkdf_extract` as emitted. -/
def extract (f : Fns) : Prog isa := scrubAll 0 (xFr + 32) (Impl.Hkdf.Arm.extract f)

/-- `vg_hkdf_expand` as emitted. -/
def expand (f : Fns) : Prog isa := scrubAll 0 (eFr + 32) (Impl.Hkdf.Arm.expand f)

end VG.Impl.Hkdf.Arm.Fn

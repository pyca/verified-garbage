module

public import VerifiedGarbage.Impl.AesXts.X86_64Unit
public import VerifiedGarbage.Impl.AesXts.X86_64UnitTo
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-XTS's data-unit functions on x86-64: the functions as emitted

Each, over the implementations it calls, then its cleanup
(`Impl.Scrub.X86_64.scrubAll v 0 n`): every vector register at the level
`v` and every caller-saved register cleared, and its whole stack wiped.
-/

@[expose] public section

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

namespace VG.Impl.AesXts.X86_64Unit.Fn

/-- `vg_aes_xts_encrypt_unit`, as emitted. -/
def encrypt (v : VecLevel) (x : Xts) : Prog isa := scrubAll v 0 16 (X86_64Unit.encrypt x)

/-- `vg_aes_xts_decrypt_unit`, as emitted. -/
def decrypt (v : VecLevel) (x : Xts) : Prog isa := scrubAll v 0 16 (X86_64Unit.decrypt x)

end VG.Impl.AesXts.X86_64Unit.Fn

namespace VG.Impl.AesXts.X86_64UnitTo.Fn

/-- `vg_aes_xts_encrypt_unit_to`, as emitted. -/
def encrypt (v : VecLevel) (x : X86_64Unit.Xts) (y : XtsTo) : Prog isa :=
  scrubAll v 0 24 (X86_64UnitTo.encrypt x y)

/-- `vg_aes_xts_decrypt_unit_to`, as emitted. -/
def decrypt (v : VecLevel) (x : X86_64Unit.Xts) (y : XtsTo) : Prog isa :=
  scrubAll v 0 24 (X86_64UnitTo.decrypt x y)

end VG.Impl.AesXts.X86_64UnitTo.Fn

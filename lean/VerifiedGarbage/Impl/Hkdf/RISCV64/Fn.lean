module

public import VerifiedGarbage.Impl.Hkdf.RISCV64
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-! # HKDF on RISC-V: the functions as emitted

Each function's code, which calls HMAC through its table (the functions `f`
an indirect call of the table's may reach), then its cleanup
(`Impl.Scrub.RISCV64.scrubAll`): the caller-saved registers cleared (they
return nothing), and the stack it uses zeroed: its frame, and at most 512
bytes below it for the functions it calls. -/

@[expose] public section

namespace VG.Impl.Hkdf.RISCV64.Fn

open VG VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrubAll)
open VG.Impl.Ecdsa.Rfc6979.RISCV64 (Fns)

/-- `vg_hkdf_key` as emitted. -/
def key (f : Fns) : Prog isa := scrubAll 0 (kFr + 512) (Impl.Hkdf.RISCV64.key f)

/-- `vg_hkdf_extract` as emitted. -/
def extract (f : Fns) : Prog isa := scrubAll 0 (xFr + 512) (Impl.Hkdf.RISCV64.extract f)

/-- `vg_hkdf_expand` as emitted. -/
def expand (f : Fns) : Prog isa := scrubAll 0 (eFr + 512) (Impl.Hkdf.RISCV64.expand f)

end VG.Impl.Hkdf.RISCV64.Fn

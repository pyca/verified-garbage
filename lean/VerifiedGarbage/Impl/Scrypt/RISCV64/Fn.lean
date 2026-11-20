module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.Scrypt
public import VerifiedGarbage.Impl.Scrub.RISCV64

/-!
# scrypt on RISC-V: the function as emitted

`vg_scrypt`, calling the implementation `pbk` of PBKDF2-HMAC-SHA256 named
`pbkName`, then its cleanup (`Impl.Scrub.RISCV64.scrub`): the caller-saved
registers cleared (it returns nothing), and the 1248 bytes of stack its
frames and those of the functions it calls use zeroed. Its arguments on the
stack are in the caller's frame, among the buffers, which the caller owns.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64.Fn

open VG.RISCV64
open VG.Impl.Scrub.RISCV64 (scrub)

/-- `vg_scrypt`, calling `pbk` (named `pbkName`), as emitted. -/
def scrypt (pbkName : String) (pbk : Prog isa) : Prog isa :=
  scrub 0 1248 (Impl.Scrypt.RISCV64.Whole.scrypt pbkName pbk)

end VG.Impl.Scrypt.RISCV64.Fn

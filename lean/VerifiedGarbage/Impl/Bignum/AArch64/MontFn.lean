module

public import VerifiedGarbage.Impl.Bignum.AArch64

@[expose] public section

namespace VG.Impl.Bignum.AArch64.MontFn
open VG.AArch64 VG.Impl.Bignum

/-- Load an array pointer indexed by a public 32-bit argument. -/
def loadArray (d i : Reg) : List Instr := [
  .lsl .x i i 3,
  .add .x i .x0 i,
  .ldr .x d i 64]

/-- Ignore the unspecified upper halves of 32-bit arguments. -/
def zext : List Instr := [.addImm .w .x2 .x2 0, .addImm .w .x3 .x3 0, .addImm .w .x4 .x4 0]

/-- The same register layout as `bases`, with indices passed at run time. -/
def basesTail : List Instr :=
  loadArray .x5 .x2 ++ loadArray .x11 .x3 ++ loadArray .x9 .x4 ++
  [ldh .x8 (sArr 2), ldh .x10 (sArr 0), ldh .x6 (sArr 3),
    ldh .x12 sW, ldh .x15 sMinv, movi .x7 0]

def basesR : List Instr := zext ++ basesTail

/-- AAPCS64 `vg_rsa_mont_mul(ws, ws_len, o, a, b)`, no stack or saved registers. -/
def mulBase : Prog isa :=
  .seq (.block basesR) (.seq zeroAcc (.seq rounds (.seq subMod selectAcc)))

end VG.Impl.Bignum.AArch64.MontFn

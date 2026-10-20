module

public import VerifiedGarbage.Impl.Bignum.AArch64.ProductDispatch

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

/-- Recognize the public in-place accumulator-square call used by FFDH.
Only the low 32 bits of the indices belong to the ABI arguments. -/
def squareTest : List Instr :=
  [movi .x7 5, .logic .eor .w .x5 .x2 .x7, .logic .eor .w .x6 .x3 .x7,
   .logic .orr .w .x5 .x5 .x6, .logic .eor .w .x6 .x4 .x7,
   .logic .orr .w .x5 .x5 .x6]

/-- Reuse RSA's scheduled eight-limb kernel for accumulator squares;
retain the general callable implementation for every other valid index tuple. -/
def mul : Prog isa :=
  .seq (.block squareTest)
    (.ite (.zero .w .x5) (SquareEightDispatch.mm 5 5 5) mulBase)

/-- Recognize the public accumulator-times-window tuple. -/
def productTest : List Instr :=
  [movi .x7 5, .logic .eor .w .x5 .x2 .x7, .logic .eor .w .x6 .x3 .x7,
   .logic .orr .w .x5 .x5 .x6, movi .x7 6, .logic .eor .w .x6 .x4 .x7,
   .logic .orr .w .x5 .x5 .x6]

/-- Scheduled products for window multiplication; preserve all other paths. -/
def mulProduct : Prog isa :=
  .seq (.block productTest)
    (.ite (.zero .w .x5) (ProductDispatch.mm 5 5 6) mul)

end VG.Impl.Bignum.AArch64.MontFn

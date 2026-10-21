module

import VerifiedGarbage.Impl.Bignum.Arm.DownRow
public import VerifiedGarbage.Impl.Bignum.Arm.RowUmaal
public import VerifiedGarbage.Impl.Bignum.Arm.Row

/-! The downward-write row uses UMAAL and reconstructs baseline scratch registers once. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.DownRow
open VG VG.Arm VG.Impl.Bignum.Arm

def stepU : List Instr :=
  [.ldr .r2 .r12 0, .ldr .r3 .r0 4, .mov .r5 (.reg .r3),
   .umaal .r3 .r11 .r2 .r9, .str .r3 .r0 0]

def bodyU : Prog isa := .seq (.block stepU) (.block rowAdvance)
def loopU : Prog isa := .loop bodyU .ne

def coreU : Prog isa := .seq (.block rowUJoin) (.seq loopU (.block rowUEnd))
def codeU : Prog isa := .seq (.block rowSplit) (.seq coreU (.block rowJoin))

end VG.Impl.Bignum.Arm.DownRow

module

public import VerifiedGarbage.TCB.Arm.Isa

/-! Skip public leading zero exponent bytes, retaining at least one byte.
The base pointer/count are restored and packed domain storage is untouched. -/

@[expose] public section
namespace VG.Impl.Ffdh.Arm.PublicScan
open VG VG.Arm

-- The same public-bound scanner used by GenerateKey, in its r4/r6 registers.
def advance : Prog isa := .block [
  .dp .add .r4 .r4 (.imm 1), .dp .sub .r6 .r6 (.imm 1),
  .mov .r11 (.imm 1), .cmp .r11 (.imm 0)]
def stop : Prog isa := .block [.mov .r11 (.imm 0), .cmp .r11 (.imm 0)]
def step : Prog isa := .seq (.block [.ldrb .r3 .r4 0, .cmp .r3 (.imm 0)])
  (.ite .eq (.seq (.block [.cmp .r6 (.imm 1)]) (.ite .ne advance stop)) stop)
def scan : Prog isa := .loop step .ne

def enter : List Instr := [
  .mov .r8 (.reg .r4), .mov .r9 (.reg .r6),
  .mov .r4 (.reg .r1), .mov .r6 (.reg .r2)]
def leave : List Instr := [
  .mov .r1 (.reg .r4), .mov .r2 (.reg .r6),
  .mov .r4 (.reg .r8), .mov .r6 (.reg .r9)]

/-- Trim only the public exponent in r1/r2; preserve the base in r4/r6. -/
def code : Prog isa := .seq (.block enter) (.seq scan (.block leave))

end VG.Impl.Ffdh.Arm.PublicScan

module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialOfb

/-! # Serial CBC encryption with prepared SM4 keys -/

@[expose] public section
namespace VG.Impl.Sm4.Arm.SerialCbc

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Sm4.Arm
open VG.Impl.Modes.Arm (copyWord xorWord)

def xorInput : List Instr := (List.range 4).flatMap (xorWord sb .r6 (4 * tailSlot) 0)
def fill : Prog isa := .seq (.block BatchCfb.first) (.block xorInput)
def copyOutput : List Instr := (List.range 4).flatMap (copyWord .r6 sb 0 (4 * tailSlot))
def advance : List Instr := [.dp .add .r6 .r6 (.imm 16), .subs .r7 .r7 (.reg .r11)]
def core : Prog isa := .seq fill BatchCtr.crypt
def tail : Prog isa := .seq (.block copyOutput) (.seq (.block SerialOfb.saveFeedback) (.block advance))
/-- Keep the Thumb round loop word-aligned. -/
def count : Prog isa := .seq SerialCfb.count (.block BatchCfb.pad)
def group : Prog isa := .seq count (.seq core tail)
def dataLoop : Prog isa := .ite .eq (.block []) (.loop group .ne)
def encrypt : Prog isa := .seq BatchCtr.prologue (.seq dataLoop BatchCtr.finish)

end VG.Impl.Sm4.Arm.SerialCbc

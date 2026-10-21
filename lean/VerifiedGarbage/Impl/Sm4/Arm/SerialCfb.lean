module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCfb

/-! # Serial CFB encryption with one preparation of the SM4 round keys -/

@[expose] public section
namespace VG.Impl.Sm4.Arm.SerialCfb

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Sm4.Arm
open VG.Impl.Modes.Arm (copyWord)

/-- The batch has advanced `r6`; retain its output for the next feedback. -/
def saveCipher : List Instr :=
  [.dp .sub .r0 .r6 (.imm 16)] ++
    (List.range 4).flatMap (copyWord sb .r0 (4 * BatchCtr.counterSlot) 0)

/-- Keep the Thumb cipher round loop word-aligned. -/
def count : Prog isa := .seq (.block [.mov .r11 (.imm 1)]) (.block BatchCfb.pad)

def group : Prog isa := .seq count
  (.seq BatchCfb.batch (.seq (.block saveCipher) (.block [.subs .r7 .r7 (.reg .r11)])))

def dataLoop : Prog isa := .ite .eq (.block []) (.loop group .ne)
def encrypt : Prog isa := .seq BatchCtr.prologue (.seq dataLoop BatchCtr.finish)

end VG.Impl.Sm4.Arm.SerialCfb

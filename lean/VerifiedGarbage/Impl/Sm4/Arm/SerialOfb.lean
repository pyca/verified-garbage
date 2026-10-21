module

public import VerifiedGarbage.Impl.Sm4.Arm.SerialCfb

/-! # Serial OFB with one preparation of the SM4 round keys -/

@[expose] public section
namespace VG.Impl.Sm4.Arm.SerialOfb

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Sm4.Arm
open VG.Impl.Modes.Arm (copyWord)

/-- Retain the encrypted feedback block as the next input. -/
def saveFeedback : List Instr :=
  (List.range 4).flatMap (copyWord sb sb (4 * BatchCtr.counterSlot) (4 * tailSlot))

def group : Prog isa := .seq SerialCfb.count
  (.seq BatchCfb.batch (.seq (.block saveFeedback) (.block [.subs .r7 .r7 (.reg .r11)])))

def dataLoop : Prog isa := .ite .eq (.block []) (.loop group .ne)
def crypt : Prog isa := .seq BatchCtr.prologue (.seq dataLoop BatchCtr.finish)

end VG.Impl.Sm4.Arm.SerialOfb

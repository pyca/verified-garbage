module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr
public import VerifiedGarbage.Impl.Modes.Arm.Counter32
public import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# SM4 counter mode with GCM's `inc₃₂`, in eight-block batches on ARMv7

`BatchCtr`'s code with the running counter stepped by GCM's `inc₃₂`
(`inc32At`) instead of a 128-bit increment: the same entry, key preparation,
batches of up to eight counters encrypted together, XOR and exit.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm.BatchCtr32

open VG.Arm VG.Impl.Aes.Arm
open VG.Impl.Modes.Arm (copyWord inc32At)

/-- Fill one lane and step the running counter by `inc₃₂`. -/
def fillBody : List Instr :=
  (List.range 4).flatMap (copyWord .r0 sb 0 (4 * BatchCtr.counterSlot)) ++ inc32At sb (4 * BatchCtr.counterSlot) ++
    [.dp .add .r0 .r0 (.imm 16), .subs .r1 .r1 (.imm 1)]

def fill : Prog isa :=
  .seq (.block [tailAddr .r0, movR .r1 .r11]) (.loop (.block fillBody) .ne)

def batch : Prog isa := .seq fill (.seq BatchCtr.crypt BatchCtr.xorGroup)

def group : Prog isa :=
  .seq BatchCtr.count (.seq batch (.block [.subs .r7 .r7 (.reg .r11)]))

def dataLoop : Prog isa := .ite .eq (.block []) (.loop group .ne)

def ctr32 : Prog isa := .seq BatchCtr.prologue (.seq dataLoop BatchCtr.finish)

/-- `vg_sm4_ctr32`: `ctr32` with its 1512 bytes of working space on the stack,
zeroed on return. -/
def ctr32Framed : Prog isa := Impl.StackScratch.Arm.withStackScratchWiped 1520 0 378 ctr32

end VG.Impl.Sm4.Arm.BatchCtr32

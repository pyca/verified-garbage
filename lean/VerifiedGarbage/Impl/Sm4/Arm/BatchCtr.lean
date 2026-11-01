module

public import VerifiedGarbage.Impl.Sm4.Arm.Prepared
public import VerifiedGarbage.Impl.Modes.Arm.Seq

/-!
# SM4-CTR in eight-block batches on ARMv7

The key table is prepared once. Each group fills the tail buffer with up
to eight counters, encrypts them together, and XORs the outputs into the
data. The running counter is secret; every loop count and address is public.
-/

@[expose] public section

namespace VG.Impl.Sm4.Arm.BatchCtr

open VG.Arm VG.Impl.Aes.Arm
open VG.Impl.Modes.Arm (copyWord xorWord incAt)

/-- Saved registers follow the cipher's working space. -/
def savedSlot : Nat := slots
/-- Four words for the running counter follow the nine saved registers. -/
def counterSlot : Nat := slots + 9
/-- Rounded to whole 64-bit words. -/
def totalSlots : Nat := slots + 14

def modeSaved : List (Reg × Nat) := savedRegs.map fun (r, k) => (r, 4 * (savedSlot + k - Arm.savedSlot))
def save : List Instr := modeSaved.map fun p => .str p.1 .r12 p.2
def restore : List Instr := modeSaved.map fun p => .ldr p.1 .r12 p.2

/-- Keep the arguments in callee-saved registers across the helper calls. -/
def entry : List Instr :=
  [.ldrSp .r12 0] ++ save ++
    [movR sb .r12, movR .r4 .r0, movR .r5 .r1, movR .r6 .r2, movR .r7 .r3]

def prepare : Prog isa :=
  .seq (.block [movR .r0 .r4, .mov .r1 (.imm 0), movR .r2 sb, .mov .r3 (.imm 182)])
    (.call "vg_sm4_prepare_keys" prepareKeys)

def crypt : Prog isa :=
  .seq (.block [movR .r0 sb, .mov .r1 (.imm 182)])
    cryptPrepared

/-- Choose the number of useful lanes, in `r11`. -/
def count : Prog isa :=
  .seq (.block [.mov .r10 (lsrOp .r7 3), .cmp .r10 (.imm 0)])
    (.ite .ne (.block [.mov .r11 (.imm 8)]) (.block [movR .r11 .r7]))

/-- Fill one lane and advance the full 128-bit counter. -/
def fillBody : List Instr :=
  (List.range 4).flatMap (copyWord .r0 sb 0 (4 * counterSlot)) ++ incAt sb (4 * counterSlot) ++
    [.dp .add .r0 .r0 (.imm 16), .subs .r1 .r1 (.imm 1)]

def fill : Prog isa :=
  .seq (.block [tailAddr .r0, movR .r1 .r11]) (.loop (.block fillBody) .ne)

/-- Consume one encrypted counter block. -/
def xorBody : List Instr :=
  (List.range 4).flatMap (xorWord .r6 .r0 0 0) ++
    [.dp .add .r0 .r0 (.imm 16), .dp .add .r6 .r6 (.imm 16), .subs .r1 .r1 (.imm 1)]

def xorGroup : Prog isa :=
  .seq (.block [tailAddr .r0, movR .r1 .r11]) (.loop (.block xorBody) .ne)

def batch : Prog isa := .seq fill (.seq crypt xorGroup)

def group : Prog isa :=
  .seq count (.seq batch (.block [.subs .r7 .r7 (.reg .r11)]))

def copyCounterIn : List Instr := (List.range 4).flatMap (copyWord sb .r5 (4 * counterSlot) 0)
def copyCounterOut : List Instr := (List.range 4).flatMap (copyWord .r5 sb 0 (4 * counterSlot))

def prologue : Prog isa :=
  .seq (.block entry) (.seq prepare (.block (copyCounterIn ++ [.cmp .r7 (.imm 0)])))

def dataLoop : Prog isa := .ite .eq (.block []) (.loop group .ne)

def finish : Prog isa := .block (copyCounterOut ++ [movR .r12 sb] ++ restore)

def ctr : Prog isa := .seq prologue (.seq dataLoop finish)

end VG.Impl.Sm4.Arm.BatchCtr

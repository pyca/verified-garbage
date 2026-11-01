module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr

/-! # Eight-block CBC decryption with prepared SM4 keys on ARMv7

Decrypt ciphertext blocks independently, then combine the results with their
preceding ciphertext in reverse order, before it is overwritten. The last
ciphertext is saved in the caller's IV; the old IV remains in counter space
until the first block has been combined with it.
-/

@[expose] public section
namespace VG.Impl.Sm4.Arm.BatchCbc

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Sm4.Arm
open VG.Impl.Modes.Arm (copyWord xorWord)

def prepare : Prog isa :=
  .seq (.block [movR .r0 .r4, .mov .r1 (.imm 1), movR .r2 sb, .mov .r3 (.imm 182)])
    (.call "vg_sm4_prepare_keys" prepareKeys)

def prologue : Prog isa :=
  .seq (.block BatchCtr.entry) (.seq prepare (.block (BatchCtr.copyCounterIn ++ [.cmp .r7 (.imm 0)])))

def copyLane (j : Nat) : List Instr :=
  (List.range 4).flatMap (copyWord sb .r6 (4 * tailSlot + 16 * j) (16 * j))

def saveLast (j : Nat) : List Instr := (List.range 4).flatMap (copyWord .r5 .r6 0 (16 * j))

def fillSteps (j : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (copyLane j ++ [.cmp .r11 (.imm (BitVec.ofNat 32 (j + 1)))]))
      (.ite .eq (.block (saveLast j)) (fillSteps (j + 1) n))

/-- Pads the Thumb cipher-loop placement to a word boundary. -/
def pad : List Instr := [movR .r9 .r9]
def fill : Prog isa := .seq (.block pad) (fillSteps 0 8)

def xorBlock (j : Nat) : List Instr :=
  (List.range 4).flatMap (copyWord .r6 sb (16 * j) (4 * tailSlot + 16 * j)) ++
    (List.range 4).flatMap (if j = 0 then xorWord .r6 sb 0 (4 * BatchCtr.counterSlot)
      else xorWord .r6 .r6 (16 * j) (16 * (j - 1)))

def xorPrefix : Nat → Prog isa
  | 0 => .block (xorBlock 0)
  | j + 1 => .seq (.block (xorBlock (j + 1))) (xorPrefix j)

def chooseXor (j : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block [.cmp .r11 (.imm (BitVec.ofNat 32 (j + 1)))])
      (.ite .eq (xorPrefix j) (chooseXor (j + 1) n))

def advance : List Instr :=
  [.mov .r0 (.shifted .r11 .lsl 4), .dp .add .r6 .r6 (.reg .r0), .subs .r7 .r7 (.reg .r11)]

def batch : Prog isa := .seq fill
  (.seq BatchCtr.crypt (.seq (chooseXor 0 8) (.block BatchCtr.copyCounterIn)))
def group : Prog isa := .seq BatchCtr.count (.seq batch (.block advance))
def dataLoop : Prog isa := .ite .eq (.block []) (.loop group .ne)
def decrypt : Prog isa := .seq prologue (.seq dataLoop BatchCtr.finish)

end VG.Impl.Sm4.Arm.BatchCbc

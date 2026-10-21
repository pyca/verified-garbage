module

public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr

/-! # Eight-block CFB decryption with prepared SM4 keys on ARMv7

CFB decryption encrypts the IV and preceding ciphertext blocks independently.
The current ciphertext is saved before XOR writes plaintext over the input.
-/

@[expose] public section
namespace VG.Impl.Sm4.Arm.BatchCfb

open VG.Arm VG.Impl.Aes.Arm VG.Impl.Sm4.Arm
open VG.Impl.Modes.Arm (copyWord)

/-- Counter space is the chaining value; lane zero receives its old value. -/
def first : List Instr :=
  (List.range 4).flatMap (copyWord sb sb (4 * tailSlot) (4 * BatchCtr.counterSlot))

/-- A ciphertext before the last useful block becomes the next input lane;
the last becomes the next chaining value. The recursion stops there. -/
def nextLane (j : Nat) : List Instr :=
  (List.range 4).flatMap (copyWord sb .r6 (4 * tailSlot + 16 * (j + 1)) (16 * j))

def saveLast (j : Nat) : List Instr :=
  (List.range 4).flatMap (copyWord sb .r6 (4 * BatchCtr.counterSlot) (16 * j))

def steps (j : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block [.cmp .r11 (.imm (BitVec.ofNat 32 (j + 1)))])
      (.ite .eq (.block (saveLast j)) (.seq (.block (nextLane j)) (steps (j + 1) n)))

def fill : Prog isa := .seq (.block first) (steps 0 8)
def batch : Prog isa := .seq fill (.seq BatchCtr.crypt BatchCtr.xorGroup)
def group : Prog isa := .seq BatchCtr.count (.seq batch (.block [.subs .r7 .r7 (.reg .r11)]))
def dataLoop : Prog isa := .ite .eq (.block []) (.loop group .ne)
def decrypt : Prog isa := .seq BatchCtr.prologue (.seq dataLoop BatchCtr.finish)

end VG.Impl.Sm4.Arm.BatchCfb

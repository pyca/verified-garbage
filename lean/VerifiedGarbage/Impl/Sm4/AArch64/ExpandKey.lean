import VerifiedGarbage.Impl.Sm4.AArch64.Ecb
import VerifiedGarbage.Impl.Sm4.Planes

/-!
# The SM4 key schedule on AArch64

`expandKey(key = x0, schedule = x1, scratch = x2)`: `vg_sm4_expand_key`
with its working space in the scratch buffer (`Layers.lean`, moved to
`x5`), which the artifact allocates on the stack. As on x86-64
(`Impl/Sm4/X86_64/ExpandKey.lean`): the bitsliced rounds of ECB, with `L'`
for `L` and a table of `CK`'s planes for the round keys, run the key
schedule on sixteen copies of `MK ⊕ FK`; after every four rounds `fromBs`
puts the state's words in the tail buffer as a block, whose 64-bit words
byte-reversed (`rev`) are the schedule's next 16 bytes.

Only `x0`, `x1` (the schedule), `x3` (the table's end), `x4` (the round
key's entry), `x5` and the loop test (`t0`) hold public values; no address
and no branch depends on anything else.
-/

namespace VG.Impl.Sm4.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64
open VG.Impl.Sm4 (Lin planeOf fkWord)

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks of the tail buffer. -/
def loadHalf (h : Nat) : List Instr :=
  [.ldr .x t0 .x0 (8 * h)] ++ imm t1 (fkWord h) ++ [eorR t0 t0 t1] ++
  (List.range 16).map fun b => stS (tailAt b h) t0

/-- The planes of `CK`, in the table's slots. -/
def ckEntries : List (Nat × BitVec 64) :=
  (List.range 32).flatMap fun i => (List.range 8).map fun j => (tableSlot + 8 * i + j, planeOf (Spec.Sm4.ck i) j)

/-- The table of `CK`'s planes. -/
def ckTable : List Instr := setSlots ckEntries

/-- The four new round keys, from the tail buffer's first block to the
schedule at `x1`. -/
def extract : List Instr :=
  [ldS t0 (tailAt 0 1), .rev t0 t0, .str .x t0 .x1 0,
   ldS t0 (tailAt 0 0), .rev t0 t0, .str .x t0 .x1 8]

/-- Four rounds of the key schedule, and their round keys to the schedule;
`t0` is zero when `kp` reaches the table's end. -/
def keyBody : List Instr :=
  rounds4 .key ++ [.addImm .x kp kp 256] ++ fromBs ++ extract ++
  [.addImm .x .x1 .x1 16, .sub .x t0 kp .x3]

def expandKey : Prog isa :=
  .seq (.block ([movR sb .x2] ++ saveRegs ++ setSlots keyMasks ++ ckTable ++ loadHalf 0 ++
      loadHalf 1 ++ toBs ++ slotAddr .x3 tableEnd ++ slotAddr kp tableSlot))
    (.seq (.loop (.block keyBody) (.nonzero .x t0)) (.block restoreRegs))

end VG.Impl.Sm4.AArch64

module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# The SM4 key schedule on RISC-V

`expandKey(key = a0, schedule = a1, scratch = a2)`: `vg_sm4_expand_key`
with its working space in the scratch buffer (`Layers.lean`, moved to
`a5`), which the artifact allocates on the stack. As on PPC64LE
(`Impl/Sm4/PPC64LE/ExpandKey.lean`): the bitsliced rounds of ECB, with `L'`
for `L` and a table of `CK`'s planes for the round keys, run the key
schedule on sixteen copies of `MK ⊕ FK`; after every four rounds `fromBs`
puts the state's words in the tail buffer as a block, whose 64-bit words
stored byte-reversed are the schedule's next 16 bytes. The contracts state
no alignment for the key or the schedule, so the key is read a byte at a
time, and the schedule written a byte at a time (which reverses the bytes).

Only `a0` (the key), `a1` (the schedule), `a3` (the round key's entry),
`a4` (the table, then its end), `a5` and the loop test (`t0`) hold public
values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64
open VG.Impl.Sm4 (Lin planeOf fkWord)
open VG.Impl.Words.RISCV64 (li64 loadLE64 storeBE)

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks of the tail buffer. -/
def loadHalf (h : Nat) : List Instr :=
  loadLE64 t0 t2 (m 1) .a0 (8 * h) ++ li64 t1 t2 (fkWord h) ++ [xorR t0 t0 t1] ++
  (List.range 16).map fun b => stS (tailAt b h) t0

/-- The planes of `CK`, by their offsets in the table. -/
def ckEntries : List (Nat × BitVec 64) :=
  (List.range 32).flatMap fun i => (List.range 8).map fun j => (8 * i + j, planeOf (Spec.Sm4.ck i) j)

/-- The table of `CK`'s planes, through `a4` (left at the table). -/
def ckTable : List Instr :=
  slotAddr .a4 tableSlot ++ ckEntries.flatMap fun (k, v) => li64 t0 t1 v ++ [.store .d t0 .a4 (8 * k)]

/-- The four new round keys, from the tail buffer's first block to the
schedule at `a1`, each 64-bit word byte-reversed (stored big-endian, a byte
at a time through `t1`). -/
def extract : List Instr :=
  [ldS t0 (tailAt 0 1)] ++ storeBE 8 t0 t1 .a1 0 ++ [ldS t0 (tailAt 0 0)] ++ storeBE 8 t0 t1 .a1 8

/-- Four rounds of the key schedule, and their round keys to the schedule;
`t0` is zero when `kr` reaches the table's end. -/
def keyBody : List Instr :=
  rounds4 .key ++ [.addi kr kr 256] ++ fromBs ++ extract ++ [.addi .a1 .a1 16, .sub t0 kr .a4]

def expandKey : Prog isa :=
  .seq (.block ([movR sb .a2] ++ saveRegs ++ setSlots (keyMasks ++ bsKs) ++ ckTable ++ loadHalf 0 ++
      loadHalf 1 ++ toBs ++ slotAddr .a4 tableEnd ++ slotAddr kr tableSlot))
    (.seq (.loop (.block keyBody) (.nonzero t0)) (.block restoreRegs))

end VG.Impl.Sm4.RISCV64

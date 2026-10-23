module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Ecb
public import VerifiedGarbage.Impl.Sm4.Planes

/-!
# The SM4 key schedule on PPC64LE

`expandKey(key = r3, schedule = r4, scratch = r5)`: `vg_sm4_expand_key`
with its working space in the scratch buffer (`Layers.lean`, moved to
`r8`), which the artifact allocates on the stack. As on x86-64 and AArch64
(`Impl/Sm4/AArch64/ExpandKey.lean`): the bitsliced rounds of ECB, with `L'`
for `L` and a table of `CK`'s planes for the round keys, run the key
schedule on sixteen copies of `MK ⊕ FK`; after every four rounds `fromBs`
puts the state's words in the tail buffer as a block, whose 64-bit words
stored byte-reversed (`stdbrx`) are the schedule's next 16 bytes.

Only `r3`, `r4` (the schedule), `r8`, `r10` (the round key's entry), `r11`
(the table's end), `r12` (the byte-reversed stores' index) and the loop test
(`t0`) hold public values; no address and no branch depends on anything else.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE
open VG.Impl.Sm4 (Lin planeOf fkWord)

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks of the tail buffer. -/
def loadHalf (h : Nat) : List Instr :=
  [.load .d t0 .r3 (8 * h)] ++ imm64 t1 (fkWord h) ++ [xorR t0 t0 t1] ++
  (List.range 16).map fun b => stS (tailAt b h) t0

/-- The planes of `CK`, in the table's slots. -/
def ckEntries : List (Nat × BitVec 64) :=
  (List.range 32).flatMap fun i => (List.range 8).map fun j => (tableSlot + 8 * i + j, planeOf (Spec.Sm4.ck i) j)

/-- The table of `CK`'s planes. -/
def ckTable : List Instr := setSlots ckEntries

/-- The four new round keys, from the tail buffer's first block to the
schedule at `r4`, each 64-bit word byte-reversed. -/
def extract : List Instr :=
  [ldS t0 (tailAt 0 1), .li .r12 0, .storeRev .d t0 .r4 .r12,
   ldS t0 (tailAt 0 0), .li .r12 8, .storeRev .d t0 .r4 .r12]

/-- Four rounds of the key schedule, and their round keys to the schedule;
`t0` is zero when `kr` reaches the table's end. -/
def keyBody : List Instr :=
  rounds4 .key ++ [.addi kr kr 256] ++ fromBs ++ extract ++
  [.addi .r4 .r4 16, .sub t0 kr .r11]

def expandKey : Prog isa :=
  .seq (.block ([movR sb .r5] ++ saveRegs ++ setSlots keyMasks ++ ckTable ++ loadHalf 0 ++
      loadHalf 1 ++ toBs ++ slotAddr .r11 tableEnd ++ slotAddr kr tableSlot))
    (.seq (.loop (.block keyBody) (.nonzero .d t0)) (.block restoreRegs))

end VG.Impl.Sm4.PPC64LE

import VerifiedGarbage.Impl.Sm4.X86_64.Ecb
import VerifiedGarbage.Spec.Sm4

/-!
# The SM4 key schedule on x86-64

`expandKey(key = rdi, schedule = rsi, scratch = rdx)`: `vg_sm4_expand_key`
with its working space in the scratch buffer (`Layers.lean`, moved to
`r9`), which the artifact allocates on the stack.

The key schedule (draft-ribose-cfrg-sm4-10 §7.3) is the recurrence of the
rounds with `L'` for `L` and the constants `CK` for the round keys, from
`MK ⊕ FK`: the bitsliced rounds of ECB run it on sixteen copies of
`MK ⊕ FK`, with a table of `CK`'s planes (immediates in the code, computed
from the specification's `CK`, as `FK` is). After
every four rounds the state's words are the next four round keys; `fromBs`
puts them in the tail buffer as a block, the last first and each
big-endian, whose 64-bit words byte-swapped are the schedule's next
16 bytes.

Only `rdi`, `rsi` (the table's end, and the round key's entry), `r8` (the
schedule) and `r9` hold public values; no address and no branch depends on
anything else.
-/

namespace VG.Impl.Sm4.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64
open VG.Impl.Sm4 (Lin)

/-- Plane `j` of the 32-bit word `x` in every block: bit `16 i + b` is bit
`j` of its byte `i`, from the most significant. -/
def planeOf (x : BitVec 32) (j : Nat) : BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map fun p => x.getLsbD (8 * (3 - p / 16) + j))).setWidth 64

/-- `FK`'s words `2 h` and `2 h + 1` as a block stores them (each big-endian),
read as a little-endian word. -/
def fkWord (h : Nat) : BitVec 64 :=
  (BitVec.ofBoolListLE ((List.range 64).map fun t =>
    (Spec.Sm4.fk.getD (2 * h + t / 32) 0).getLsbD (8 * (3 - t % 32 / 8) + t % 8))).setWidth 64

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks of the tail buffer. -/
def loadHalf (h : Nat) : List Instr :=
  [.mov t0 (.mem (at_ .rdi (8 * h))), .movImm64 t1 (fkWord h), xorR t0 t1] ++
  (List.range 16).map fun b => st (tailAt b h) t0

/-- The planes of `CK`, in the table's slots. -/
def ckEntries : List (Nat × BitVec 64) :=
  (List.range 32).flatMap fun i => (List.range 8).map fun j => (tableSlot + 8 * i + j, planeOf (Spec.Sm4.ck i) j)

/-- The table of `CK`'s planes. -/
def ckTable : List Instr := setMasks ckEntries

/-- The four new round keys, from the tail buffer's first block to the
schedule at `r8`. -/
def extract : List Instr :=
  [movS t0 (tailAt 0 1), .bswap t0, .store (at_ .r8 0) t0,
   movS t0 (tailAt 0 0), .bswap t0, .store (at_ .r8 8) t0]

/-- Four rounds of the key schedule, and their round keys to the schedule. -/
def keyBody : List Instr :=
  rounds4 .key ++ [.alu .add kp (.imm 256)] ++ fromBs ++ extract ++
  [.alu .add .r8 (.imm 16), .alu .cmp kp (.reg .rdi)]

def expandKey : Prog isa :=
  .seq (.block ([movR sb .rdx, movR .r8 .rsi] ++ saveRegs ++ setMasks keyMasks ++ ckTable ++ loadHalf 0 ++
      loadHalf 1 ++ toBs ++
      slotAddr .rdi tableEnd ++ slotAddr kp tableSlot))
    (.seq (.loop (.block keyBody) .ne) (.block restoreRegs))

end VG.Impl.Sm4.X86_64

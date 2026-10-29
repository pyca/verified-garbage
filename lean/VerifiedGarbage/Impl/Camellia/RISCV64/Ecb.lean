module

public import VerifiedGarbage.Impl.Camellia.RISCV64.Layers

/-!
# Camellia ECB, bitsliced, on RISC-V

`ecb dir(schedule = a0, rounds = a1, data = a2, n = a3, scratch = a4)`:
`vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` with their working
space in the scratch buffer (`Layers.lean` has its layout), which the
artifact allocates on the stack. As on PPC64LE (`Impl/Camellia/PPC64LE/Ecb.lean`):
* The scratch buffer moves to `a5`, the callee-saved registers are saved,
  the masks set.
* The subkeys are bitsliced into the table at slot 128, in the order the
  rounds use them: the stored order for encryption; for decryption the
  order RFC 3713 §2.3.3 swaps them into, `kw3, kw4`, then the subkeys
  between `kw2` and `kw3` from the last back to the first, then `kw1,
  kw2`. Decryption then runs the same rounds as encryption.
* Each group of up to eight blocks, copied to the tail buffer and back:
  both halves bitsliced, the prewhitening, groups of six rounds with FL and
  FLINV between them, the postwhitening, and the halves stored back
  swapped.

The schedule and the data have no alignment, so they are read and written
a byte at a time; the scratch buffer is aligned, as the artifact allocates
it on the stack. `a0` (the schedule, then the end of six rounds), `a1`
(the table, then the round key's entry), `a2` (the data), `a3` (the blocks
left), `a4` (the postwhitening's entry), `a5`, the copies' pointers
(`t3`, `t4`) and counts (`t5`, `t6`), and the loop tests (`t0`, `t1`)
hold public values; no address and
no branch depends on anything else. The rounds use only the state, the
temporaries and the scratch buffer, so the public values stay in `a0`–`a5`
throughout.
-/

@[expose] public section

namespace VG.Impl.Camellia.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64
open VG.Impl

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The subkeys -/

/-- Bitslice the subkey at `[a0 + d]` (read a byte at a time: the schedule
has no alignment) into the entry at `kp`, and step `kp` to the next entry. -/
def keyOne (d : Nat) : List Instr :=
  Words64.RISCV64.loadLE64 (q 0) t0 t2 .a0 d ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++
  toBs ++ (List.range 8).map (fun j => .store .d (q j) kp (8 * j)) ++
  ([.addi kp kp 64] : List Instr)

/-- `kp := ` the table. -/
def tableSetup : List Instr := [.addi kp sb ((8 * keySlot : Nat) : Int)]

/-- `a4 := ` the address of the postwhitening's entry, `8 g` entries into
the table (`g ≥ 1` the number of groups of six rounds), in two steps, as
an immediate reaches only 2047. -/
def endAddr (g : Nat) : List Instr :=
  [.addi .a4 sb ((8 * keySlot + 512 : Nat) : Int), .addi .a4 .a4 ((512 * (g - 1) : Nat) : Int)]

/-- What depends on the number of groups `g`: `a4` (`endAddr`), the
subkeys the loop bitslices in `t1`, and for decryption `a0` at `kw3`. -/
def groupConsts : Dir → Nat → List Instr
  | .encrypt, g => endAddr g ++ [.li t1 ((8 * g + 2 : Nat) : Int)]
  | .decrypt, g => endAddr g ++ [.addi .a0 .a0 ((64 * g : Nat) : Int), .li t1 ((8 * g - 2 : Nat) : Int)]

/-- Encryption's table: the `t1` subkeys from `a0`, in order. -/
def encKeys : Prog isa :=
  .seq (.block tableSetup)
    (.loop (.block (keyOne 0 ++ ([.addi .a0 .a0 8, .addi t1 t1 (-1)] : List Instr))) (.nonzero t1))

/-- Decryption's table, for `g` groups, `a0` at word `8 g` and `t1 = 8 g - 2`:
`kw3, kw4` (words `8 g`, `8 g + 1`), words `8 g - 1` down to 2, then
`kw1, kw2`. -/
def decKeys : Prog isa :=
  .seq (.block (tableSetup ++ keyOne 0 ++ keyOne 8 ++ ([.addi .a0 .a0 (-8)] : List Instr)))
    (.seq (.loop (.block (keyOne 0 ++ ([.addi .a0 .a0 (-8), .addi t1 t1 (-1)] : List Instr))) (.nonzero t1))
      (.block (([.addi .a0 .a0 (-8)] : List Instr) ++ keyOne 0 ++ keyOne 8)))

/-- The table for 18 rounds (`t0 = 0`) or 24, and `a4` at its
postwhitening entry: the branches set only `groupConsts`, and one copy of
the loops builds either table. -/
def keys (dir : Dir) : Prog isa :=
  .seq (.ite (.zero t0) (.block (groupConsts dir 3)) (.block (groupConsts dir 4)))
    (match dir with | .encrypt => encKeys | .decrypt => decKeys)

/-! ## Eight blocks, in the tail buffer -/

/-- Load half `h` (0 for `D1`, 1 for `D2`) of the eight blocks in the tail buffer. -/
def loadWords (h : Nat) : List Instr := (List.range 8).map fun b => ldS (q b) (tailSlot + 2 * b + h)

/-- Store the eight words to half `h` of the blocks in the tail buffer. -/
def storeWords (h : Nat) : List Instr := (List.range 8).map fun b => stS (tailSlot + 2 * b + h) (q b)

/-- The prewhitening, after `D1` is bitsliced into the state: `D1 ^= kw1`
into the state and its slots, `D2 ^= kw2` in its slots. -/
def whiten : List Instr :=
  keyXor 0 ++ storeHalf d1Slot ++
  ((List.range 8).flatMap fun j =>
    [ldS t0 (d2Slot + j), .load .d u7 kp (8 * (8 + j)), xorR t0 t0 u7, stS (d2Slot + j) t0])

/-- Bitslice both halves, `D2` to its slots and `D1` into the state, and
whiten them with the first two entries; `kp` is left at the first round's. -/
def head : List Instr :=
  tableSetup ++ loadWords 1 ++ toBs ++ storeHalf d2Slot ++ loadWords 0 ++ toBs ++ whiten ++
  ([.addi kp kp 128] : List Instr)

/-- Two rounds: `D2 ^= F(D1, k)`, `D1 ^= F(D2, k')`, with the state holding
`D1` before and after; `t0` is zero when `kp` reaches `a0`. -/
def pairBody : List Instr :=
  round 0 d2Slot ++ round 8 d1Slot ++ ([.addi kp kp 128, .sub t0 kp .a0] : List Instr)

/-- Six rounds, then FL and FLINV unless they were the last; `t0` is zero
when `kp` is at the postwhitening's entry. -/
def groupBody : Prog isa :=
  .seq (.block [.addi .a0 kp 384])
    (.seq (.loop (.block pairBody) (.nonzero t0))
      (.seq (.block [.sub t0 kp .a4])
        (.seq (.ite (.nonzero t0) (.block flLayer) (.block []))
          (.block [.sub t0 kp .a4]))))

/-- The postwhitening, and the halves back to the blocks, swapped: `D2`
to the left halves, `D1` to the right. -/
def tail : List Instr :=
  keyXor 8 ++ fromBs ++ storeWords 1 ++ loadHalf d2Slot ++ keyXor 0 ++ fromBs ++ storeWords 0

/-- The eight blocks in the tail buffer, in place. -/
def crypt8 : Prog isa := .seq (.block head) (.seq (.loop groupBody (.nonzero t0)) (.block tail))

/-! ## The groups -/

/-- The pointers and the count on to the next block. -/
def copyStep : List Instr := [.addi .t3 .t3 16, .addi .t4 .t4 16, .addi .t5 .t5 (-1)]

/-- Copy `t5` blocks from the data at `t3` to the tail buffer at `t4`
(through `t0`; the data has no alignment, so it is read a byte at a time). -/
def copyInBlocks : Prog isa :=
  .loop (.block (Words64.RISCV64.loadLE64 t0 t1 t2 .t3 0 ++ [.store .d t0 .t4 0] ++
      Words64.RISCV64.loadLE64 t0 t1 t2 .t3 8 ++ [.store .d t0 .t4 8] ++ copyStep)) (.nonzero .t5)

/-- Copy `t5` blocks from the tail buffer at `t3` to the data at `t4`,
written a byte at a time. -/
def copyOutBlocks : Prog isa :=
  .loop (.block ([.load .d t0 .t3 0] ++ Words64.RISCV64.storeLE64 t0 t1 t2 .t4 0 ++
      [.load .d t0 .t3 8] ++ Words64.RISCV64.storeLE64 t0 t1 t2 .t4 8 ++ copyStep)) (.nonzero .t5)

/-- `t6 := min(a3, 8)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [shrI t0 .a3 3])
    (.ite (.nonzero t0) (.block [.li .t6 8]) (.block [movR .t6 .a3]))

/-- The tail buffer's address, in `r`. -/
def tailAddr (r : Reg) : List Instr := [.addi r sb ((8 * tailSlot : Nat) : Int)]

/-- The group's blocks to the tail buffer. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .t3 .a2] ++ tailAddr .t4 ++ [movR .t5 .t6])) copyInBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa :=
  .seq groupCount (.seq (.block (tailAddr .t3 ++ [movR .t4 .a2, movR .t5 .t6])) copyOutBlocks)

/-- Eight blocks, or the last one to seven, and on to the next. -/
def group : Prog isa :=
  .seq copyIn (.seq crypt8 (.seq copyOut (.block [.sub .a3 .a3 .t6, .addi .a2 .a2 128])))

/-- The prologue: the scratch buffer (passed in `r`) to `a5`, the
callee-saved registers saved, the masks set, and `t0 = rounds - 18`. -/
def prologue (r : Reg) : List Instr :=
  [movR sb r] ++ saveRegs ++ setSlots allMasks ++ ([.addi t0 .a1 (-18)] : List Instr)

/-- The whole function: the table for 18 or 24 rounds, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block (prologue .a4))
    (.seq (keys dir)
      (.seq (.ite (.zero .a3) (.block []) (.loop group (.nonzero .a3))) (.block restoreRegs)))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.Camellia.RISCV64

module

public import VerifiedGarbage.Impl.Camellia.AArch64.Layers

/-!
# Camellia ECB, bitsliced, on AArch64

`ecb dir(schedule = x0, rounds = x1, data = x2, n = x3, scratch = x4)`:
`vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` with their working
space in the scratch buffer (`Layers.lean` has its layout), which the
artifact allocates on the stack. As on x86-64:

* The scratch buffer moves to `x5`, the callee-saved registers are saved,
  the masks set.
* The subkeys are bitsliced into the table at slot 96, in the order the
  rounds use them: the stored order for encryption; for decryption the
  order RFC 3713 §2.3.3 swaps them into, `kw3, kw4`, then the subkeys
  between `kw2` and `kw3` from the last back to the first, then `kw1,
  kw2`. Decryption then runs the same rounds as encryption.
* Each group of up to eight blocks, copied to the tail buffer and back:
  both halves bitsliced, the prewhitening, groups of six rounds with FL and
  FLINV between them, the postwhitening, and the halves stored back
  swapped.

`x0` (the schedule, then the end of six rounds), `x1` (the table, then the
round key's entry), `x2` (the data), `x3` (the blocks left), `x4` (the
postwhitening's entry), `x5`, the copies' pointers and counts, and the loop
tests (`t0`, `t1`) hold public values; no address and no branch depends on
anything else. The rounds use only the state, the temporaries and the
scratch buffer, so the public values stay in `x0`–`x4` throughout.
-/

@[expose] public section

namespace VG.Impl.Camellia.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The subkeys -/

/-- Bitslice the subkey at `[x0 + d]` into the entry at `kp`, and step
`kp` to the next entry. -/
def keyOne (d : Nat) : List Instr :=
  ([.ldr .x (q 0) .x0 d] : List Instr) ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++
  toBs ++ (List.range 8).map (fun j => .str .x (q j) kp (8 * j)) ++
  ([.addImm .x kp kp 64] : List Instr)

/-- `kp := ` the table. -/
def tableSetup : List Instr := [movR kp sb, .addImm .x kp kp (8 * keySlot)]

/-- `x4 := ` the address of the postwhitening's entry, `8 g` entries into
the table (`g` the number of groups of six rounds). -/
def endAddr (g : Nat) : List Instr := [movR .x4 sb, .addImm .x .x4 .x4 (8 * keySlot + 512 * g)]

/-- Encryption's table, for `g` groups: the `8 g + 2` subkeys in order. -/
def encKeys (g : Nat) : Prog isa :=
  .seq (.block (tableSetup ++ ([.movz .x t1 (BitVec.ofNat 16 (8 * g + 2)) 0] : List Instr)))
    (.loop (.block (keyOne 0 ++ ([.addImm .x .x0 .x0 8, .subImm .x t1 t1 1] : List Instr))) (.nonzero .x t1))

/-- Decryption's table, for `g` groups: `kw3, kw4` (words `8 g`, `8 g + 1`),
words `8 g - 1` down to 2, then `kw1, kw2`. -/
def decKeys (g : Nat) : Prog isa :=
  .seq (.block (tableSetup ++ ([.addImm .x .x0 .x0 (64 * g)] : List Instr) ++
      keyOne 0 ++ keyOne 8 ++ ([.subImm .x .x0 .x0 8, .movz .x t1 (BitVec.ofNat 16 (8 * g - 2)) 0] : List Instr)))
    (.seq (.loop (.block (keyOne 0 ++ ([.subImm .x .x0 .x0 8, .subImm .x t1 t1 1] : List Instr))) (.nonzero .x t1))
      (.block (([.subImm .x .x0 .x0 8] : List Instr) ++ keyOne 0 ++ keyOne 8)))

def keys (dir : Dir) (g : Nat) : Prog isa :=
  .seq (match dir with | .encrypt => encKeys g | .decrypt => decKeys g) (.block (endAddr g))

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
    [ldS t0 (d2Slot + j), .ldr .x u7 kp (8 * (8 + j)), eorR t0 t0 u7, stS (d2Slot + j) t0])

/-- Bitslice both halves, `D2` to its slots and `D1` into the state, and
whiten them with the first two entries; `kp` is left at the first round's. -/
def head : List Instr :=
  tableSetup ++ loadWords 1 ++ toBs ++ storeHalf d2Slot ++ loadWords 0 ++ toBs ++ whiten ++
  ([.addImm .x kp kp 128] : List Instr)

/-- Two rounds: `D2 ^= F(D1, k)`, `D1 ^= F(D2, k')`, with the state holding
`D1` before and after; `t0` is zero when `kp` reaches `x0`. -/
def pairBody : List Instr :=
  round 0 d2Slot ++ round 8 d1Slot ++ ([.addImm .x kp kp 128, .sub .x t0 kp .x0] : List Instr)

/-- Six rounds, then FL and FLINV unless they were the last; `t0` is zero
when `kp` is at the postwhitening's entry. -/
def groupBody : Prog isa :=
  .seq (.block [.addImm .x .x0 kp 384])
    (.seq (.loop (.block pairBody) (.nonzero .x t0))
      (.seq (.block [.sub .x t0 kp .x4])
        (.seq (.ite (.nonzero .x t0) (.block flLayer) (.block []))
          (.block [.sub .x t0 kp .x4]))))

/-- The postwhitening, and the halves back to the blocks, swapped: `D2`
to the left halves, `D1` to the right. -/
def tail : List Instr :=
  keyXor 8 ++ fromBs ++ storeWords 1 ++ loadHalf d2Slot ++ keyXor 0 ++ fromBs ++ storeWords 0

/-- The eight blocks in the tail buffer, in place. -/
def crypt8 : Prog isa := .seq (.block head) (.seq (.loop groupBody (.nonzero .x t0)) (.block tail))

/-! ## The groups -/

/-- Copy `x17` blocks from `x14` to `x15` (through `t0`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.ldr .x t0 .x14 0, .str .x t0 .x15 0, .ldr .x t0 .x14 8, .str .x t0 .x15 8,
      .addImm .x .x14 .x14 16, .addImm .x .x15 .x15 16, .subImm .x .x17 .x17 1]) (.nonzero .x .x17)

/-- `x16 := min(x3, 8)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [lsrI t0 .x3 3])
    (.ite (.nonzero .x t0) (.block [.movz .x .x16 8 0]) (.block [movR .x16 .x3]))

/-- The tail buffer's address, in `r`. -/
def tailAddr (r : Reg) : List Instr := [movR r sb, .addImm .x r r (8 * tailSlot)]

/-- The group's blocks to the tail buffer. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .x14 .x2] ++ tailAddr .x15 ++ [movR .x17 .x16])) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa :=
  .seq groupCount (.seq (.block (tailAddr .x14 ++ [movR .x15 .x2, movR .x17 .x16])) copyBlocks)

/-- Eight blocks, or the last one to seven, and on to the next. -/
def group : Prog isa :=
  .seq copyIn (.seq crypt8 (.seq copyOut (.block [.sub .x .x3 .x3 .x16, .addImm .x .x2 .x2 128])))

/-- The whole function: the table for 18 or 24 rounds, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block ([movR sb .x4] ++ saveRegs ++ setSlots layerMasks ++ ([.subImm .x t0 .x1 18] : List Instr)))
    (.seq (.ite (.zero .x t0) (keys dir 3) (keys dir 4))
      (.seq (.ite (.zero .x .x3) (.block []) (.loop group (.nonzero .x .x3))) (.block restoreRegs)))

end VG.Impl.Camellia.AArch64

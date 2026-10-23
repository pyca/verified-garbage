module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.Layers

/-!
# Camellia ECB, bitsliced, on PPC64LE

`ecb dir(schedule = r3, rounds = r4, data = r5, n = r6, scratch = r7)`:
`vg_camellia_ecb_encrypt` and `vg_camellia_ecb_decrypt` with their working
space in the scratch buffer (`Layers.lean` has its layout), which the
artifact allocates on the stack. As on AArch64 (`Impl/Camellia/AArch64/Ecb.lean`)
and x86-64:

* The scratch buffer moves to `r8`, the callee-saved registers are saved,
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

`r3` (the schedule, then the end of six rounds), `r4` (the table, then the
round key's entry), `r5` (the data), `r6` (the blocks left), `r7` (the
postwhitening's entry), `r8`, the copies' pointers (`r9`–`r12`) and counts, and the loop
tests (`t0`, `t1`) hold public values; no address and no branch depends on
anything else. The rounds use only the state, the temporaries and the
scratch buffer, so the public values stay in `r3`–`r7` throughout.
-/

@[expose] public section

namespace VG.Impl.Camellia.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The subkeys -/

/-- Bitslice the subkey at `[r3 + d]` into the entry at `kp`, and step
`kp` to the next entry. -/
def keyOne (d : Nat) : List Instr :=
  ([.load .d (q 0) .r3 d] : List Instr) ++ ((List.range 7).map fun i => movR (q (i + 1)) (q 0)) ++
  toBs ++ (List.range 8).map (fun j => .store .d (q j) kp (8 * j)) ++
  ([.addi kp kp 64] : List Instr)

/-- `kp := ` the table. -/
def tableSetup : List Instr := [.addi kp sb (8 * keySlot)]

/-- `r7 := ` the address of the postwhitening's entry, `8 g` entries into
the table (`g` the number of groups of six rounds). -/
def endAddr (g : Nat) : List Instr := [.addi .r7 sb (8 * keySlot + 512 * g)]

/-- What depends on the number of groups `g`: `r7` (`endAddr`), the
subkeys the loop bitslices in `t1`, and for decryption `r3` at `kw3`. -/
def groupConsts : Dir → Nat → List Instr
  | .encrypt, g => endAddr g ++ [.li t1 (8 * g + 2)]
  | .decrypt, g => endAddr g ++ [.addi .r3 .r3 (64 * g), .li t1 (8 * g - 2)]

/-- Encryption's table: the `t1` subkeys from `r3`, in order. -/
def encKeys : Prog isa :=
  .seq (.block tableSetup)
    (.loop (.block (keyOne 0 ++ ([.addi .r3 .r3 8, .subi t1 t1 1] : List Instr))) (.nonzero .d t1))

/-- Decryption's table, for `g` groups, `r3` at word `8 g` and `t1 = 8 g - 2`:
`kw3, kw4` (words `8 g`, `8 g + 1`), words `8 g - 1` down to 2, then
`kw1, kw2`. -/
def decKeys : Prog isa :=
  .seq (.block (tableSetup ++ keyOne 0 ++ keyOne 8 ++ ([.subi .r3 .r3 8] : List Instr)))
    (.seq (.loop (.block (keyOne 0 ++ ([.subi .r3 .r3 8, .subi t1 t1 1] : List Instr))) (.nonzero .d t1))
      (.block (([.subi .r3 .r3 8] : List Instr) ++ keyOne 0 ++ keyOne 8)))

/-- The table for 18 rounds (`t0 = 0`) or 24, and `r7` at its
postwhitening entry: the branches set only `groupConsts`, and one copy of
the loops builds either table. -/
def keys (dir : Dir) : Prog isa :=
  .seq (.ite (.zero .d t0) (.block (groupConsts dir 3)) (.block (groupConsts dir 4)))
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
`D1` before and after; `t0` is zero when `kp` reaches `r3`. -/
def pairBody : List Instr :=
  round 0 d2Slot ++ round 8 d1Slot ++ ([.addi kp kp 128, .sub t0 kp .r3] : List Instr)

/-- Six rounds, then FL and FLINV unless they were the last; `t0` is zero
when `kp` is at the postwhitening's entry. -/
def groupBody : Prog isa :=
  .seq (.block [.addi .r3 kp 384])
    (.seq (.loop (.block pairBody) (.nonzero .d t0))
      (.seq (.block [.sub t0 kp .r7])
        (.seq (.ite (.nonzero .d t0) (.block flLayer) (.block []))
          (.block [.sub t0 kp .r7]))))

/-- The postwhitening, and the halves back to the blocks, swapped: `D2`
to the left halves, `D1` to the right. -/
def tail : List Instr :=
  keyXor 8 ++ fromBs ++ storeWords 1 ++ loadHalf d2Slot ++ keyXor 0 ++ fromBs ++ storeWords 0

/-- The eight blocks in the tail buffer, in place. -/
def crypt8 : Prog isa := .seq (.block head) (.seq (.loop groupBody (.nonzero .d t0)) (.block tail))

/-! ## The groups -/

/-- Copy `r11` blocks from `r9` to `r10` (through `t0`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.load .d t0 .r9 0, .store .d t0 .r10 0, .load .d t0 .r9 8, .store .d t0 .r10 8,
      .addi .r9 .r9 16, .addi .r10 .r10 16, .subi .r11 .r11 1]) (.nonzero .d .r11)

/-- `r12 := min(r6, 8)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [shrI t0 .r6 3])
    (.ite (.nonzero .d t0) (.block [.li .r12 8]) (.block [movR .r12 .r6]))

/-- The tail buffer's address, in `r`. -/
def tailAddr (r : Reg) : List Instr := [.addi r sb (8 * tailSlot)]

/-- The group's blocks to the tail buffer. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .r9 .r5] ++ tailAddr .r10 ++ [movR .r11 .r12])) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa :=
  .seq groupCount (.seq (.block (tailAddr .r9 ++ [movR .r10 .r5, movR .r11 .r12])) copyBlocks)

/-- Eight blocks, or the last one to seven, and on to the next. -/
def group : Prog isa :=
  .seq copyIn (.seq crypt8 (.seq copyOut (.block [.sub .r6 .r6 .r12, .addi .r5 .r5 128])))

/-- The whole function: the table for 18 or 24 rounds, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block ([movR sb .r7] ++ saveRegs ++ setSlots layerMasks ++ ([.subi t0 .r4 18] : List Instr)))
    (.seq (keys dir)
      (.seq (.ite (.zero .d .r6) (.block []) (.loop group (.nonzero .d .r6))) (.block restoreRegs)))

end VG.Impl.Camellia.PPC64LE

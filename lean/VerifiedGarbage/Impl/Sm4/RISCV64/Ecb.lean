module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Layers
public import VerifiedGarbage.Impl.Words.RISCV64.CopyFast

/-!
# SM4 ECB, bitsliced, on RISC-V

`ecb dir(schedule = a0, data = a1, n = a2, scratch = a3)`:
`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` with their working space in
the scratch buffer (`Layers.lean` has its layout), which the artifact
allocates on the stack. As on PPC64LE (`Impl/Sm4/PPC64LE/Ecb.lean`):

* The scratch buffer moves to `a5`; the callee-saved registers are saved,
  the masks set.
* The model faults on misaligned accesses, and the contracts state no
  alignment for the schedule or the data: the schedule is copied to the
  tail buffer, which is aligned, and read there; the blocks are copied to
  and from the tail buffer. Each copy (`copyAny`) moves a doubleword at a
  time when the source and destination are 8-byte aligned, and a byte at a
  time otherwise, a choice of the pointers alone.
* The round keys are bitsliced into the table at slot 128, in the order the
  rounds use them: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption
  (§7.2). Decryption then runs the same rounds as encryption. The sixteen
  pairs of round keys are unrolled.
* Each group of up to sixteen blocks is copied to the tail buffer,
  bitsliced, run through the 32 rounds (eight times four, the state's words
  taking the new words in turn), and copied back.

`a0` (the schedule's copy, then the table's end), `a1` (the data), `a2` (the
blocks left), `a3` (the round key's entry), `a4` (the group's blocks),
`a5` and, between the rounds, the copies' pointers and counts (`t1`–`t3`)
and the loop test (`t0`) hold public values; no address and no branch
depends on anything else. The rounds' S-boxes also use `a0`, `a4` and
`ra`, the last saved in the scratch buffer (a public value loaded from
memory would be secret), so the rounds keep `a1`, `a2`, `a3` and `a5`,
and `a0` is set again after them.
-/

@[expose] public section

namespace VG.Impl.Sm4.RISCV64

open VG.RISCV64 VG.Impl.Aes.RISCV64
open VG.Impl.Sm4 (Lin)
open VG.Impl.Words.RISCV64 (copyAny)

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The round keys -/

/-- The schedule at `a0` to the tail buffer (through `t1`–`t4`), and `a0`
to that copy. -/
def copySchedule : Prog isa :=
  .seq (.block ([movR .t1 .a0] ++ slotAddr .t2 tailSlot ++ [.li .t3 128]))
    (.seq (copyAny .t4 .t1 .t2 .t3) (.block (slotAddr .a0 tailSlot)))

/-- `n` pairs of round keys, from the word at `a0`, to the entries at `kr`,
which `st` moves to the next entry after each. -/
def keyPairs (st : Instr) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (keyOne 0 ++ [st] ++ keyOne 1 ++ [st, .addi .a0 .a0 8])) (keyPairs st n)

/-- Encryption's table: round keys `2 m` and `2 m + 1`, from the word at
`a0`, to entries `2 m` and `2 m + 1`. -/
def encKeys : Prog isa := .seq (.block (slotAddr kr tableSlot)) (keyPairs (.addi kr kr 64) 16)

/-- Decryption's table: round keys `2 m` and `2 m + 1` to entries `31 - 2 m`
and `30 - 2 m`. -/
def decKeys : Prog isa := .seq (.block (slotAddr kr (tableSlot + 8 * 31))) (keyPairs (.addi kr kr (-64)) 16)

/-- The schedule's copy, the table, then `a0 := ` its end. -/
def keys (dir : Dir) : Prog isa :=
  .seq copySchedule
    (.seq (match dir with | .encrypt => encKeys | .decrypt => decKeys) (.block (slotAddr .a0 tableEnd)))

/-! ## Sixteen blocks -/

/-- Four rounds, `kr += 256`, `t0 := kr - ` the table's end (the S-box
uses `a0`). -/
def roundsBody (l : Lin) : List Instr :=
  rounds4 l ++ [.addi kr kr 256] ++ slotAddr t0 tableEnd ++ [.sub t0 kr t0]

/-- The 32 rounds, with `kr` from the table's start to its end. -/
def rounds (l : Lin) : Prog isa :=
  .seq (.block (slotAddr kr tableSlot)) (.loop (.block (roundsBody l)) (.nonzero t0))

/-- The sixteen blocks of the tail buffer, in place, with `ra` saved while
the rounds' S-boxes use it, and `a0` (the table's end) set again after
them; they leave `a4` (the group's blocks, computed again by `copyOut`)
as it is. -/
def crypt16 : Prog isa :=
  .seq (.block (toBs ++ saveAux)) (.seq (rounds .enc) (.block (restoreAux ++ fromBs ++ slotAddr .a0 tableEnd)))

/-! ## The groups -/

/-- `a4 := min(a2, 16)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [shrI t0 .a2 4])
    (.ite (.nonzero t0) (.block [.li .a4 16]) (.block [movR .a4 .a2]))

/-- The group's blocks to the tail buffer, a doubleword at a time if the
data is 8-byte aligned, else a byte at a time. -/
def copyIn : Prog isa :=
  .seq groupCount
    (.seq (.block ([movR .t1 .a1] ++ slotAddr .t2 tailSlot ++ [shlI .t3 .a4 4])) (copyAny .t4 .t1 .t2 .t3))

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa :=
  .seq groupCount
    (.seq (.block (slotAddr .t1 tailSlot ++ [movR .t2 .a1, shlI .t3 .a4 4])) (copyAny .t4 .t1 .t2 .t3))

/-- Sixteen blocks, or the last one to fifteen, and on to the next. -/
def group : Prog isa :=
  .seq copyIn (.seq crypt16 (.seq copyOut (.block [.sub .a2 .a2 .a4, .addi .a1 .a1 256])))

/-- The code with its working space at `sr` and the table built by `k`:
the table, then the groups. -/
def ecbWith (sr : Reg) (k : Prog isa) : Prog isa :=
  .seq (.block ([movR sb sr] ++ saveRegs ++ setSlots (keyMasks ++ bsKs)))
    (.seq k
      (.seq (.ite (.zero .a2) (.block []) (.loop group (.nonzero .a2))) (.block restoreRegs)))

/-- The whole function, with its working space at `a3`. -/
def ecb (dir : Dir) : Prog isa := ecbWith .a3 (keys dir)

end VG.Impl.Sm4.RISCV64

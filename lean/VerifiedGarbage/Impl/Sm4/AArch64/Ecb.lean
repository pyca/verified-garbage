module

public import VerifiedGarbage.Impl.Sm4.AArch64.Layers

/-!
# SM4 ECB, bitsliced, on AArch64

`ecb dir(schedule = x0, data = x1, n = x2, scratch = x3)`:
`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` with their working space in
the scratch buffer (`Layers.lean` has its layout), which the artifact
allocates on the stack. As on x86-64:

* The scratch buffer moves to `x5`; the callee-saved registers are saved,
  the masks set.
* The round keys are bitsliced into the table at slot 128, in the order the
  rounds use them: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption
  (§7.2). Decryption then runs the same rounds as encryption.
* Each group of up to sixteen blocks is copied to the tail buffer,
  bitsliced, run through the 32 rounds (eight times four, the state's words
  taking the new words in turn), and copied back.

`x0` (the schedule), `x1` (the data), `x2` (the blocks left), `x3` (the
key setup's count, then the table's end), `x4` (the round key's entry),
`x5`, the copies' pointers and counts, and the loop test (`t0`) hold public
values; no address and no branch depends on anything else. The rounds use
only the state, the temporaries and the scratch buffer, so the public
values stay in `x0`–`x4` throughout.
-/

@[expose] public section

namespace VG.Impl.Sm4.AArch64

open VG.AArch64 VG.Impl.Aes.AArch64
open VG.Impl.Sm4 (Lin)

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The round keys -/

/-- `r := ` the address of slot `k`. -/
def slotAddr (r : Reg) (k : Nat) : List Instr := [movR r sb, .addImm .x r r (8 * k)]

/-- Encryption's table: round keys `2 m` and `2 m + 1`, from the word at
`x0`, to entries `2 m` and `2 m + 1`. -/
def encKeys : Prog isa :=
  .seq (.block (slotAddr kp tableSlot ++ [.movz .x .x3 16 0]))
    (.loop (.block (keyOne 0 ++ [.addImm .x kp kp 64] ++ keyOne 1 ++
      [.addImm .x kp kp 64, .addImm .x .x0 .x0 8, .subImm .x .x3 .x3 1])) (.nonzero .x .x3))

/-- Decryption's table: round keys `2 m` and `2 m + 1` to entries `31 - 2 m`
and `30 - 2 m`. -/
def decKeys : Prog isa :=
  .seq (.block (slotAddr kp (tableSlot + 8 * 31) ++ [.movz .x .x3 16 0]))
    (.loop (.block (keyOne 0 ++ [.subImm .x kp kp 64] ++ keyOne 1 ++
      [.subImm .x kp kp 64, .addImm .x .x0 .x0 8, .subImm .x .x3 .x3 1])) (.nonzero .x .x3))

/-- The table, then `x3 := ` its end. -/
def keys (dir : Dir) : Prog isa :=
  .seq (match dir with | .encrypt => encKeys | .decrypt => decKeys) (.block (slotAddr .x3 tableEnd))

/-! ## Sixteen blocks -/

/-- Four rounds, `kp += 256`, `t0 := kp - x3`. -/
def roundsBody (l : Lin) : List Instr := rounds4 l ++ [.addImm .x kp kp 256, .sub .x t0 kp .x3]

/-- The 32 rounds, with `kp` from the table's start to its end (in `x3`). -/
def rounds (l : Lin) : Prog isa :=
  .seq (.block (slotAddr kp tableSlot)) (.loop (.block (roundsBody l)) (.nonzero .x t0))

/-- The sixteen blocks of the tail buffer, in place. -/
def crypt16 : Prog isa := .seq (.block toBs) (.seq (rounds .enc) (.block fromBs))

/-! ## The groups -/

/-- Copy `x17` blocks from `x14` to `x15` (through `t0`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.ldr .x t0 .x14 0, .str .x t0 .x15 0, .ldr .x t0 .x14 8, .str .x t0 .x15 8,
      .addImm .x .x14 .x14 16, .addImm .x .x15 .x15 16, .subImm .x .x17 .x17 1]) (.nonzero .x .x17)

/-- `x16 := min(x2, 16)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [lsrI t0 .x2 4])
    (.ite (.nonzero .x t0) (.block [.movz .x .x16 16 0]) (.block [movR .x16 .x2]))

/-- The group's blocks to the tail buffer. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .x14 .x1] ++ slotAddr .x15 tailSlot ++ [movR .x17 .x16])) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa :=
  .seq groupCount (.seq (.block (slotAddr .x14 tailSlot ++ [movR .x15 .x1, movR .x17 .x16])) copyBlocks)

/-- Sixteen blocks, or the last one to fifteen, and on to the next. -/
def group : Prog isa :=
  .seq copyIn (.seq crypt16 (.seq copyOut (.block [.sub .x .x2 .x2 .x16, .addImm .x .x1 .x1 256])))

/-- The whole function: the table, then the groups. -/
def ecb (dir : Dir) : Prog isa :=
  .seq (.block ([movR sb .x3] ++ saveRegs ++ setSlots keyMasks))
    (.seq (keys dir)
      (.seq (.ite (.zero .x .x2) (.block []) (.loop group (.nonzero .x .x2))) (.block restoreRegs)))

end VG.Impl.Sm4.AArch64

module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Layers

/-!
# SM4 ECB, bitsliced, on PPC64LE

`ecb dir(schedule = r3, data = r4, n = r5, scratch = r6)`:
`vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` with their working space in
the scratch buffer (`Layers.lean` has its layout), which the artifact
allocates on the stack. As on x86-64 and AArch64
(`Impl/Sm4/AArch64/Ecb.lean`):

* The scratch buffer moves to `r8`; the callee-saved registers are saved,
  the masks set.
* The round keys are bitsliced into the table at slot 128, in the order the
  rounds use them: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption
  (§7.2). Decryption then runs the same rounds as encryption.
* Each group of up to sixteen blocks is copied to the tail buffer,
  bitsliced, run through the 32 rounds (eight times four, the state's words
  taking the new words in turn), and copied back.

`r3` (the schedule, then the copies' count), `r4` (the data), `r5` (the
blocks left), `r6` and `r7` (the copies' pointers), `r8`, `r10` (the round
key's entry), `r11` (the key setup's count, then the table's end), `r12`
(the group's blocks) and the loop test (`t0`) hold public values; no
address and no branch depends on anything else. The rounds use only the
state, the temporaries and the scratch buffer, so the public values stay in
`r3`–`r12` (but `r9`) throughout.
-/

@[expose] public section

namespace VG.Impl.Sm4.PPC64LE

open VG.PPC64LE VG.Impl.Aes.PPC64LE
open VG.Impl.Sm4 (Lin)

inductive Dir | encrypt | decrypt
  deriving DecidableEq, Repr

/-! ## The round keys -/

/-- `r := ` the address of slot `k`. -/
def slotAddr (r : Reg) (k : Nat) : List Instr := [.addi r sb (8 * k)]

/-- Encryption's table: round keys `2 m` and `2 m + 1`, from the word at
`r3`, to entries `2 m` and `2 m + 1`. -/
def encKeys : Prog isa :=
  .seq (.block (slotAddr kr tableSlot ++ [.li .r11 16]))
    (.loop (.block (keyOne 0 ++ [.addi kr kr 64] ++ keyOne 1 ++
      [.addi kr kr 64, .addi .r3 .r3 8, .subi .r11 .r11 1])) (.nonzero .d .r11))

/-- Decryption's table: round keys `2 m` and `2 m + 1` to entries `31 - 2 m`
and `30 - 2 m`. -/
def decKeys : Prog isa :=
  .seq (.block (slotAddr kr (tableSlot + 8 * 31) ++ [.li .r11 16]))
    (.loop (.block (keyOne 0 ++ [.subi kr kr 64] ++ keyOne 1 ++
      [.subi kr kr 64, .addi .r3 .r3 8, .subi .r11 .r11 1])) (.nonzero .d .r11))

/-- The table, then `r11 := ` its end. -/
def keys (dir : Dir) : Prog isa :=
  .seq (match dir with | .encrypt => encKeys | .decrypt => decKeys) (.block (slotAddr .r11 tableEnd))

/-! ## Sixteen blocks -/

/-- Four rounds, `kr += 256`, `t0 := kr - r11`. -/
def roundsBody (l : Lin) : List Instr := rounds4 l ++ [.addi kr kr 256, .sub t0 kr .r11]

/-- The 32 rounds, with `kr` from the table's start to its end (in `r11`). -/
def rounds (l : Lin) : Prog isa :=
  .seq (.block (slotAddr kr tableSlot)) (.loop (.block (roundsBody l)) (.nonzero .d t0))

/-- The sixteen blocks of the tail buffer, in place. -/
def crypt16 : Prog isa := .seq (.block toBs) (.seq (rounds .enc) (.block fromBs))

/-! ## The groups -/

/-- Copy `r3` blocks from `r6` to `r7` (through `t0`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.load .d t0 .r6 0, .store .d t0 .r7 0, .load .d t0 .r6 8, .store .d t0 .r7 8,
      .addi .r6 .r6 16, .addi .r7 .r7 16, .subi .r3 .r3 1]) (.nonzero .d .r3)

/-- `r12 := min(r5, 16)`, the blocks of this group. -/
def groupCount : Prog isa :=
  .seq (.block [shrI t0 .r5 4])
    (.ite (.nonzero .d t0) (.block [.li .r12 16]) (.block [movR .r12 .r5]))

/-- The group's blocks to the tail buffer. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .r6 .r4] ++ slotAddr .r7 tailSlot ++ [movR .r3 .r12])) copyBlocks)

/-- The tail buffer back to the group's blocks. -/
def copyOut : Prog isa :=
  .seq groupCount (.seq (.block (slotAddr .r6 tailSlot ++ [movR .r7 .r4, movR .r3 .r12])) copyBlocks)

/-- Sixteen blocks, or the last one to fifteen, and on to the next. -/
def group : Prog isa :=
  .seq copyIn (.seq crypt16 (.seq copyOut (.block [.sub .r5 .r5 .r12, .addi .r4 .r4 256])))

/-- The code with its working space at `sr` and the table built by `k`:
the table, then the groups. -/
def ecbWith (sr : Reg) (k : Prog isa) : Prog isa :=
  .seq (.block ([movR sb sr] ++ saveRegs ++ setSlots keyMasks))
    (.seq k
      (.seq (.ite (.zero .d .r5) (.block []) (.loop group (.nonzero .d .r5))) (.block restoreRegs)))

/-- The whole function, with its working space at `r6`. -/
def ecb (dir : Dir) : Prog isa := ecbWith .r6 (keys dir)

end VG.Impl.Sm4.PPC64LE

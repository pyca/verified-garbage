module

public import VerifiedGarbage.Impl.Sm4.PPC64LE.Layers

/-!
# SM4 ECB's pieces, bitsliced, on PPC64LE

The code of `vg_sm4_prepare_keys` and `vg_sm4_crypt_prepared`
(`Prepared.lean`), which `vg_sm4_ecb_encrypt` and `vg_sm4_ecb_decrypt` call,
and the copies between ECB's data and the tail buffer, with the working
space in the scratch buffer (`Layers.lean` has its layout, at `r8`). As on
x86-64 and AArch64 (`Impl/Sm4/AArch64/Ecb.lean`):

* The round keys are bitsliced into the table at slot 128, in the order the
  rounds use them: `rk₀ … rk₃₁` for encryption, `rk₃₁ … rk₀` for decryption
  (§7.2). Decryption then runs the same rounds as encryption. The sixteen
  pairs of round keys are unrolled, so that every store of the table is at a
  known offset of the scratch buffer (`kr` moves by a constant between them):
  a caller's analysis of constant time (`VG.PPC64LE.slotTaint`) then knows
  that the callee-saved registers the functions save there survive the
  table, and its own public values with them.
* Sixteen blocks of the tail buffer are bitsliced, run through the 32 rounds
  (eight times four, the state's words taking the new words in turn), and
  bitsliced back (`crypt16`).
* A group of up to sixteen blocks is copied to the tail buffer and back
  (`copyIn`, `copyOut`), the data pointer in `r31`, through `r3`, `r6`, `r9`,
  `r10` and `r12`.

`r10` (the round key's entry), `r11` (the table's end) and the loop test
(`t0`) hold public values; no address and no branch depends on anything else.
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

/-- `n` pairs of round keys, from the word at `r3`, to the entries at `kr`,
which `st` moves to the next entry after each. -/
def keyPairs (st : Instr) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (.block (keyOne 0 ++ [st] ++ keyOne 1 ++ [st, .addi .r3 .r3 8])) (keyPairs st n)

/-- Encryption's table: round keys `2 m` and `2 m + 1`, from the word at
`r3`, to entries `2 m` and `2 m + 1`. -/
def encKeys : Prog isa := .seq (.block (slotAddr kr tableSlot)) (keyPairs (.addi kr kr 64) 16)

/-- Decryption's table: round keys `2 m` and `2 m + 1` to entries `31 - 2 m`
and `30 - 2 m`. -/
def decKeys : Prog isa := .seq (.block (slotAddr kr (tableSlot + 8 * 31))) (keyPairs (.subi kr kr 64) 16)

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

/-- Copy `r3` blocks from `r6` to `r10` (through `r9`). -/
def copyBlocks : Prog isa :=
  .loop (.block [.load .d .r9 .r6 0, .store .d .r9 .r10 0, .load .d .r9 .r6 8, .store .d .r9 .r10 8,
      .addi .r6 .r6 16, .addi .r10 .r10 16, .subi .r3 .r3 1]) (.nonzero .d .r3)

/-- `r12 := min(r5, 16)`, the blocks of this group (through `r9`). -/
def groupCount : Prog isa :=
  .seq (.block [shrI .r9 .r5 4])
    (.ite (.nonzero .d .r9) (.block [.li .r12 16]) (.block [movR .r12 .r5]))

/-- The group's blocks (at `r31`) to the tail buffer. -/
def copyIn : Prog isa :=
  .seq groupCount (.seq (.block ([movR .r6 .r31] ++ slotAddr .r10 tailSlot ++ [movR .r3 .r12])) copyBlocks)

/-- The tail buffer back to the group's blocks (at `r31`). -/
def copyOut : Prog isa :=
  .seq groupCount (.seq (.block (slotAddr .r6 tailSlot ++ [movR .r10 .r31, movR .r3 .r12])) copyBlocks)

end VG.Impl.Sm4.PPC64LE

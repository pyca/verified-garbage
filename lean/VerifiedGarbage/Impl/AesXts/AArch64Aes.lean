module

public import VerifiedGarbage.Impl.Aes.AArch64.AeseBlocks

/-!
# XTS-AES on AArch64 in one pass, with the Cryptographic Extension

`vg_aes_xts_encrypt_aes(schedule = x0, rounds = x1, tweak = x2, data = x3, n = x4, scratch = x5)`
and `vg_aes_xts_decrypt_aes`, with the contracts of `vg_aes_xts_encrypt` and
`vg_aes_xts_decrypt` (`Spec/Xts/Contract.lean`), for CPUs with FEAT_AES.
Unlike the functions calling a block function (`AArch64.lean`), they call
nothing: each block is read once, has its tweak XORed in, is enciphered (or
deciphered) and has its tweak XORed in again before it is stored.

The arguments are moved so that the setup and round code of
`vg_aes_encrypt_blocks_aes` (`Impl/Aes/AArch64/AeseBlocks.lean`) finds them
where it expects them: the data pointer in `x2` and the number of blocks
left in `x3`; the tweak pointer goes to `x11`. The setup (`encSetup` or
`decSetup`) leaves the round keys in `v16`–`v30`, `x6 = rounds − 10`,
`x7 = rounds − 12` and `x13 = n / 8`.

The tweak is kept in `x14` (its low word) and `x15` (its high word), and
multiplied by `α` as `vg_aes_xts_encrypt` does (`AArch64.mulA`): the words
shifted left by `adds` and `adcs`, and `0x87` XORed into the low word if
the high word's top bit was set, chosen by `csel` on the carry. These run on
the integer units, beside the AES instructions.

Blocks go eight at a time (`v0`–`v7`), each round applied to all eight so
the AES pipeline stays full, then one at a time (`v0`). The tweaks of the
eight-block groups are computed a group ahead, so that no group's rounds
wait on the chain of multiplications by `α`: two banks of eight tweaks,
`scratch` and `scratch + 128`, hold those of the current group (at `x12`)
and of the next (at `x8`). Before the first group, its tweaks are stored at
`x12` (`gen`). Each group loads each block and XORs in its tweak from `x12`
(`preL`), stores the next group's tweaks at `x8` while its rounds run, then
XORs each block register with its tweak from `x12` again and stores it
(`post`), and swaps the banks. After the last group the tweak of the next
block is loaded back from `x12`. Each block after the groups is loaded and
XORed with its tweak, which is moved into `v31` (`dup`, `ins`) and saved at
`scratch` for the XOR after the rounds, and the tweak is multiplied by `α`
(`pre`). The tweak after the last block is written back.

Every branch and every address depends only on the pointers, `rounds` and
`n`. No callee-saved register is written.
-/

@[expose] public section

namespace VG.Impl.AesXts.AArch64Aes

open VG.AArch64
open VG.Impl.Aes.AArch64.Aese (regs8)

/-- The tweak pointer into `x11`, the data pointer into `x2`, the number of
blocks into `x3`, and the tweak into `x14` and `x15`. -/
def enter : List Instr :=
  [.addImm .x .x11 .x2 0, .addImm .x .x2 .x3 0, .addImm .x .x3 .x4 0, .ldr .x .x14 .x11 0,
   .ldr .x .x15 .x11 8]

/-- The tweak in `x14` and `x15` times `α`. -/
def mulA : List Instr :=
  [.adds .x .x14 .x14 .x14, .adcs .x .x15 .x15 .x15, .movz .x .x9 0x87 0, .movz .x .x10 0 0,
   .csel .x .x9 .x9 .x10, .logic .eor .x .x14 .x14 .x9]

/-- Load block register `b` from the data block `x2 + 16 j`, and XOR in the
tweak, saved at `scratch + 16 j`; then the tweak times `α`. -/
def pre1 (b : VReg) (j : Nat) : List Instr :=
  [.ldrq b .x2 (16 * j), .vop (.dup .d2 .v31 .x14), .vop (.ins .d2 .v31 1 .x15), .strq .v31 .x5 (16 * j),
   .vop (.logic .eor b b .v31)] ++ mulA

/-- `pre1` for the registers, from place `j` on. -/
def pre : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => pre1 b j ++ pre bs (j + 1)

/-- XOR the tweak saved at `t + 16 j` into block register `b` again, and
store it to the data block `x2 + 16 j`. -/
def post1 (t : Reg) (b : VReg) (j : Nat) : List Instr :=
  [.ldrq .v31 t (16 * j), .vop (.logic .eor b b .v31), .strq b .x2 (16 * j)]

/-- `post1` for the registers, from place `j` on. -/
def post (t : Reg) : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => post1 t b j ++ post t bs (j + 1)

/-- Load block register `b` from the data block `x2 + 16 j`, and XOR in its
tweak from `x12 + 16 j`. -/
def preL1 (b : VReg) (j : Nat) : List Instr :=
  [.ldrq b .x2 (16 * j), .ldrq .v31 .x12 (16 * j), .vop (.logic .eor b b .v31)]

/-- `preL1` for the registers, from place `j` on. -/
def preL : List VReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => preL1 b j ++ preL bs (j + 1)

/-- The tweak stored at `r + 16 j`, and multiplied by `α`. -/
def genStep (r : Reg) (j : Nat) : List Instr :=
  ([.str .x .x14 r (16 * j), .str .x .x15 r (16 * j + 8)] : List Instr) ++ mulA

/-- The next eight tweaks, stored at `r`. -/
def gen (r : Reg) : List Instr := (List.range 8).flatMap (genStep r)

/-- Eight blocks, their tweaks at `x12`, storing the next group's at `x8`;
then the banks swapped, and `x13 = n / 8` for the blocks left. -/
def blk8 (f : List VReg → Prog isa) : Prog isa :=
  .seq (.block (preL regs8 0 ++ gen .x8))
    (.seq (f regs8)
      (.block (post .x12 regs8 0 ++ ([.addImm .x .x2 .x2 128, .subImm .x .x3 .x3 8, .lsr .x .x13 .x3 3,
        .addImm .x .x10 .x12 0, .addImm .x .x12 .x8 0, .addImm .x .x8 .x10 0] : List Instr))))

/-- One block. -/
def blk1 (f : List VReg → Prog isa) : Prog isa :=
  .seq (.block (pre [.v0] 0))
    (.seq (f [.v0]) (.block (post .x5 [.v0] 0 ++ ([.addImm .x .x2 .x2 16, .subImm .x .x3 .x3 1] : List Instr))))

/-- The banks set up, and the first group's tweaks stored at `x12`. -/
def start8 : List Instr := [.addImm .x .x12 .x5 0, .addImm .x .x8 .x5 128] ++ gen .x12

/-- The tweak of the next block, loaded back. -/
def end8 : List Instr := [.ldr .x .x14 .x12 0, .ldr .x .x15 .x12 8]

/-- The tweak after the last block, written back. -/
def finish : List Instr := [.str .x .x14 .x11 0, .str .x .x15 .x11 8]

/-- All the blocks, eight and then one at a time, after `setup`. -/
def crypt (setup : List Instr) (f : List VReg → Prog isa) : Prog isa :=
  .seq (.block (enter ++ setup))
    (.seq (.ite (.zero .x .x13) (.block [])
        (.seq (.block start8) (.seq (.loop (blk8 f) (.nonzero .x .x13)) (.block end8))))
      (.seq (.ite (.zero .x .x3) (.block []) (.loop (blk1 f) (.nonzero .x .x3)))
        (.block finish)))

def encrypt : Prog isa := crypt Aes.AArch64.Aese.encSetup Aes.AArch64.Aese.aes

def decrypt : Prog isa := crypt Aes.AArch64.Aese.decSetup Aes.AArch64.Aese.aesDec

end VG.Impl.AesXts.AArch64Aes
